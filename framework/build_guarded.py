#!/usr/bin/env python3
"""Three-tier, zero-leak resource-guarded build and gate dispatcher for oss-proof.

Routes Lean builds, verification gates, and ASan+UBSan differential tests cleanly across:
1. User-configured remote Linux build hosts (read strictly from `~/.config/oss-proof/builders.toml`
   or `$OSS_PROOF_BUILDERS_CONFIG` — never stored in the repository), with capability routing
   (`lean` vs `difftest`), failover (`backup_ssh`), and incremental worktree sync (no WIP git push
   required) that preserves remote `.lake/build` caches.
2. Safe serialized local execution (`--local` or automatic fallback when no remote builder is
   configured/reachable), acquiring a machine-wide `fcntl.flock`, capping `LEAN_NUM_THREADS`, and
   diagnosing SIGTERM/SIGKILL (exit 143/137) kill reasons from local memory-guard logs if present.
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
import shlex
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
import tomllib

from framework import check_spec_layers
from framework.manifest import Project, REPO, load_project

DEFAULT_CONFIG_PATH = Path.home() / ".config/oss-proof/builders.toml"
DEFAULT_LOCAL_LOCK = Path("/tmp/oss-proof-lean.lock")


@dataclass(frozen=True)
class BuilderSpec:
    name: str
    ssh: str
    remote_dir: str
    capabilities: tuple[str, ...] = ("lean",)
    backup_ssh: str | None = None
    threads: int = 8
    memory_max_gb: int = 16
    min_free_mem_gb: int = 6
    slice: str = ""
    python: str = "python3"
    lean_bin: str = "~/.elan/bin"


def load_builders_config(path: Path | None = None) -> tuple[dict, list[BuilderSpec]]:
    cfg_path = path or Path(os.environ.get("OSS_PROOF_BUILDERS_CONFIG", str(DEFAULT_CONFIG_PATH)))
    if not cfg_path.is_file():
        return {}, []
    data = tomllib.loads(cfg_path.read_text())
    defaults = data.get("defaults", {})
    builders: list[BuilderSpec] = []
    for entry in data.get("builders", []):
        builders.append(
            BuilderSpec(
                name=entry["name"],
                ssh=entry["ssh"],
                backup_ssh=entry.get("backup_ssh"),
                remote_dir=entry.get("remote_dir", "~/oss-proof-build"),
                capabilities=tuple(entry.get("capabilities", ("lean",))),
                threads=int(entry.get("threads", defaults.get("threads", 8))),
                memory_max_gb=int(entry.get("memory_max_gb", defaults.get("memory_max_gb", 16))),
                min_free_mem_gb=int(entry.get("min_free_mem_gb", defaults.get("min_free_mem_gb", 6))),
                slice=str(entry.get("slice", defaults.get("slice", ""))),
                python=str(entry.get("python", "python3")),
                lean_bin=str(entry.get("lean_bin", "~/.elan/bin")),
            )
        )
    return defaults, builders


def select_candidate_builders(
    builders: list[BuilderSpec],
    *,
    required_capability: str,
    preferred_name: str | None = None,
) -> list[BuilderSpec]:
    matching = [b for b in builders if required_capability in b.capabilities]
    if preferred_name:
        matching = [b for b in matching if b.name == preferred_name]
    return matching


def ssh_endpoints(builder: BuilderSpec) -> list[str]:
    eps = [builder.ssh]
    if builder.backup_ssh:
        eps.append(builder.backup_ssh)
    return eps


def probe_builder(builder: BuilderSpec, timeout_s: int = 5) -> dict | None:
    probe_script = (
        "avail=$(awk '/^MemAvailable:/ {print $2; exit}' /proc/meminfo 2>/dev/null || echo 0); "
        "cores=$(nproc 2>/dev/null || echo 1); "
        "disk=$(df -Pk ~ 2>/dev/null | awk 'NR==2 {print $4}'); "
        "busy=0; "
        "lock=$HOME/.local/state/oss-proof/build.lock; "
        "if [ -f \"$lock\" ] && command -v flock >/dev/null 2>&1; then "
        "  flock -n \"$lock\" true 2>/dev/null || busy=1; "
        "fi; "
        "has_cc=0; (command -v gcc >/dev/null 2>&1 || command -v clang >/dev/null 2>&1) && has_cc=1; "
        "echo \"$avail $cores $disk $busy $has_cc\""
    )
    for ep in ssh_endpoints(builder):
        res = subprocess.run(
            [
                "ssh",
                "-o",
                "BatchMode=yes",
                "-o",
                f"ConnectTimeout={timeout_s}",
                ep,
                probe_script,
            ],
            capture_output=True,
            text=True,
        )
        if res.returncode == 0 and res.stdout.strip():
            parts = res.stdout.strip().splitlines()[-1].split()
            if len(parts) >= 5:
                return {
                    "builder": builder,
                    "endpoint": ep,
                    "mem_avail_kb": int(parts[0]),
                    "cores": int(parts[1]),
                    "disk_avail_kb": int(parts[2]),
                    "busy": parts[3] == "1",
                    "has_cc": parts[4] == "1",
                }
    return None


def pick_best_builder(
    builders: list[BuilderSpec],
    *,
    required_capability: str,
    preferred_name: str | None = None,
) -> dict | None:
    candidates = select_candidate_builders(
        builders,
        required_capability=required_capability,
        preferred_name=preferred_name,
    )
    probed: list[dict] = []
    for b in candidates:
        info = probe_builder(b)
        if info is not None:
            probed.append(info)
    if not probed:
        return None
    # Prefer idle hosts first, then higher available memory, then more cores.
    probed.sort(key=lambda d: (d["busy"], -d["mem_avail_kb"], -d["cores"]))
    return probed[0]


def affected_targets(proj: Project, base_rev: str = "origin/main") -> list[str]:
    """Compute minimal Lake build targets for modified `.lean` files inside `proj`."""
    try:
        out = subprocess.check_output(
            ["git", "status", "--porcelain"],
            cwd=REPO,
            text=True,
        )
        dirty_paths = [line[3:].strip().split(" -> ")[-1] for line in out.splitlines() if line.strip()]
    except subprocess.CalledProcessError:
        dirty_paths = []

    try:
        diff_out = subprocess.check_output(
            ["git", "diff", "--name-only", base_rev],
            cwd=REPO,
            text=True,
            stderr=subprocess.DEVNULL,
        )
        branch_paths = [line.strip() for line in diff_out.splitlines() if line.strip()]
    except subprocess.CalledProcessError:
        branch_paths = []

    prefix = f"projects/{proj.id}/"
    changed = sorted(set(dirty_paths + branch_paths))
    targets: list[str] = []
    full_needed = False
    for path in changed:
        if not path.startswith(prefix):
            continue
        rel = path[len(prefix) :]
        if rel in ("lakefile.toml", "lean-toolchain", "project.json"):
            full_needed = True
            break
        if rel.startswith(f"{proj.package}/Runtime/") or rel.startswith(f"{proj.package}/Spec/"):
            full_needed = True
            break
        if rel.endswith(".lean") and (rel == f"{proj.package}.lean" or rel.startswith(f"{proj.package}/")):
            parts = list(Path(rel).parts)
            mod = check_spec_layers.canonical(parts[:-1] + [parts[-1][: -len(".lean")]])
            if mod not in targets:
                targets.append(mod)

    if full_needed or not targets:
        return list(proj.targets)
    if proj.results_module and proj.results_module not in targets:
        targets.append(proj.results_module)
    return targets


def detect_local_memory_guard() -> Path | None:
    """Locate a local memory-guard event log directory if present on this workstation."""
    candidates = [
        Path(os.environ.get("OSS_PROOF_MEMGUARD_DIR", "")) if os.environ.get("OSS_PROOF_MEMGUARD_DIR") else None,
        Path.home() / ".local/share/zlib-f-memory-guard",
        Path.home() / ".local/share/oss-proof-memory-guard",
    ]
    for cand in candidates:
        if cand and cand.is_dir():
            return cand
    return None


def diagnose_local_kill(guard_dir: Path | None, started_at: float) -> str | None:
    """Inspect recent memory-guard JSONL events to explain exit 143/137 kills."""
    if not guard_dir:
        return None
    logs = sorted(guard_dir.glob("events*.jsonl"), key=lambda p: p.stat().st_mtime, reverse=True)
    for log_file in logs[:2]:
        try:
            lines = log_file.read_text(errors="ignore").splitlines()[-25:]
        except OSError:
            continue
        for raw in reversed(lines):
            try:
                ev = json.loads(raw)
            except json.JSONDecodeError:
                continue
            reason = ev.get("reason") or ev.get("rule") or ev.get("message")
            rss = ev.get("rss_mb") or ev.get("rss_mib") or ev.get("rss")
            if reason:
                return f"local memory guard killed Lean (reason={reason}, rss={rss}, log={log_file.name})"
    return None


def run_local(
    proj: Project,
    mode: str,
    targets: list[str],
    *,
    threads: int | None,
    lock_path: Path,
) -> int:
    guard_dir = detect_local_memory_guard()
    if threads is None:
        threads = 1 if guard_dir else min(4, max(1, os.cpu_count() or 1))
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = str(threads)
    elan_bin = str(Path.home() / ".elan/bin")
    if elan_bin not in env.get("PATH", ""):
        env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

    lock_path.parent.mkdir(parents=True, exist_ok=True)
    print(f"==> [local] Waiting for host build lock ({lock_path}), LEAN_NUM_THREADS={threads}")
    with open(lock_path, "w") as lock_fh:
        fcntl.flock(lock_fh.fileno(), fcntl.LOCK_EX)
        started = time.time()
        try:
            if mode == "build":
                cmd = ["lake", "--dir", str(proj.root), "build", "--wfail", *targets]
                print("==> [local] Running:", " ".join(cmd))
                res = subprocess.run(cmd, cwd=REPO, env=env)
                rc = res.returncode
            elif mode == "gate":
                cmd = ["lake", "--dir", str(proj.root), "build", "--wfail", *targets]
                print("==> [local] Running:", " ".join(cmd))
                res = subprocess.run(cmd, cwd=REPO, env=env)
                rc = res.returncode
                if rc == 0:
                    rc = subprocess.run(
                        [sys.executable, "framework/check_project.py", proj.id, "--skip-build"],
                        cwd=REPO,
                        env=env,
                    ).returncode
            elif mode == "difftest":
                rc = subprocess.run(
                    [sys.executable, "framework/run_difftest.py", proj.id],
                    cwd=REPO,
                    env=env,
                ).returncode
            else:
                raise RuntimeError(f"unsupported mode: {mode}")
        finally:
            elapsed = time.time() - started
            fcntl.flock(lock_fh.fileno(), fcntl.LOCK_UN)

    print(f"==> [local] Finished mode={mode} project={proj.id} exit={rc} elapsed={elapsed:.1f}s")
    if rc in (137, 143, -9, -15) or rc != 0:
        diag = diagnose_local_kill(guard_dir, started)
        if diag and rc != 0:
            print(f"DIAGNOSIS: {diag}", file=sys.stderr)
            print(
                "HINT: Configure remote build hosts in ~/.config/oss-proof/builders.toml "
                "(see framework/builders.example.toml) or lower threads with --threads 1.",
                file=sys.stderr,
            )
    return rc


def sync_to_remote(
    endpoint: str,
    remote_dir: str,
    proj: Project,
    *,
    sync_mode: str,
    git_ref: str | None,
) -> None:
    if sync_mode == "ref":
        ref = git_ref or subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
        cmd = (
            f"cd {remote_dir} && git fetch origin && git checkout --detach {shlex.quote(ref)} && "
            f"git submodule update --init --depth=1 -- projects/{shlex.quote(proj.id)}/"
        )
        subprocess.run(["ssh", "-o", "BatchMode=yes", endpoint, cmd], check=True)
        return

    # Worktree incremental rsync: syncs framework/, lean-toolchain, and projects/<id>/ (excluding .lake
    # and build artifacts) directly into remote_dir so remote `.lake/build` stays warm without pushing.
    subprocess.run(
        [
            "ssh",
            "-o",
            "BatchMode=yes",
            endpoint,
            f"mkdir -p {remote_dir}/framework {remote_dir}/projects/{shlex.quote(proj.id)}",
        ],
        check=True,
    )
    rsync_common = [
        "rsync",
        "-az",
        "--delete",
        "--exclude=.lake/",
        "--exclude=__pycache__/",
        "--exclude=.git/",
        "--exclude=tests/build/",
    ]
    subprocess.run(
        [*rsync_common, str(REPO / "lean-toolchain"), f"{endpoint}:{remote_dir}/lean-toolchain"],
        check=True,
    )
    subprocess.run(
        [*rsync_common, str(REPO / "framework") + "/", f"{endpoint}:{remote_dir}/framework/"],
        check=True,
    )
    # Exclude the upstream submodule directory from rsync --delete so remote's initialized submodule stays intact.
    sub_name = proj.data["upstream"]["submodule"]
    subprocess.run(
        [
            *rsync_common,
            f"--exclude=/{sub_name}/",
            str(proj.root) + "/",
            f"{endpoint}:{remote_dir}/projects/{proj.id}/",
        ],
        check=True,
    )


def run_remote(
    picked: dict,
    proj: Project,
    mode: str,
    targets: list[str],
    *,
    sync_mode: str,
    git_ref: str | None,
) -> int:
    builder: BuilderSpec = picked["builder"]
    endpoint: str = picked["endpoint"]
    print(
        f"==> [remote:{builder.name}] Selected (idle={not picked['busy']}, "
        f"mem_avail={picked['mem_avail_kb'] // 1024} MiB, cores={picked['cores']}, sync={sync_mode})"
    )
    sync_to_remote(endpoint, builder.remote_dir, proj, sync_mode=sync_mode, git_ref=git_ref)
    env_assign = " ".join(
        [
            f"OSS_PROOF_THREADS={builder.threads}",
            f"OSS_PROOF_MEM_MAX_GB={builder.memory_max_gb}",
            f"OSS_PROOF_MIN_FREE_GB={builder.min_free_mem_gb}",
            f"OSS_PROOF_SLICE={shlex.quote(builder.slice)}",
            f"OSS_PROOF_PYTHON={shlex.quote(builder.python)}",
            f"OSS_PROOF_LEAN_BIN={shlex.quote(builder.lean_bin)}",
        ]
    )
    target_args = " ".join(shlex.quote(t) for t in targets) if mode in ("build", "gate") else ""
    remote_cmd = (
        f"cd {builder.remote_dir} && {env_assign} "
        f"bash framework/remote_runner.sh {shlex.quote(mode)} {shlex.quote(proj.id)} {target_args}"
    )
    res = subprocess.run(["ssh", "-o", "BatchMode=yes", endpoint, remote_cmd])
    return res.returncode


def run_doctor(config_path: Path | None) -> int:
    defaults, builders = load_builders_config(config_path)
    cfg = config_path or Path(os.environ.get("OSS_PROOF_BUILDERS_CONFIG", str(DEFAULT_CONFIG_PATH)))
    print(f"Config file : {cfg} ({'found' if cfg.is_file() else 'not found'})")
    print(f"Local guard : {detect_local_memory_guard() or 'not detected'}")
    print(f"Local lock  : {defaults.get('local_lock', DEFAULT_LOCAL_LOCK)}")
    if not builders:
        print("Remote pool : none configured (copy framework/builders.example.toml to ~/.config/oss-proof/builders.toml)")
        return 0
    print(f"Remote pool : {len(builders)} configured host(s)")
    ok_any = False
    for b in builders:
        info = probe_builder(b)
        if info is None:
            print(f"  - {b.name:12s} UNREACHABLE  caps={list(b.capabilities)}")
        else:
            ok_any = True
            state = "BUSY" if info["busy"] else "IDLE"
            cc = "cc=yes" if info["has_cc"] else "cc=no"
            print(
                f"  - {b.name:12s} {state:4s}  mem_avail={info['mem_avail_kb'] // 1024:6d} MiB  "
                f"cores={info['cores']:2d}  disk_free={info['disk_avail_kb'] // (1024 * 1024):4d} GiB  "
                f"{cc}  caps={list(b.capabilities)}"
            )
    return 0 if ok_any else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", help="Project ID to build or check")
    parser.add_argument("targets", nargs="*", help="Optional explicit Lake targets")
    parser.add_argument("--mode", choices=("build", "gate", "difftest"), default="build")
    parser.add_argument("--affected", action="store_true", help="Build only git-changed modules + Results")
    parser.add_argument("--local", action="store_true", help="Force local serialized build")
    parser.add_argument("--builder", help="Pin a specific builder name from builders.toml")
    parser.add_argument("--sync", choices=("worktree", "ref"), default=None, help="Remote sync mode")
    parser.add_argument("--ref", help="Git ref/SHA when using --sync=ref")
    parser.add_argument("--threads", type=int, default=None, help="Override local LEAN_NUM_THREADS")
    parser.add_argument("--config", type=Path, default=None, help="Path to builders.toml")
    parser.add_argument("--doctor", action="store_true", help="Probe remote build pool and local environment")
    args = parser.parse_args()

    if args.doctor:
        return run_doctor(args.config)

    if not args.project:
        parser.error("provide <project> or --doctor")

    proj = load_project(args.project, REPO)
    targets = list(args.targets) if args.targets else (affected_targets(proj) if args.affected else list(proj.targets))
    defaults, builders = load_builders_config(args.config)
    sync_mode = args.sync or defaults.get("sync_mode", "worktree")
    lock_path = Path(defaults.get("local_lock", str(DEFAULT_LOCAL_LOCK)))

    if not args.local and builders:
        req_cap = "difftest" if args.mode == "difftest" else "lean"
        picked = pick_best_builder(builders, required_capability=req_cap, preferred_name=args.builder)
        if picked is not None:
            return run_remote(picked, proj, args.mode, targets, sync_mode=sync_mode, git_ref=args.ref)
        print(
            f"WARNING: no reachable remote builder with capability '{req_cap}'; falling back to serialized local mode",
            file=sys.stderr,
        )

    return run_local(proj, args.mode, targets, threads=args.threads, lock_path=lock_path)


if __name__ == "__main__":
    sys.exit(main())
