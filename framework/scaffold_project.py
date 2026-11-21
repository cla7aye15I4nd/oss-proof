#!/usr/bin/env python3
"""Scaffold a new oss-proof project wired to the shared `OssProof` Lean core, or audit template sync."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from framework._py import ensure_python311

ensure_python311()
from framework.manifest import REPO, load_all_projects


def default_package_name(project_id: str) -> str:
    parts = [p for p in project_id.replace("_", "-").split("-") if p]
    return "".join(p[0].upper() + p[1:] for p in parts) + "F"


def render_files(project_id: str, package: str, title: str, submodule: str, repo_url: str) -> dict[str, str]:
    results_check_src = (REPO / "framework/lean/ResultsCheck.lean").read_text()
    results_check_proj = results_check_src.replace("namespace OssProof.Results", f"namespace {package}.Results")
    results_check_proj = results_check_proj.replace(
        "end OssProof.Results",
        f"def inLibrary (env : Environment) (n : Name) : Bool :=\n  inPackage `{package} env n\n\nend {package}.Results",
    )
    toolchain = (REPO / "lean-toolchain").read_text()

    project_json = {
        "version": 1,
        "id": project_id,
        "title": title,
        "package": package,
        "upstream": {
            "submodule": submodule,
            "repository": repo_url,
            "version": "pinned",
            "target": "portable scalar x86_64 Linux LP64",
            "patches_dir": "patches",
        },
        "build": {
            "targets": [package, f"{package}.Results"],
            "results_module": f"{package}.Results",
            "compiler_helpers": "tests/audit/compiler-helpers.txt",
        },
        "checks": {
            "spec_layers": {
                "spec_dir": f"{package}/Spec",
                "math_dir": f"{package}/Math",
                "proof_dir": f"{package}/Proof",
            }
        },
        "site": {
            "route": project_id,
            "brand": f"{title} × Lean",
            "findings_count": 0,
            "patches_count": 0,
            "summary": {
                "en": f"Strict ISO C17 runtime and safety verification scaffold for {title}; C translation and public API proofs not done.",
                "zh": f"{title} 的严格 ISO C17 运行时与安全验证骨架；C 翻译与公开 API 证明未完成。",
            },
        },
    }

    return {
        "lean-toolchain": toolchain,
        "lakefile.toml": (
            f'name = "{project_id}-f"\n'
            'version = "0.1.0"\n'
            f'defaultTargets = ["{package}"]\n\n'
            "[[require]]\n"
            'name = "OssProof"\n'
            'path = "../../framework/lean"\n\n'
            "[[lean_lib]]\n"
            f'name = "{package}"\n'
            f'roots = ["{package}", "{package}.Results"]\n'
        ),
        "project.json": json.dumps(project_json, indent=2, ensure_ascii=False) + "\n",
        f"{package}.lean": (
            f"import {package}.Runtime.Heap\n"
            f"import {package}.Spec.Common.Base\n"
            f"import {package}.Spec.Safety.RuntimeUb\n"
            f"import {package}.Proof.RuntimeUb\n"
        ),
        f"{package}/Runtime/Heap.lean": (
            "import OssProof\n\n"
            f"namespace {package}.Runtime\n"
            "open OssProof\n\n"
            "structure Heap where\n"
            "  bytes : Tbl UInt8 := {}\n"
            "  garbage : Nat → UInt64 := fun _ => 0\n\n"
            "abbrev M (α : Type) := OssProof.M Heap α\n\n"
            "instance : Space Heap Nat UInt8 where\n"
            "  get h id := h.bytes.get id\n"
            "  ro h id := h.bytes.ro id\n"
            "  modify h id f := { h with bytes := h.bytes.modify id f }\n\n"
            f"end {package}.Runtime\n"
        ),
        f"{package}/Spec/Common/Base.lean": (
            f"import {package}.Runtime.Heap\n\n"
            f"namespace {package}.Spec.Common\n"
            f"abbrev Heap := {package}.Runtime.Heap\n"
            f"end {package}.Spec.Common\n"
        ),
        f"{package}/Spec/Safety/RuntimeUb.lean": (
            f"import {package}.Spec.Common.Base\n\n"
            f"namespace {package}.Spec.Safety\n"
            "open OssProof\n"
            f"open {package}.Runtime\n\n"
            "def Goal.null_ptr_add_zero_ub : Prop :=\n"
            "  ∀ h : Heap, ∃ msg, Ptr.add (H := Heap) (R := Nat) (T := UInt8) .null 0 h = .error (.ub msg)\n\n"
            "def Goal.dangling_ptr_add_zero_ub : Prop :=\n"
            "  ∀ (h : Heap) (r off : Nat), Space.get (T := UInt8) h r = none →\n"
            "    ∃ msg, Ptr.add (H := Heap) (R := Nat) (T := UInt8) (.ref r off) 0 h = .error (.ub msg)\n\n"
            "def Goal.null_ptr_diff_null_ub : Prop :=\n"
            "  ∀ h : Heap, ∃ msg, Ptr.diff (H := Heap) (R := Nat) (T := UInt8) .null .null h = .error (.ub msg)\n\n"
            "def Goal.cross_object_ptr_diff_ub : Prop :=\n"
            "  ∀ (h : Heap) (r1 r2 o1 o2 : Nat), r1 ≠ r2 →\n"
            "    ∃ msg, Ptr.diff (H := Heap) (R := Nat) (T := UInt8) (.ref r1 o1) (.ref r2 o2) h = .error (.ub msg)\n\n"
            "def Goal.null_memset_zero_ub : Prop :=\n"
            "  ∀ (h : Heap) (v : UInt8),\n"
            "    ∃ msg, Ptr.memset (H := Heap) (R := Nat) (T := UInt8) .null v 0 h = .error (.ub msg)\n\n"
            f"end {package}.Spec.Safety\n"
        ),
        f"{package}/Proof/RuntimeUb.lean": (
            f"import {package}.Spec.Safety.RuntimeUb\n\n"
            f"namespace {package}.Proof.RuntimeUb\n"
            "open OssProof\n"
            f"open {package}.Spec.Safety\n\n"
            "theorem null_ptr_add_zero_ub : Goal.null_ptr_add_zero_ub :=\n"
            "  fun h => Ptr.null_add_zero_ub h\n\n"
            "theorem dangling_ptr_add_zero_ub : Goal.dangling_ptr_add_zero_ub :=\n"
            "  fun h r off hnone => Ptr.dangling_add_zero_ub h r off hnone\n\n"
            "theorem null_ptr_diff_null_ub : Goal.null_ptr_diff_null_ub :=\n"
            "  fun h => Ptr.null_diff_null_ub h\n\n"
            "theorem cross_object_ptr_diff_ub : Goal.cross_object_ptr_diff_ub :=\n"
            "  fun h r1 r2 o1 o2 hne => Ptr.cross_object_diff_ub h r1 r2 o1 o2 hne\n\n"
            "theorem null_memset_zero_ub : Goal.null_memset_zero_ub :=\n"
            "  fun h v => Ptr.null_memset_zero_ub h v\n\n"
            f"end {package}.Proof.RuntimeUb\n"
        ),
        f"{package}/ResultsCheck.lean": results_check_proj,
        f"{package}/Results.lean": (
            f"import {package}\n"
            f"import {package}.ResultsCheck\n\n"
            f"namespace {package}.Results\n"
            "open Lean Elab Command\n\n"
            "def proved : List (Name × Name) := [\n"
            f"  (``{package}.Spec.Safety.Goal.null_ptr_add_zero_ub, ``{package}.Proof.RuntimeUb.null_ptr_add_zero_ub),\n"
            f"  (``{package}.Spec.Safety.Goal.dangling_ptr_add_zero_ub, ``{package}.Proof.RuntimeUb.dangling_ptr_add_zero_ub),\n"
            f"  (``{package}.Spec.Safety.Goal.null_ptr_diff_null_ub, ``{package}.Proof.RuntimeUb.null_ptr_diff_null_ub),\n"
            f"  (``{package}.Spec.Safety.Goal.cross_object_ptr_diff_ub, ``{package}.Proof.RuntimeUb.cross_object_ptr_diff_ub),\n"
            f"  (``{package}.Spec.Safety.Goal.null_memset_zero_ub, ``{package}.Proof.RuntimeUb.null_memset_zero_ub)\n"
            "]\n\n"
            "def notDone : List Name := []\n\n"
            "def required : List Name := [\n"
            f"  ``{package}.Spec.Safety.Goal.null_ptr_add_zero_ub,\n"
            f"  ``{package}.Spec.Safety.Goal.dangling_ptr_add_zero_ub,\n"
            f"  ``{package}.Spec.Safety.Goal.null_ptr_diff_null_ub,\n"
            f"  ``{package}.Spec.Safety.Goal.cross_object_ptr_diff_ub,\n"
            f"  ``{package}.Spec.Safety.Goal.null_memset_zero_ub\n"
            "]\n\n"
            "#eval checkWith proved notDone required inLibrary\n\n"
            f"end {package}.Results\n"
        ),
        "tests/audit/compiler-helpers.txt": (
            "# Compiler-generated execution auxiliaries reviewed for PartialCheck.\n"
        ),
        "patches/README.md": f"# Patches (`{project_id}`)\n\nNo local patches are currently applied.\n",
        "docs/en/overview.md": f"# {title} × Lean\n\nVerification scope and strict ISO C17 runtime model for `{title}`.\n",
        "docs/zh/overview.md": f"# {title} × Lean\n\n`{title}` 的验证范围与严格 ISO C17 运行时模型。\n",
        "docs/en/progress.md": f"# Status of the results (`{title}`)\n\nPublic API verification: **not done**.\n",
        "docs/zh/progress.md": f"# 结论的状态（`{title}`）\n\n公开 API 验证：**未完成**。\n",
    }


def check_results_check_sync() -> list[str]:
    """Verify every registered project's `ResultsCheck.lean` retains the core checks of `framework/lean/ResultsCheck.lean`."""
    required_snippets = (
        "allowedAxioms",
        "isGoalType",
        "expectedType",
        "collectAxioms",
        "ti.type == expectedType g d.type",
        "required goal",
    )
    errors: list[str] = []
    for proj in load_all_projects(REPO):
        rc = proj.root / proj.package / "ResultsCheck.lean"
        if not rc.is_file():
            errors.append(f"[{proj.id}] missing {rc.relative_to(REPO)}")
            continue
        text = rc.read_text()
        for snippet in required_snippets:
            if snippet not in text:
                errors.append(f"[{proj.id}] {rc.relative_to(REPO)} is missing required check fragment `{snippet}`")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-sync", action="store_true", help="Check ResultsCheck.lean consistency across projects")
    parser.add_argument("project_id", nargs="?", help="Project ID under projects/<id>/ to scaffold")
    parser.add_argument("--package", help="Lean package name (default: CamelCaseF)")
    parser.add_argument("--title", help="Display title (default: project_id)")
    parser.add_argument("--submodule", help="Upstream submodule folder name (default: project_id)")
    parser.add_argument("--repo-url", default="https://example.invalid/upstream", help="Upstream repository URL")
    parser.add_argument("--out-dir", type=Path, help="Override destination directory (default: projects/<id>)")
    parser.add_argument("--dry-run", action="store_true", help="Print planned files without writing")
    args = parser.parse_args()

    if args.check_sync:
        errs = check_results_check_sync()
        for e in errs:
            print(e, file=sys.stderr)
        if errs:
            return 1
        print("ResultsCheck.lean core invariants verified across all registered projects")
        return 0

    if not args.project_id:
        parser.error("provide <project_id> or --check-sync")

    pid = args.project_id
    pkg = args.package or default_package_name(pid)
    title = args.title or pid
    sub = args.submodule or pid
    dest = args.out_dir or (REPO / "projects" / pid)
    files = render_files(pid, pkg, title, sub, args.repo_url)

    if args.dry_run:
        print(f"Would scaffold {len(files)} files into {dest}:")
        for rel in sorted(files):
            print("  " + rel)
        return 0

    created = 0
    for rel, content in files.items():
        path = dest / rel
        if path.exists():
            print(f"  skip (exists): {path}")
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        created += 1
    print(f"Scaffolded {created} new file(s) in {dest} (package {pkg}, wired to OssProof)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
