#!/usr/bin/env python3
"""Unit tests for the shared oss-proof verification framework."""
from __future__ import annotations

import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))

from framework import (
    build_guarded,
    check_forbidden,
    check_options,
    check_project,
    check_proof_hygiene,
    check_runtime_ub,
    check_spec_layers,
    ci_matrix,
    manifest,
    patches,
    plan_proof,
    preflight,
    run_difftest,
    scaffold_project,
)


class FrameworkTests(unittest.TestCase):
    def test_registered_projects_load_and_pass_options(self):
        projects = manifest.load_all_projects(REPO)
        self.assertTrue(any(p.id == "zlib" for p in projects))
        self.assertEqual(check_options.check_repo(REPO), [])

    def test_forbidden_constructs_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "FooF").mkdir()
            (root / "FooF.lean").write_text("import FooF.A\n")
            mod = root / "FooF/A.lean"
            mod.write_text("theorem ok : True := trivial\n")
            self.assertEqual(check_forbidden.check_project_forbidden(root, "FooF"), [])

            for snippet in (
                "theorem bad : True := by native_decide",
                "theorem bad2 : True := by bv_decide",
                "axiom cheat : False",
                "partial def loop : Nat → Nat | n => loop n",
                "unsafe def raw : Nat := 0",
                "opaque secret : Nat := 0",
                "@[extern \"c_fn\"] def ext : IO Unit := pure ()",
                "@[implemented_by other] def swap : Nat := 0",
            ):
                with self.subTest(snippet=snippet):
                    mod.write_text(snippet + "\n")
                    self.assertTrue(check_forbidden.check_project_forbidden(root, "FooF"))

    def test_options_and_toolchain_checks(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            (repo / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
            (repo / "framework").mkdir()
            (repo / "framework/projects.json").write_text(json.dumps({"version": 1, "projects": ["demo"]}))
            proj = repo / "projects/demo"
            (proj / "DemoF").mkdir(parents=True)
            (proj / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
            (proj / "lakefile.toml").write_text(
                'name = "DemoF"\nversion = "0.1.0"\ndefaultTargets = ["DemoF"]\n'
                '[[lean_lib]]\nname = "DemoF"\nroots = ["DemoF", "DemoF.Results"]\n'
            )
            (proj / "project.json").write_text(
                json.dumps(
                    {
                        "version": 1,
                        "id": "demo",
                        "title": "demo",
                        "package": "DemoF",
                        "upstream": {"submodule": "upstream"},
                        "build": {"targets": ["DemoF"], "results_module": "DemoF.Results"},
                    }
                )
            )
            (proj / "DemoF.lean").write_text("import DemoF.A\n")
            (proj / "DemoF/A.lean").write_text("set_option autoImplicit false\ntheorem t : True := trivial\n")
            self.assertEqual(check_options.check_repo(repo), [])

            # Mismatched toolchain fails
            (proj / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
            self.assertTrue(check_options.check_repo(repo))
            (proj / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")

            # Root lakefile fails
            (repo / "lakefile.toml").write_text('name = "Root"\n')
            self.assertTrue(check_options.check_repo(repo))
            (repo / "lakefile.toml").unlink()

            # Forbidden set_option fails
            (proj / "DemoF/A.lean").write_text("set_option «debug».skipKernelTC true\n")
            self.assertTrue(check_options.check_repo(repo))

    def test_spec_layer_checker_for_arbitrary_package(self):
        with tempfile.TemporaryDirectory() as tmp:
            proj = Path(tmp)
            for sub in ("Spec/Common", "Spec/Safety", "Spec/Functional", "Proof", "Math"):
                (proj / "ZstdF" / sub).mkdir(parents=True)
            (proj / "ZstdF/Spec/Common/Base.lean").write_text("def x : Nat := 1\n")
            (proj / "ZstdF/Spec/Safety/Safe.lean").write_text(
                "import ZstdF.Spec.Common.Base\ndef Goal.safe : Prop := True\n"
            )
            (proj / "ZstdF/Spec/Functional/Full.lean").write_text(
                "import ZstdF.Spec.Common.Base\ndef Goal.full : Prop := True\n"
            )
            (proj / "ZstdF/Proof/SafeProof.lean").write_text("import ZstdF.Spec.Safety.Safe\n")
            checker = check_spec_layers.SpecLayerChecker(proj, "ZstdF")
            errors, count, _ = checker.run()
            self.assertEqual(errors, [])
            self.assertEqual(count, 3)

            # Safety importing Functional must fail
            (proj / "ZstdF/Spec/Safety/Safe.lean").write_text("import ZstdF.Spec.Functional.Full\n")
            errors, _, _ = check_spec_layers.SpecLayerChecker(proj, "ZstdF").run()
            self.assertTrue(any("imports functional" in e for e in errors))

    def test_ci_matrix_scoping(self):
        p_zlib = manifest.Project(
            id="zlib",
            root=REPO / "projects/zlib",
            data=json.loads((REPO / "projects/zlib/project.json").read_text()),
        )
        p_zstd = manifest.Project(
            id="zstd",
            root=REPO / "projects/zstd",
            data={
                "version": 1,
                "id": "zstd",
                "title": "zstd",
                "package": "ZstdF",
                "upstream": {"submodule": "zstd"},
                "build": {"targets": ["ZstdF"], "results_module": "ZstdF.Results"},
                "difftest": {"watch_paths": ["ZstdF/Zstd/", "patches/"]},
            },
        )
        projects = [p_zlib, p_zstd]

        # Push to main runs everything
        self.assertEqual(ci_matrix.compute_matrices(projects, "push", ["README.md"]), (["zlib", "zstd"], ["zlib", "zstd"]))

        # Shared framework change on PR runs everything
        self.assertEqual(
            ci_matrix.compute_matrices(projects, "pull_request", ["framework/check_options.py"]),
            (["zlib", "zstd"], ["zlib", "zstd"]),
        )

        # Proof-only change in zlib builds only zlib and skips difftest
        self.assertEqual(
            ci_matrix.compute_matrices(projects, "pull_request", ["projects/zlib/ZlibF/Proof/foo.lean"]),
            (["zlib"], []),
        )

        # Translation change in zstd builds and difftests only zstd
        self.assertEqual(
            ci_matrix.compute_matrices(projects, "pull_request", ["projects/zstd/ZstdF/Zstd/dec.c.lean"]),
            (["zstd"], ["zstd"]),
        )

        # Site-only change skips Lean builds and difftests on PR
        self.assertEqual(
            ci_matrix.compute_matrices(projects, "pull_request", ["site/portal.py"]),
            ([], []),
        )

    def test_runtime_ub_policy_rejects_wild_ptr_add_zero_and_null_diff(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "projects/zstd"
            rt = root / "ZstdF/Runtime"
            rt.mkdir(parents=True)
            proj = manifest.Project(
                id="zstd",
                root=root,
                data={
                    "version": 1,
                    "id": "zstd",
                    "title": "zstd",
                    "package": "ZstdF",
                    "upstream": {"submodule": "zstd"},
                    "build": {"targets": ["ZstdF"], "results_module": "ZstdF.Results"},
                },
            )
            # Strict Ptr.lean passes
            (rt / "Ptr.lean").write_text(
                "def Ptr.add (p : Ptr R) (k : Int) : M (Ptr R) := fun h =>\n"
                "  match p with\n"
                "  | .null => .error (.ub \"null\")\n"
                "  | .ref r off => .ok (p, h)\n"
            )
            (rt / "Libc.lean").write_text("def Ptr.memcpy := 0\n")
            self.assertEqual(check_runtime_ub.check_project_runtime_ub(proj, base=Path(tmp)), [])

            # Wild/NULL pointer + 0 shortcut (`if k = 0 then .ok`) is rejected!
            (rt / "Ptr.lean").write_text(
                "def Ptr.add (p : Ptr R) (k : Int) : M (Ptr R) := fun h =>\n"
                "  if k = 0 then .ok (p, h) else .error (.ub \"bad\")\n"
            )
            errs = check_runtime_ub.check_project_runtime_ub(proj, base=Path(tmp))
            self.assertEqual(len(errs), 1)
            self.assertIn("ISO C17", errs[0])

            # NULL - NULL shortcut is rejected!
            (rt / "Ptr.lean").write_text(
                "def Ptr.diff (p q : Ptr R) : M Int64 := fun h =>\n"
                "  match p, q with\n"
                "  | .null, .null => .ok (0, h)\n"
                "  | _, _ => .error (.ub \"bad\")\n"
            )
            errs = check_runtime_ub.check_project_runtime_ub(proj, base=Path(tmp))
            self.assertEqual(len(errs), 1)
            self.assertIn("NULL - NULL", errs[0])

            # Zero-length memcpy shortcut is rejected!
            (rt / "Ptr.lean").write_text("def Ptr.add := 0\n")
            (rt / "Libc.lean").write_text(
                "def Ptr.memcpy (dst src : Ptr R) (n : Nat) : M Unit := fun h =>\n"
                "  if n = 0 then .ok ((), h) else .error (.ub \"bad\")\n"
            )
            errs = check_runtime_ub.check_project_runtime_ub(proj, base=Path(tmp))
            self.assertEqual(len(errs), 1)
            self.assertIn("n = 0", errs[0])

    def test_difftest_driver_targets_for_zlib(self):
        targets = run_difftest.driver_targets(REPO / "projects/zlib/tests/list.txt")
        self.assertIn("difftest_inflate", targets)
        self.assertIn("difftest_deflate", targets)
        self.assertTrue(all(t.startswith("difftest_") for t in targets))

    def _patch_project(self, tmp: Path, layout: str | None, count: int | None) -> tuple[Path, dict]:
        root = tmp / "proj"
        up = root / "up"
        up.mkdir(parents=True)
        (up / "a.c").write_text("int a;\n")
        (up / "test").mkdir()
        (up / "test/t.cc").write_text("// t\n")
        (root / "patches").mkdir()
        upstream = {"submodule": "up", "patches_dir": "patches"}
        if layout:
            upstream["patch_layout"] = layout
        data = {"upstream": upstream, "site": {} if count is None else {"patches_count": count}}
        return root, data

    @staticmethod
    def _series(old: str, new: str, test: bool) -> str:
        text = f"From 0 Mon Sep 17 00:00:00 2001\nSubject: [PATCH] x\n\n---\n" \
               f"diff --git a/a.c b/a.c\n--- a/a.c\n+++ b/a.c\n@@ -1 +1 @@\n-{old}\n+{new}\n"
        if test:
            text += "diff --git a/test/t.cc b/test/t.cc\n--- a/test/t.cc\n+++ b/test/t.cc\n@@ -1 +1,2 @@\n // t\n+// more\n"
        return text

    def test_patch_layouts(self):
        with tempfile.TemporaryDirectory() as raw:
            tmp = Path(raw)
            # Flat layout: other projects keep patches/*.patch.
            root, data = self._patch_project(tmp / "flat", None, 1)
            (root / "patches/0001-x.patch").write_text(self._series("int a;", "int b;", False))
            self.assertEqual(patches.check_project_patches("demo", root, data), 1)
            # Flat layout with no patches and none declared passes; declared but missing fails loudly.
            root, data = self._patch_project(tmp / "none", None, 0)
            self.assertEqual(patches.check_project_patches("demo", root, data), 0)
            root, data = self._patch_project(tmp / "missing", None, 2)
            with self.assertRaises(patches.PatchError):
                patches.check_project_patches("demo", root, data)

            # Directory layout: two series, the second on top of the first (library and test hunks).
            root, data = self._patch_project(tmp / "dirs", "directories", 2)
            pd = root / "patches"
            for name, old, new in (("0001-first", "int a;", "int b;"), ("0002-second", "int b;", "int c;")):
                (pd / name).mkdir()
                (pd / name / "upstream.patch").write_text(self._series(old, new, name.startswith("0001")))
                (pd / name / "pr-summary.md").write_text("# x\n")
            (pd / "README.md").write_text(
                "| Patch | x |\n| --- | --- |\n"
                "| [0001-first](0001-first/pr-summary.md) | a |\n| [0002-second](0002-second/pr-summary.md) | b |\n"
            )
            self.assertEqual(patches.check_project_patches("demo", root, data), 2)
            # A wrong declared count, a missing file, a stray flat patch, a gap in the numbering, a README that
            # does not list a directory, and a series that does not apply in order all fail.
            data["site"]["patches_count"] = 3
            with self.assertRaisesRegex(patches.PatchError, "patches_count"):
                patches.check_project_patches("demo", root, data)
            data["site"]["patches_count"] = 2
            (pd / "0002-second/pr-summary.md").unlink()
            with self.assertRaisesRegex(patches.PatchError, "missing pr-summary.md"):
                patches.check_project_patches("demo", root, data)
            (pd / "0002-second/pr-summary.md").write_text("# x\n")
            (pd / "0003-x.patch").write_text("")
            with self.assertRaisesRegex(patches.PatchError, "flat patch files"):
                patches.check_project_patches("demo", root, data)
            (pd / "0003-x.patch").unlink()
            (pd / "0002-second").rename(pd / "0003-second")
            with self.assertRaisesRegex(patches.PatchError, "expected number 0002"):
                patches.check_project_patches("demo", root, data)
            (pd / "0003-second").rename(pd / "0002-second")
            readme = (pd / "README.md").read_text()
            (pd / "README.md").write_text(readme.replace("| [0002-second](0002-second/pr-summary.md) | b |\n", ""))
            with self.assertRaisesRegex(patches.PatchError, "do not list exactly"):
                patches.check_project_patches("demo", root, data)
            (pd / "README.md").write_text(readme)
            (pd / "0002-second/upstream.patch").write_text(self._series("int a;", "int c;", False))
            with self.assertRaisesRegex(patches.PatchError, "does not apply"):
                patches.check_project_patches("demo", root, data)
            # An empty directory layout fails instead of passing silently.
            root, data = self._patch_project(tmp / "empty", "directories", 0)
            (root / "patches/README.md").write_text("# none\n")
            with self.assertRaisesRegex(patches.PatchError, "none were found"):
                patches.check_project_patches("demo", root, data)

    def test_zlib_ng_patch_directories(self):
        proj = manifest.load_project("zlib-ng", REPO)
        self.assertEqual(proj.data["upstream"].get("patch_layout"), "directories")
        series = patches.discover(proj.root / "patches", "directories")
        self.assertEqual(len(series), proj.data["site"]["patches_count"])
        self.assertTrue(all(p.name == "upstream.patch" for p in series))

    def test_options_allows_only_local_ossproof_require(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "DemoF").mkdir()
            (root / "DemoF.lean").write_text("")
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n")
            (root / "lakefile.toml").write_text(
                'name = "demo-f"\nversion = "0.1.0"\ndefaultTargets = ["DemoF"]\n'
                '[[require]]\nname = "OssProof"\npath = "../../framework/lean"\n'
                '[[lean_lib]]\nname = "DemoF"\nroots = ["DemoF", "DemoF.Results"]\n'
            )
            self.assertEqual(
                check_options.check_project_options(root, "DemoF", root_toolchain="leanprover/lean4:v4.36.0\n"),
                [],
            )
            # Any non-OssProof dependency must be rejected.
            (root / "lakefile.toml").write_text(
                'name = "demo-f"\nversion = "0.1.0"\ndefaultTargets = ["DemoF"]\n'
                '[[require]]\nname = "Mathlib"\npath = "../mathlib"\n'
                '[[lean_lib]]\nname = "DemoF"\nroots = ["DemoF"]\n'
            )
            errs = check_options.check_project_options(root, "DemoF", root_toolchain="leanprover/lean4:v4.36.0\n")
            self.assertTrue(any("OssProof" in e for e in errs))

    def test_forbidden_strips_comments_and_catches_sorry_and_multiline(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "FooF").mkdir()
            (root / "FooF.lean").write_text("import FooF.A\n")
            mod = root / "FooF/A.lean"
            # Comments and string literals must not false-positive.
            mod.write_text(
                "/- sorry axiom native_decide -/\n"
                '-- admit partial def\n'
                'def msg : String := "sorry bv_decide"\n'
            )
            self.assertEqual(check_forbidden.check_project_forbidden(root, "FooF"), [])
            # `sorry` is rejected by default, allowed only with allow_sorry=True.
            mod.write_text("theorem t : True := by sorry -- comment\n")
            self.assertTrue(check_forbidden.check_project_forbidden(root, "FooF"))
            self.assertEqual(check_forbidden.check_project_forbidden(root, "FooF", allow_sorry=True), [])
            # Multiline `partial\ndef` is caught.
            mod.write_text("partial\ndef loop : Nat → Nat | n => loop n\n")
            self.assertTrue(check_forbidden.check_project_forbidden(root, "FooF"))
        # Shared OssProof core itself must have zero forbidden constructs.
        self.assertEqual(check_forbidden.check_shared_core_forbidden(REPO), [])

    def test_runtime_ub_catches_memcmp_and_renamed_params(self):
        with tempfile.TemporaryDirectory() as tmp:
            rt = Path(tmp) / "Runtime"
            rt.mkdir()
            (rt / "Ptr.lean").write_text(
                "def Ptr.add (p : Ptr R) (delta : Int) : M (Ptr R) := fun h =>\n"
                "  if delta = 0 then .ok (p, h) else .error (.ub \"bad\")\n"
            )
            errs = check_runtime_ub.check_runtime_dir_ub(rt, "demo", base=Path(tmp))
            self.assertEqual(len(errs), 1)
            (rt / "Ptr.lean").write_text("def Ptr.add := 0\n")
            (rt / "Libc.lean").write_text(
                "def Ptr.memcmp (a b : Ptr R) (len : Nat) : M Int32 := fun h =>\n"
                "  if len == 0 then .ok (0, h) else .error (.ub \"bad\")\n"
            )
            errs = check_runtime_ub.check_runtime_dir_ub(rt, "demo", base=Path(tmp))
            self.assertEqual(len(errs), 1)
        # Shared OssProof runtime must pass strict UB check.
        self.assertEqual(
            check_runtime_ub.check_runtime_dir_ub(REPO / "framework/lean/OssProof/Runtime", "OssProof", base=REPO),
            [],
        )

    def test_ci_matrix_skips_doc_only_changes(self):
        p_zlib = manifest.load_project("zlib", REPO)
        self.assertEqual(
            ci_matrix.compute_matrices([p_zlib], "pull_request", ["projects/zlib/docs/en/overview.md"]),
            ([], []),
        )
        self.assertEqual(
            ci_matrix.compute_matrices([p_zlib], "pull_request", ["projects/zlib/AGENTS.md"]),
            ([], []),
        )
        self.assertEqual(
            ci_matrix.compute_matrices([p_zlib], "pull_request", ["framework/PROOF_PLAYBOOK.md"]),
            ([], []),
        )

    def test_check_patches_apply_rejects_uninitialized_submodule(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "proj"
            (root / "up").mkdir(parents=True)  # Empty dir without `.git`
            proj = manifest.Project(
                id="demo",
                root=root,
                data={
                    "version": 1,
                    "id": "demo",
                    "title": "demo",
                    "package": "DemoF",
                    "upstream": {"submodule": "up", "patches_dir": "patches"},
                    "build": {"targets": ["DemoF"], "results_module": "DemoF.Results"},
                },
            )
            with self.assertRaisesRegex(RuntimeError, "not initialized"):
                check_project.check_patches_apply(proj)

    def test_proof_hygiene_and_orphan_detection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for sub in ("DemoF/Proof", "DemoF/Spec/Safety", "DemoF/Spec/Common"):
                (root / sub).mkdir(parents=True)
            (root / "DemoF.lean").write_text("import DemoF.Proof.A\n")
            (root / "DemoF/Results.lean").write_text("import DemoF\n")
            (root / "DemoF/Proof/A.lean").write_text(
                "set_option maxHeartbeats 1000000\n"
                "def recBad (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => recBad k\n"
                "theorem bad : True := by decide +kernel\n"
            )
            (root / "DemoF/Proof/Orphan.lean").write_text("theorem unused : True := trivial\n")
            (root / "DemoF/Spec/Safety/G.lean").write_text("def Goal.stub : Prop := True\n")
            proj = manifest.Project(
                id="demo",
                root=root,
                data={
                    "version": 1,
                    "id": "demo",
                    "title": "demo",
                    "package": "DemoF",
                    "upstream": {"submodule": "up"},
                    "build": {"targets": ["DemoF"], "results_module": "DemoF.Results"},
                },
            )
            self.assertEqual(check_project.check_orphan_modules(proj), ["DemoF.Proof.Orphan", "DemoF.Spec.Safety.G"])
            rep = check_proof_hygiene.analyze_project(proj)
            self.assertEqual(len(rep["rec_defs"]), 1)
            self.assertEqual(len(rep["decide_kernels"]), 1)
            self.assertEqual(len(rep["heartbeats"]), 1)
            self.assertEqual(len(rep["placeholder_goals"]), 1)

    def test_plan_proof_topological_waves(self):
        with tempfile.TemporaryDirectory() as tmp:
            c_file = Path(tmp) / "sample.c"
            c_file.write_text(
                "static int leaf(int x) { return x + 1; }\n"
                "static int mid(int *p, int n) { int s = 0; for (int i = 0; i < n; i++) s += leaf(p[i]); return s; }\n"
                "int entry(int *p, int n) { return mid(p, n); }\n"
            )
            funcs = plan_proof.scan_c_file(c_file, Path(tmp))
            waves = plan_proof.plan_waves(funcs)
            self.assertEqual([[f["name"] for f in w] for w in waves], [["leaf"], ["mid"], ["entry"]])

    def test_build_guarded_config_and_routing(self):
        defaults, builders = build_guarded.load_builders_config(REPO / "framework/builders.example.toml")
        self.assertEqual(defaults["memory_max_gb"], 16)
        self.assertEqual(len(builders), 2)
        lean_cands = build_guarded.select_candidate_builders(builders, required_capability="lean")
        diff_cands = build_guarded.select_candidate_builders(builders, required_capability="difftest")
        self.assertEqual(len(lean_cands), 2)
        self.assertEqual([b.name for b in diff_cands], ["builder-b"])
        self.assertEqual(len(build_guarded.ssh_endpoints(builders[0])), 2)

    def test_preflight_privacy_leak_scanner(self):
        bad_diff = (
            "+++ b/framework/foo.py\n"
            "+HOST = '100.81.85.26'\n"
            "+PATH = '/Users/alice/repo'\n"
            "+Co-Authored-By: Bot\n"
        )
        hits = preflight.scan_added_diff_leaks(bad_diff)
        self.assertEqual(len(hits), 3)
        clean_diff = "+++ b/framework/foo.py\n+HOST = 'build-host.example.invalid'\n"
        self.assertEqual(preflight.scan_added_diff_leaks(clean_diff), [])

    def test_scaffold_project_passes_static_gates(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "projects/demo"
            files = scaffold_project.render_files("demo", "DemoF", "demo", "demo", "https://example.invalid/demo")
            for rel, content in files.items():
                p = dest / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(content)
            root_tc = (REPO / "lean-toolchain").read_text()
            self.assertEqual(check_options.check_project_options(dest, "DemoF", root_toolchain=root_tc), [])
            self.assertEqual(check_forbidden.check_project_forbidden(dest, "DemoF"), [])
            errs, count, _ = check_spec_layers.SpecLayerChecker(dest, "DemoF").run()
            self.assertEqual(errs, [])
            self.assertEqual(count, 2)
            proj = manifest.Project(id="demo", root=dest, data=json.loads((dest / "project.json").read_text()))
            self.assertEqual(check_project.check_orphan_modules(proj), [])

    def test_portal_done_requires_full_public_api_coverage(self):
        sys.path.insert(0, str(REPO / "site"))
        import portal

        zlib_summary = portal.summarize_project(manifest.load_project("zlib", REPO))
        self.assertTrue(zlib_summary.done)
        zng_summary = portal.summarize_project(manifest.load_project("zlib-ng", REPO))
        if zng_summary.proved_functions < zng_summary.documented_functions:
            self.assertFalse(zng_summary.done)


if __name__ == "__main__":
    unittest.main()
