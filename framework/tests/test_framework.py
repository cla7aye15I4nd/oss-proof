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

from framework import check_forbidden, check_options, check_runtime_ub, check_spec_layers, ci_matrix, manifest, run_difftest


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


if __name__ == "__main__":
    unittest.main()
