"""Load and validate oss-proof project manifests."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import json
import re

REPO = Path(__file__).resolve().parents[1]
PROJECT_ID = re.compile(r"^[a-z0-9][a-z0-9-]*$")
PACKAGE_NAME = re.compile(r"^[A-Z][A-Za-z0-9_]*$")


class ManifestError(ValueError):
    pass


def check_relative_path(raw: str, *, allow_empty: bool = False) -> Path:
    if not isinstance(raw, str) or (not raw and not allow_empty):
        raise ManifestError(f"expected non-empty relative path, got {raw!r}")
    path = Path(raw)
    if path.is_absolute() or ".." in path.parts:
        raise ManifestError(f"path escapes project root: {raw!r}")
    return path


@dataclass(frozen=True)
class Project:
    id: str
    root: Path
    data: dict

    @property
    def title(self) -> str:
        return self.data["title"]

    @property
    def package(self) -> str:
        return self.data["package"]

    @property
    def targets(self) -> tuple[str, ...]:
        return tuple(self.data["build"]["targets"])

    @property
    def results_module(self) -> str:
        return self.data["build"]["results_module"]

    @property
    def compiler_helpers(self) -> Path | None:
        raw = self.data["build"].get("compiler_helpers")
        return self.root / check_relative_path(raw) if raw else None


def registered_ids(repo: Path = REPO) -> list[str]:
    registry_path = repo / "framework/projects.json"
    if not registry_path.is_file():
        raise ManifestError(f"missing registry: {registry_path}")
    raw = json.loads(registry_path.read_text())
    if raw.get("version") != 1:
        raise ManifestError("framework/projects.json must have version 1")
    projects = raw.get("projects")
    if not isinstance(projects, list) or not projects:
        raise ManifestError("framework/projects.json must list at least one project")
    if len(projects) != len(set(projects)):
        raise ManifestError("duplicate project id in framework/projects.json")
    for pid in projects:
        if not isinstance(pid, str) or not PROJECT_ID.match(pid):
            raise ManifestError(f"invalid project id: {pid!r}")
    return list(projects)


def load_project(pid: str, repo: Path = REPO) -> Project:
    if not PROJECT_ID.match(pid):
        raise ManifestError(f"invalid project id: {pid!r}")
    root = repo / "projects" / pid
    manifest_path = root / "project.json"
    if not manifest_path.is_file():
        raise ManifestError(f"missing project manifest: {manifest_path}")
    data = json.loads(manifest_path.read_text())
    if data.get("version") != 1:
        raise ManifestError(f"{pid}: project.json must have version 1")
    if data.get("id") != pid:
        raise ManifestError(f"{pid}: project.json id {data.get('id')!r} does not match directory")
    package = data.get("package")
    if not isinstance(package, str) or not PACKAGE_NAME.match(package):
        raise ManifestError(f"{pid}: invalid Lean package name {package!r}")
    if not isinstance(data.get("title"), str) or not data["title"].strip():
        raise ManifestError(f"{pid}: missing title")
    build = data.get("build")
    if not isinstance(build, dict) or not build.get("targets") or not build.get("results_module"):
        raise ManifestError(f"{pid}: build section must define targets and results_module")
    upstream = data.get("upstream")
    if not isinstance(upstream, dict) or not upstream.get("submodule"):
        raise ManifestError(f"{pid}: upstream section must name submodule")
    check_relative_path(upstream["submodule"])
    if upstream.get("patches_dir"):
        check_relative_path(upstream["patches_dir"])
    if build.get("compiler_helpers"):
        check_relative_path(build["compiler_helpers"])
    return Project(id=pid, root=root, data=data)


def load_all_projects(repo: Path = REPO) -> list[Project]:
    return [load_project(pid, repo) for pid in registered_ids(repo)]
