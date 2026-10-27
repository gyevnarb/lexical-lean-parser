from __future__ import annotations

import json
import subprocess

import pytest

from lexical_lean_parser import (
    build_dependency_graph,
    deps_to_dict,
    deps_to_str,
    parse_commit,
    parse_dependencies,
)
from lexical_lean_parser.cli import main

FILES = {
    "Lib/A.lean": """
        def base : Nat := 0
        """,
    "Lib/B.lean": """
        import Lib.A

        -- TODO
        theorem uses_base : base = 0 := rfl
        """,
}


def test_deps_to_dict_and_str(make_project):
    project = make_project(FILES)
    deps = parse_dependencies(project)
    d = deps_to_dict(deps, project)
    assert d["Lib/B.lean"] == [{
        "kind": "theorem", "namespace": None, "name": "uses_base", "n_todos": 1,
        "depends_on": [{"kind": "def", "namespace": None, "name": "base"}],
    }]
    assert deps_to_dict(deps, project, include_imports=True)["Lib/B.lean"][0]["kind"] == "import"
    assert "Module Lib.B:\n    theorem uses_base\n        Depends on: def base" in \
        deps_to_str(deps, project)


def test_graph(make_project):
    pytest.importorskip("networkx")
    project = make_project(FILES)
    G = build_dependency_graph(parse_dependencies(project), project, include_imports=False)
    src = ("theorem", "Lib.B", None, "uses_base")
    dst = ("def", "Lib.A", None, "base")
    assert set(G.nodes) == {src, dst}
    # `weight` counts occurrences in the body only; `base` appears in the statement.
    assert G.edges[src, dst] == {"weight": 0, "from_def": True, "from_body": False}
    assert G.nodes[src]["n_todos"] == 1


def test_relative_project_path(make_project, monkeypatch):
    pytest.importorskip("networkx")
    project = make_project(FILES)
    monkeypatch.chdir(project.parent)
    rel = type(project)(project.name)
    deps = parse_dependencies(rel)
    assert set(deps_to_dict(deps, rel)) == {"Lib/A.lean", "Lib/B.lean"}
    assert "Module Lib.A:" in deps_to_str(deps, rel)
    assert len(build_dependency_graph(deps, rel)) == 3


def test_parse_commit_leaves_working_tree_alone(make_project):
    project = make_project(FILES)

    def git(*args: str) -> str:
        return subprocess.run(["git", "-C", str(project), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    git("init", "-q")
    git("-c", "user.name=t", "-c", "user.email=t@t", "add", ".")
    git("-c", "user.name=t", "-c", "user.email=t@t", "commit", "-qm", "init")
    (project / "Lib/A.lean").write_text("def renamed : Nat := 0\n")

    deps = parse_commit(project, "HEAD")
    assert set(deps) == {project / "Lib/A.lean", project / "Lib/B.lean"}
    names = {d.name for items in deps.values() for d in items if hasattr(d, "body")}
    assert names == {"base", "uses_base"}
    assert all(d.file.parent == project / "Lib" for items in deps.values() for d in items)
    assert (project / "Lib/A.lean").read_text() == "def renamed : Nat := 0\n"


def test_cli(make_project, capsys):
    project = make_project(FILES)
    assert main([str(project)]) == 0
    out = json.loads(capsys.readouterr().out)
    assert set(out) == {"Lib/A.lean", "Lib/B.lean"}
    assert main([str(project), "--format", "text"]) == 0
    assert "Module Lib.A:" in capsys.readouterr().out
