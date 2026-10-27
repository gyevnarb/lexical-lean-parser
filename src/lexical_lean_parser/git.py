"""Parse a repository as it was at a given commit, without touching its working tree."""

from __future__ import annotations

import io
import subprocess
import tarfile
import tempfile
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import TYPE_CHECKING

from lexical_lean_parser.graph import build_dependency_graph
from lexical_lean_parser.model import DepMap
from lexical_lean_parser.parser import parse_dependencies

if TYPE_CHECKING:
    import networkx as nx


@contextmanager
def checkout(repo_dir: Path, commit: str) -> Iterator[Path]:
    """Extract the tree of `commit` into a temporary directory, removed on exit.

    Uses `git archive`, so it never modifies the repository and is safe to run in parallel.
    Submodules are not included.
    """
    archive = subprocess.run(
        ["git", "-C", str(repo_dir), "archive", "--format=tar", commit],  # noqa: S607
        capture_output=True, check=True,
    ).stdout
    with tempfile.TemporaryDirectory(prefix="lean-checkout-") as tmp, \
            tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        if hasattr(tarfile, "data_filter"):
            tar.extractall(tmp, filter="data")
        else:  # Python < 3.10.12 without the extraction filters; the archive is git's own
            tar.extractall(tmp)  # noqa: S202
        yield Path(tmp).resolve()


def parse_commit(repo_dir: Path, commit: str, **kwargs) -> DepMap:
    """`parse_dependencies` on the tree of `commit`, with paths relative to the repository.

    Keyword arguments are passed on to `parse_dependencies`.
    """
    with checkout(repo_dir, commit) as tree:
        deps = parse_dependencies(tree, **kwargs)
    # Re-anchor every path from the (now deleted) temporary tree onto the repository.
    root = Path(repo_dir).resolve()
    for items in deps.values():
        for item in items:
            item.file = root / item.file.relative_to(tree)
    return {root / file.relative_to(tree): items for file, items in deps.items()}


def build_graph_at_commit(
    repo_dir: Path,
    commit: str,
    *,
    file_pattern: str | None = None,
    skip_self_refs: bool = True,
    include_imports: bool = False,
    remove_unconnected: bool = False,
    cross_file_only: bool = False,
) -> nx.DiGraph:
    """Parse `repo_dir` at `commit` and build its graph, as `build_dependency_graph` does."""
    deps = parse_commit(repo_dir, commit, file_pattern=file_pattern,
                        skip_self_refs=skip_self_refs)
    return build_dependency_graph(deps, Path(repo_dir).resolve(),
                                  include_imports=include_imports,
                                  cross_file_only=cross_file_only,
                                  remove_unconnected=remove_unconnected)
