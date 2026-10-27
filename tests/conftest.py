from __future__ import annotations

import textwrap
from pathlib import Path

import pytest


@pytest.fixture
def make_project(tmp_path: Path):
    """Write `{relative path: source}` into a fresh directory and return it."""

    def make(files: dict[str, str]) -> Path:
        for rel, src in files.items():
            path = tmp_path / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(textwrap.dedent(src).lstrip("\n"), encoding="utf-8")
        return tmp_path

    return make
