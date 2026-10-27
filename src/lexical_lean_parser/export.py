"""Serialise a parse to JSON-ready dictionaries or to plain text."""

from __future__ import annotations

from pathlib import Path

from lexical_lean_parser.model import Declaration, DepMap, Import


def deps_to_dict(
    deps: DepMap, base_dir: Path, verbose: bool = False, include_imports: bool = False
) -> dict[str, list[dict]]:
    """Map each file, relative to `base_dir`, to its declarations (and imports) as dicts."""
    base_dir = Path(base_dir).resolve()
    return {
        str(file.relative_to(base_dir)): [
            item.to_dict(verbose)
            for item in items
            if isinstance(item, Declaration) or (include_imports and isinstance(item, Import))
        ]
        for file, items in deps.items()
    }


def deps_to_str(deps: DepMap, base_dir: Path, include_imports: bool = False) -> str:
    """Render a parse as an indented, human- and LLM-readable outline."""
    base_dir = Path(base_dir).resolve()
    lines = []
    for file, items in deps.items():
        module = Path(file).relative_to(base_dir).with_suffix("").as_posix().replace("/", ".")
        lines.append(f"Module {module}:")
        for item in items:
            if include_imports and isinstance(item, Import):
                lines.append(f"    import {item.name}")
            elif isinstance(item, Declaration):
                lines.append(f"    {item.kind} {item.name}")
                names = "; ".join(f"{dep.kind} {dep.name}" for dep in item.depends_on)
                lines.append(f"        Depends on: {names or 'None'}")
        lines.append("")
    return "\n".join(lines)
