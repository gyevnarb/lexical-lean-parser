"""Command-line interface: ``lean-deps PROJECT_DIR``."""

from __future__ import annotations

import argparse
import json
import logging
import sys
from pathlib import Path

from lexical_lean_parser import __version__
from lexical_lean_parser.export import deps_to_dict, deps_to_str
from lexical_lean_parser.git import parse_commit
from lexical_lean_parser.parser import DEFAULT_FILE_PATTERN, parse_dependencies


def main(argv: list[str] | None = None) -> int:
    """Parse a Lean project and print its declarations and their dependencies."""
    ap = argparse.ArgumentParser(
        prog="lean-deps",
        description="Extract Lean 4 declarations and the dependencies between them.",
    )
    ap.add_argument("project", type=Path, help="Lean project directory.")
    ap.add_argument("-c", "--commit", help="Parse this git revision instead of the working "
                    "tree (the working tree is left untouched).")
    ap.add_argument("-f", "--format", choices=("json", "text"), default="json",
                    help="Output format (default: json).")
    ap.add_argument("-o", "--output", type=Path, help="Write to this file instead of stdout.")
    ap.add_argument("-p", "--file-pattern", default=DEFAULT_FILE_PATTERN,
                    help="Regex selecting files by their project-relative path.")
    ap.add_argument("-i", "--imports", action="store_true", help="Include import commands.")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="Include source text, file and line numbers in JSON output.")
    ap.add_argument("--keep-self-refs", action="store_true",
                    help="Keep references from a declaration to itself.")
    ap.add_argument("-q", "--quiet", action="store_true", help="Suppress parser warnings.")
    ap.add_argument("--version", action="version", version=f"%(prog)s {__version__}")
    args = ap.parse_args(argv)

    logging.basicConfig(level=logging.ERROR if args.quiet else logging.WARNING,
                        format="%(levelname)s: %(message)s")
    root = args.project.resolve()
    if not root.is_dir():
        ap.error(f"not a directory: {args.project}")

    kwargs = {"file_pattern": args.file_pattern, "skip_self_refs": not args.keep_self_refs}
    deps = parse_commit(root, args.commit, **kwargs) if args.commit \
        else parse_dependencies(root, **kwargs)

    if args.format == "json":
        out = json.dumps(deps_to_dict(deps, root, verbose=args.verbose,
                                      include_imports=args.imports),
                         indent=2, ensure_ascii=False)
    else:
        out = deps_to_str(deps, root, include_imports=args.imports)

    if args.output:
        args.output.write_text(out + "\n", encoding="utf-8")
    else:
        try:
            sys.stdout.write(out + "\n")
            sys.stdout.flush()
        except BrokenPipeError:  # e.g. piped into `head`
            sys.stdout = None  # stop Python from flushing the closed pipe again at exit
    return 0


if __name__ == "__main__":
    sys.exit(main())
