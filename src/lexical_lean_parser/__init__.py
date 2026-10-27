"""A fast, dependency-free lexical parser for Lean 4 declarations and their dependencies.

The parser reads Lean source text with regular expressions - it does not elaborate it - so
it needs no Lean toolchain and no build, and runs in seconds on large projects.
"""

from importlib.metadata import PackageNotFoundError, version

from lexical_lean_parser.export import deps_to_dict, deps_to_str
from lexical_lean_parser.git import build_graph_at_commit, checkout, parse_commit
from lexical_lean_parser.graph import build_dependency_graph, draw_dependency_graph, node_key
from lexical_lean_parser.model import Comment, Declaration, DepMap, Identifier, Import, Notation
from lexical_lean_parser.parser import (
    DEFAULT_FILE_PATTERN,
    ParsedFile,
    find_lean_files,
    parse_dependencies,
    parse_file,
    parse_text,
)

try:
    __version__ = version("lexical-lean-parser")
except PackageNotFoundError:  # running from a source tree that is not installed
    __version__ = "0.0.0"

__all__ = [
    "DEFAULT_FILE_PATTERN",
    "Comment",
    "Declaration",
    "DepMap",
    "Identifier",
    "Import",
    "Notation",
    "ParsedFile",
    "__version__",
    "build_dependency_graph",
    "build_graph_at_commit",
    "checkout",
    "deps_to_dict",
    "deps_to_str",
    "draw_dependency_graph",
    "find_lean_files",
    "node_key",
    "parse_commit",
    "parse_dependencies",
    "parse_file",
    "parse_text",
]
