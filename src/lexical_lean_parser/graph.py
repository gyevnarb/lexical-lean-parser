"""Build and draw dependency graphs with networkx (install the `graph` extra)."""

from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING

from lexical_lean_parser.model import Comment, Declaration, DepMap, Identifier, Import

if TYPE_CHECKING:
    import networkx as nx

NodeKey = tuple[str, str, "str | None", str]
"""A graph node: (kind, module, namespace, name)."""


def _networkx():
    try:
        import networkx as nx  # noqa: PLC0415
    except ImportError as e:
        msg = "Graph support needs networkx: pip install 'lexical-lean-parser[graph]'"
        raise ImportError(msg) from e
    return nx


def node_key(obj: Declaration | Import, working_dir: Path) -> NodeKey:
    """The graph node for a declaration or import."""
    module = obj.file.relative_to(working_dir).with_suffix("").as_posix().replace("/", ".")
    return (obj.kind, module, obj.namespace, obj.name)


def build_dependency_graph(
    dependencies: DepMap,
    working_dir: Path,
    include_imports: bool = True,
    cross_file_only: bool = True,
    remove_unconnected: bool = False,
) -> nx.DiGraph:
    """Build a directed graph with an edge from each declaration to each of its dependencies.

    Nodes are keyed by `node_key` and carry the attributes `name`, `file` (relative to
    `working_dir`), `kind`, `n_todos` and `payload` (the parsed object). Edges carry
    `weight` (how often the target's name occurs in the body), and `from_def`/`from_body`
    (whether the reference occurs in the signature and/or the body).

    Args:
        dependencies: The output of `parse_dependencies`.
        working_dir: The directory the parse was run on.
        include_imports: Add a node for each import.
        cross_file_only: Keep only edges between different files.
        remove_unconnected: Drop nodes without any edges.

    """
    nx = _networkx()
    working_dir = Path(working_dir).resolve()
    G = nx.DiGraph()

    def included(obj: Identifier) -> bool:
        return not isinstance(obj, Comment) and (include_imports or not isinstance(obj, Import))

    for obj in (o for items in dependencies.values() for o in items if included(o)):
        key = node_key(obj, working_dir)
        if key not in G:
            G.add_node(key, name=obj.name, file=obj.file.relative_to(working_dir),
                       kind=obj.kind, n_todos=getattr(obj, "n_todos", 0), payload=obj)

    for obj in (o for items in dependencies.values() for o in items):
        if not isinstance(obj, Declaration):
            continue
        src = node_key(obj, working_dir)
        from_def = {node_key(t, working_dir) for t in obj.depends_on_def}
        from_body = {node_key(t, working_dir) for t in obj.depends_on_body}
        seen = set()
        for target in obj.depends_on:
            dst = node_key(target, working_dir)
            if (cross_file_only and src[1] == dst[1]) or dst in seen or dst not in G:
                continue
            seen.add(dst)
            # Escaped: a `.` in a declaration name would otherwise match any character.
            weight = len(re.findall(re.escape(target.name), obj.body))
            G.add_edge(src, dst, weight=weight, from_def=dst in from_def,
                       from_body=dst in from_body)

    if remove_unconnected:
        G.remove_nodes_from([n for n in G.nodes() if G.degree(n) == 0])
    return G


_NODE_STYLES = {
    "theorem": {"shape": "ellipse", "fillcolor": "#D1FFB9"},
    "lemma": {"shape": "box", "fillcolor": "#D1E7FF"},
}
_DEFAULT_NODE_STYLE = {"shape": "box", "fillcolor": "#F0F0F0"}


def draw_dependency_graph(
    G: nx.DiGraph,
    out_dir: Path = Path(),
    *,
    name: str = "dependency_graph",
    rankdir: str = "LR",
    cluster_by_file: bool = True,
    node_fontsize: int = 10,
    file_fontsize: int = 12,
    dpi: int = 140,
) -> tuple[Path, Path | None]:
    """Write a graph as Graphviz DOT and, if Graphviz can render it, as PDF.

    Needs the `draw` extra (pygraphviz, which in turn needs Graphviz installed).

    Returns:
        The path of the DOT file, and of the PDF or None if rendering failed.

    """
    try:
        from networkx.drawing.nx_agraph import to_agraph  # noqa: PLC0415
    except ImportError as e:
        msg = "Drawing needs pygraphviz: pip install 'lexical-lean-parser[draw]'"
        raise ImportError(msg) from e

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    A = to_agraph(G)
    A.graph_attr.update(rankdir=rankdir, splines="spline", overlap="false", concentrate="true",
                        bgcolor="white", dpi=str(dpi), fontname="Helvetica")
    A.node_attr.update(fontname="Helvetica", fontsize=str(node_fontsize), style="filled",
                       color="#D3D3D3", fillcolor="white", shape="box")
    A.edge_attr.update(arrowsize="0.7", color="#666666")

    for n, data in G.nodes(data=True):
        node = A.get_node(str(n))
        node.attr["label"] = data["name"]
        node.attr.update(_NODE_STYLES.get(data["kind"], _DEFAULT_NODE_STYLE))

    if cluster_by_file:
        by_file: dict[str, list[str]] = {}
        for n, data in G.nodes(data=True):
            by_file.setdefault(str(data["file"]), []).append(str(n))
        for i, (fname, nodes) in enumerate(sorted(by_file.items())):
            # The `cluster_` prefix is what makes Graphviz draw a box around the subgraph.
            sub = A.add_subgraph(nodes, name=f"cluster_{i}_{fname}", label=fname)
            sub.graph_attr.update(style="rounded,filled", color="#DDDDDD", fillcolor="#FAFAFA",
                                  fontname="Helvetica", fontsize=str(file_fontsize))

    dot_path = out_dir / f"{name}.dot"
    A.write(dot_path)
    pdf_path: Path | None = out_dir / f"{name}.pdf"
    try:
        A.draw(pdf_path, prog="dot")
    except Exception:  # noqa: BLE001 - rendering is best-effort; the DOT file is the result
        pdf_path = None
    return dot_path, pdf_path
