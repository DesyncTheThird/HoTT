#!/usr/bin/env -S uv run --script
# /// script
# dependencies = ["pydot"]
# ///

import re
import sys
from graphlib import TopologicalSorter
from pathlib import Path

import pydot

COMMENT = re.compile(r'(?s:\{-.*?-\})|--.*')
SORRY = re.compile(r'\bsorry\b(?!\s*:)')

COLOUR = {'sorry': '"#f4a3a3"', 'tainted': '"#fde8c8"', 'clean': '"#e3f1e3"'}


def has_sorry(module):
    src = Path(module.replace('.', '/') + '.agda').read_text()
    return bool(SORRY.search(COMMENT.sub('', src)))


def main():
    src, dst = sys.argv[1:3]
    (graph,) = pydot.graph_from_dot_file(src)
    nodes = {n.get_name(): n for n in graph.get_nodes()}
    imports = {n: set() for n in nodes}
    for e in graph.get_edges():
        imports[e.get_source()].add(e.get_destination())

    status = {}
    for n in TopologicalSorter(imports).static_order():
        if has_sorry(nodes[n].get('label').strip('"')):
            status[n] = 'sorry'
        elif any(status[m] != 'clean' for m in imports[n]):
            status[n] = 'tainted'
        else:
            status[n] = 'clean'

    for n, node in nodes.items():
        node.set('style', 'filled')
        node.set('fillcolor', COLOUR[status[n]])
        node.set('URL', '"' + node.get('label').strip('"') + '.html"')
    graph.write_raw(dst)

    counts = {s: list(status.values()).count(s) for s in COLOUR}
    print(f'{len(nodes)} modules, {counts["sorry"]} with sorry, {counts["tainted"]} depending on sorry')


if __name__ == '__main__':
    main()
