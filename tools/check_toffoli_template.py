"""Check the Python Toffoli template against Lean's proved typed sequence.

This is a strict source-shape and record-template comparison, not a Lean proof of
Python execution or of the complete compiler pipeline.
"""
import ast
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def python_template():
    tree = ast.parse((ROOT / 'src/check_acceptance_estimator.py').read_text(encoding='utf-8'))
    matches = [node for node in tree.body if isinstance(node, ast.FunctionDef)
               and node.name == 'toffoli_decomposition']
    assert len(matches) == 1
    fn = matches[0]
    assert [a.arg for a in fn.args.args] == ['a', 'b', 't']
    assert not (fn.args.posonlyargs or fn.args.kwonlyargs or fn.args.vararg or fn.args.kwarg
                or fn.args.defaults or fn.decorator_list)
    assert len(fn.body) == 1 and isinstance(fn.body[0], ast.Return)
    body = fn.body[0].value
    assert isinstance(body, ast.List)
    out = []
    for record in body.elts:
        assert isinstance(record, ast.Tuple) and len(record.elts) in (2, 3)
        tag, *wires = record.elts
        assert isinstance(tag, ast.Constant) and isinstance(tag.value, str)
        assert all(isinstance(w, ast.Name) and w.id in ('a', 'b', 't') for w in wires)
        out.append((tag.value, tuple(('a', 'b', 't').index(w.id) for w in wires)))
    return out


def lean_template():
    source = (ROOT / 'lean/SectorSimulation/ThreeWireProgram.lean').read_text(encoding='utf-8')
    match = re.search(r'def threeWireToffoli : List ThreeWireGate :=\s*\[(.*?)\]', source, re.S)
    assert match, 'Lean typed Toffoli definition not found'
    parts = [part.strip() for part in match.group(1).split(',')]
    out = []
    for part in parts:
        item = re.fullmatch(r'\.(hadamard|x|z|t|cnot) ([0-2])(?: (true|false|[0-2]))?', part)
        assert item, f'Unexpected Lean gate syntax: {part}'
        kind, first, second = item.groups()
        if kind == 'cnot':
            assert second in ('0', '1', '2')
            out.append(('CX', (int(first), int(second))))
        elif kind == 't':
            assert second in ('true', 'false')
            out.append(('TDG' if second == 'true' else 'T', (int(first),)))
        else:
            assert second is None
            out.append(({'hadamard': 'H', 'x': 'X', 'z': 'Z'}[kind], (int(first),)))
    return out


def main():
    python, lean = python_template(), lean_template()
    assert python == lean, f'Toffoli templates differ: Python {python!r}; Lean {lean!r}'
    assert len(lean) == 15
    print(json.dumps({'status': 'pass', 'records': len(lean),
                      'scope': 'Strict parametric Python source template equals the Lean typed Toffoli list; not Python execution semantics.'}))


if __name__ == '__main__':
    main()
