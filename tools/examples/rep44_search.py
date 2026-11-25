"""Search for a small fan-in-two AND/OR circuit for a four-by-four bipartite graph.

Inputs 0 to 3 select one row, and inputs 4 to 7 select one column. Bit 4*r+c
of the graph mask is the requested output at (r,c). Run, for example,
python3 rep44_search.py 4459 8. A successful search prints an actual circuit.
On failure, --states FILE saves the surviving states grouped by gate budget.

To see why the pruning is exhaustive, trace the output of a circuit backwards.
Each gate replaces one needed wire value by at most two, so k remaining gates
can use at most k+1 values from the current pool. A positive and a negative
row must still have some wire high only on the positive row. Gates whose value
is already available or constant can be removed from a nonconstant computation.
The Lean proof for mask 4459 establishes these facts using the project's gates.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

FULL = (1 << 16) - 1
PINS = tuple(15 << (4 * i) for i in range(4)) + tuple(0x1111 << i for i in range(4))


def verify(target, budget, gates, output):
    values = list(PINS)
    assert len(gates) <= budget
    for op, sources in gates:
        assert op in ("and", "or") and len(sources) <= 2
        value = FULL if op == "and" else 0
        for wire in sources:
            assert 0 <= wire < len(values)
            value = value & values[wire] if op == "and" else value | values[wire]
        values.append(value)
    assert (values[output] if 0 <= output < len(values) else 0) == target


def search(target, budget, keep_states=False):
    if not 0 <= target <= FULL or budget < 0:
        raise ValueError("use a 16-bit graph mask and a nonnegative gate budget")
    result = {"mask": target, "gate_budget": budget}
    levels = defaultdict(list)

    def report(gates=None, output=None):
        result["circuit_found"] = gates is not None
        if gates is not None:
            verify(target, budget, gates, output)
            result.update(gates=gates, output=output)
        return result, levels

    if target == 0:
        return report([], 8)
    if target == FULL:
        return report([("and", [])], 8) if budget >= 1 else report()

    comparisons = [(p,n) for p in range(16) if target >> p & 1
                   for n in range(16) if not (target >> n & 1)]
    required = (1 << len(comparisons)) - 1

    @lru_cache(None)
    def distinguished(wire):
        return sum(1 << i for i,(p,n) in enumerate(comparisons)
                   if wire >> p & 1 and not (wire >> n & 1))

    def separates(state):
        mask = 0
        for wire in state:
            mask |= distinguished(wire)
        return mask == required

    @lru_cache(None)
    def finish(remaining, state):
        if keep_states:
            levels[remaining].append(state)
        if target in state:
            return ()
        if remaining == 0:
            return None
        pool = set(state)
        for a, b in combinations(state, 2):
            untouched = pool - {a,b}
            for op, c in (("or", a|b), ("and", a&b)):
                if c in pool or c in (0,FULL):
                    continue
                for kept in ((), (a,), (b,), (a,b)):
                    nxt = untouched.union(kept, (c,))
                    if len(nxt) > remaining or not separates(nxt):
                        continue
                    tail = finish(remaining-1, tuple(sorted(nxt)))
                    if tail is not None:
                        return ((op,a,b,c),) + tail
        return None

    for size in range(1, min(8, budget+1)+1):
        for root in combinations(sorted(PINS), size):
            if not separates(root):
                continue
            path = finish(budget, root)
            if path is None:
                continue
            wires = {mask:i for i,mask in enumerate(PINS)}
            gates = []
            for op, a, b, c in path:
                gates.append((op, [wires[a], wires[b]]))
                wires[c] = len(PINS) + len(gates) - 1
            result["states_visited"] = finish.cache_info().currsize
            return report(gates, wires[target])
    result["states_visited"] = finish.cache_info().currsize
    return report()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mask", type=lambda s: int(s, 0))
    parser.add_argument("budget", type=int)
    parser.add_argument("--states", type=Path)
    args = parser.parse_args()
    result, levels = search(args.mask, args.budget, args.states is not None)
    if args.states is not None:
        args.states.write_text(json.dumps(dict(sorted(levels.items()))) + "\n")
    print(json.dumps(result, indent=2))
