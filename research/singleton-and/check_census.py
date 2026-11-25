"""Independently check the exhaustive incidence census and its optimal clean circuits.

The lower-bound checker keeps layers of possible remaining wire sets. For each
minimal positive row, it intersects all high wires with the full set of negative
rows. A surviving negative row rules out every monotone continuation. The separate
upper-bound check transports an actual circuit to every labelled matrix in its
orbit and evaluates every gate on the full Boolean cube in parallel.
"""
import itertools
import json
import sys
from pathlib import Path


def permutations_of_graph(n, mask):
    for left in itertools.permutations(range(n)):
        for right in itertools.permutations(range(n)):
            for flip in (False, True):
                order = [n + left[i] if flip else left[i] for i in range(n)]
                order += [right[i] if flip else n + right[i] for i in range(n)]
                new = 0
                for i, j in itertools.product(range(n), repeat=2):
                    if mask & (1 << (n*i+j)):
                        p, q = sorted([order[i], order[n+j]])
                        new |= 1 << (n*p+q-n)
                yield new, order


def tables(n, graph):
    bits = 2*n
    length = 1 << bits
    full = (1 << length) - 1
    pins = tuple(sum(1 << r for r in range(length) if (r >> v) & 1) for v in range(bits))
    target = 0
    edges = []
    for i, j in itertools.product(range(n), repeat=2):
        if (graph >> (n*i+j)) & 1:
            target |= pins[i] & pins[n+j]
            edges.append(1 << ((1 << i) | (1 << (n+j))))
    return pins, target, full, edges


def check_lower(n, graph, budget):
    pins, target, full, edges = tables(n, graph)
    negatives = full ^ target

    def can_separate(wires):
        for edge in edges:
            candidates = negatives
            for wire in wires:
                if edge & wire:
                    candidates &= wire
                    if not candidates:
                        break
            if candidates:
                return False
        return True

    layer = set()
    for m in range(min(len(pins), budget+1)+1):
        for subset in itertools.combinations(pins, m):
            if can_separate(subset):
                layer.add(frozenset(subset))
    counts = []
    for remaining in range(budget, -1, -1):
        counts.append(len(layer))
        assert all(target not in state for state in layer), (graph, budget, "a smaller circuit exists")
        if not remaining or not layer:
            break
        new_layer = set()
        for state in layer:
            for a, b in itertools.combinations(state, 2):
                for value in (a | b, a & b):
                    if value in state or value in (0, full):
                        continue
                    candidate = state.union((value,))
                    for removed in ((a,b), (a,), (b,), ()):
                        if len(candidate) - len(removed) > remaining:
                            continue
                        after = candidate.difference(removed)
                        if after not in new_layer and can_separate(after):
                            new_layer.add(after)
        layer = new_layer
    return counts


def checked_witness(n, matrix, order, circuit):
    pins, answer, _, _ = tables(n, matrix)
    wires = [pins[i] for i in order]
    singleton_rows = sum(1 << (1 << v) for v in range(2*n))
    for op, a, b in circuit["gates"]:
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        if op == "and":
            value = wires[a] & wires[b]
            assert not (value & singleton_rows)
        else:
            assert op == "or"
            value = wires[a] | wires[b]
        wires.append(value)
    out = circuit["output"]
    assert out >= 0 and (wires[out] if out < len(wires) else 0) == answer


def has_four_cycle(n, graph):
    return any(all(graph & (1 << (n*u+v)) for u in left for v in right)
               for left in itertools.combinations(range(n),2) for right in itertools.combinations(range(n),2))


def check(records):
    if isinstance(records, dict):
        records = [records]
    for family in records:
        n = family["n"]
        labelled = set()
        for record in family["orbits"]:
            rep = record["mask"]
            cost = record["size"]
            assert record["clean_size"] == cost == len(record["clean_circuit"]["gates"])
            assert not has_four_cycle(n, rep)
            group = {}
            for mask, perm in permutations_of_graph(n, rep):
                group[mask] = perm
            assert len(group) == record["orbit"] and not labelled.intersection(group)
            for matrix, perm in group.items():
                checked_witness(n, matrix, perm, record["clean_circuit"])
            labelled.update(group)
            if cost:
                counts = check_lower(n, rep, cost-1)
                print(f"n={n} mask={rep} size={cost} lower_states={sum(counts)}", flush=True)
            else:
                assert rep == 0
        expected = {mask for mask in range(1 << (n*n)) if not has_four_cycle(n,mask)}
        assert labelled == expected
        print(f"Verified {len(labelled)} labelled {n}-by-{n} graphs.", flush=True)


if __name__ == "__main__":
    check(json.loads(Path(sys.argv[1]).read_text()))
