"""Compare optimal monotone circuits with optimum circuits whose AND gates reject every singleton."""
import argparse
from functools import lru_cache
from itertools import combinations, permutations
import json
from pathlib import Path


def is_c4_free(graph, n):
    rows = [(graph >> (n * i)) & ((1 << n) - 1) for i in range(n)]
    return all((a & b).bit_count() <= 1 for a, b in combinations(rows, 2))


def relabel(graph, left, right, transpose):
    n = len(left)
    output = 0
    for u in range(n):
        for v in range(n):
            if graph >> (n * u + v) & 1:
                i, j = (right[v], left[u]) if transpose else (left[u], right[v])
                output |= 1 << (n * i + j)
    return output


def orbits(n):
    seen = set()
    for graph in range(1 << (n * n)):
        if graph in seen or not is_c4_free(graph, n):
            continue
        orbit = {relabel(graph, left, right, flip)
                 for left in permutations(range(n)) for right in permutations(range(n)) for flip in (False, True)}
        assert min(orbit) == graph
        seen.update(orbit)
        yield graph, len(orbit)


def problem(graph, n):
    rows = list(range(1 << (2 * n)))
    full = (1 << len(rows)) - 1
    pins = [sum(1 << r for r in rows if r >> i & 1) for i in range(2 * n)]
    edges = [(1 << u) | (1 << (n + v)) for u in range(n) for v in range(n) if graph >> (n*u+v) & 1]
    on = {r for r in rows if any(e & r == e for e in edges)}
    target = sum(1 << r for r in on)
    off = set(rows) - on
    max_off = [r for r in off if all((r | (1 << i)) in on for i in range(2*n) if not (r >> i & 1))]
    required = [(p, q) for p in edges for q in max_off]
    singletons = sum(1 << (1 << i) for i in range(2 * n))
    return pins, target, full, required, singletons


def verify(graph, n, circuit, clean):
    pins, target, _, _, singletons = problem(graph, n)
    values = pins.copy()
    for op, a, b in circuit["gates"]:
        assert op in ("and", "or") and 0 <= a < len(values) and 0 <= b < len(values)
        value = values[a] & values[b] if op == "and" else values[a] | values[b]
        assert not clean or op != "and" or not (value & singletons)
        values.append(value)
    out = circuit["output"]
    assert (values[out] if out < len(values) else 0) == target


def compare(graph, n):
    pins, target, full, pairs, singletons = problem(graph, n)
    if not target:
        return {"size": 0, "clean_size": 0, "clean_circuit": {"gates": [], "output": len(pins)}}
    required = (1 << len(pairs)) - 1

    @lru_cache(None)
    def differences(w):
        return sum(1 << i for i, (p, q) in enumerate(pairs) if w >> p & 1 and not (w >> q & 1))

    def separates(state):
        covered = 0
        for w in state:
            covered |= differences(w)
        return covered == required

    def search(budget, clean):
        @lru_cache(None)
        def finish(k, state):
            if target in state:
                return ()
            if not k:
                return None
            source = set(state)
            for a, b in combinations(state, 2):
                rest = source - {a, b}
                for op, c in (("and", a & b), ("or", a | b)):
                    if c in source or c in (0, full) or (clean and op == "and" and c & singletons):
                        continue
                    for keep in ((), (a,), (b,), (a, b)):
                        after = rest.union(keep, (c,))
                        if len(after) <= k and separates(after):
                            tail = finish(k - 1, tuple(sorted(after)))
                            if tail is not None:
                                return ((op, a, b, c),) + tail
            return None

        for m in range(1, min(len(pins), budget + 1) + 1):
            for state in combinations(sorted(pins), m):
                if not separates(state):
                    continue
                path = finish(budget, state)
                if path is None:
                    continue
                wires = {v: i for i, v in enumerate(pins)}
                gates = []
                for op, a, b, c in path:
                    gates.append([op, wires[a], wires[b]])
                    wires[c] = len(pins) + len(gates) - 1
                ans = {"gates": gates, "output": wires[target]}
                verify(graph, n, ans, clean)
                return ans, finish.cache_info().currsize
        return None, finish.cache_info().currsize

    positives = graph.bit_count()
    active_rows = sum(bool((graph >> (n*i)) & ((1 << n)-1)) for i in range(n))
    active_cols = sum(any(graph >> (n*i+j) & 1 for i in range(n)) for j in range(n))
    cap = positives + min(active_rows, active_cols) - 1
    attempts = []
    for budget in range(active_rows + active_cols - 1, cap+1):
        standard, states = search(budget, False)
        attempts.append([budget, states, bool(standard)])
        if standard is not None:
            for clean_budget in range(budget, cap+1):
                clean, _ = search(clean_budget, True)
                if clean is not None:
                    return {"size": budget, "clean_size": clean_budget, "clean_circuit": clean, "lower_search": attempts}
    raise AssertionError("the explicit star construction exceeds its own bound")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, choices=(1, 2, 3, 4))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    records = []
    for graph, multiplicity in orbits(args.n):
        record = {"mask": graph, "orbit": multiplicity, **compare(graph, args.n)}
        records.append(record)
        print(graph, multiplicity, record["size"], record["clean_size"], flush=True)
    args.output.write_text(json.dumps({"n": args.n, "orbits": records}, indent=2) + "\n")
