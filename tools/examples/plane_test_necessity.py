"""Construct a 40-gate counterexample to every one-row deletion from the weight-nine test.

Run with Python 3. Each returned gate lists its operation and the two earlier wires it reads.
Wires 0 through 12 are the inputs. Lines are indexed by the cyclic difference set {0,1,3,9}.
"""
from collections import Counter
from itertools import combinations
import argparse
import json

LINES = tuple(frozenset((w + a) % 13 for a in (0, 1, 3, 9)) for w in range(13))


def construct(zeros):
    """The output for one line is its usual OR conjoined with OR(zeros)."""
    gates = []
    output = [None] * 13

    def gate(op, a, b):
        assert a != b and 0 <= min(a, b) and max(a, b) < 13 + len(gates)
        gates.append((op, a, b))
        return 12 + len(gates)

    def any_of(points):
        first, *rest = sorted(points)
        for p in rest:
            first = gate("or", first, p)
        return first

    if zeros in LINES:
        donor = LINES.index(zeros)
        target = (donor + 1) % 13
        output = [any_of(line) for line in LINES]
        output[target] = gate("and", output[target], output[donor])
        return gates, output, target

    target = max(range(13), key=lambda w: len(LINES[w] & zeros))
    common = zeros & LINES[target]
    extra = zeros - common
    assert 2 <= len(common) <= 3
    donor = next(w for w, line in enumerate(LINES) if extra <= line and w != target)
    extra_wire = any_of(extra)
    output[donor] = gate("or", extra_wire, any_of(LINES[donor] - extra))
    for w, line in enumerate(LINES):
        if w not in (target, donor):
            output[w] = any_of(line)
    inside = any_of(common)
    outside = any_of(LINES[target] - common)
    output[target] = gate("or", inside, gate("and", outside, extra_wire))
    return gates, output, target


def bitmask(points):
    return sum(1 << i for i in points)


def checked():
    full = (1 << 13) - 1
    rows = [s for s in range(full + 1) if s.bit_count() >= 9]
    index = {row: i for i, row in enumerate(rows)}
    pins = [sum(1 << i for i, row in enumerate(rows) if row & (1 << v)) for v in range(13)]
    line_values = [sum(1 << i for i, row in enumerate(rows) if row & bitmask(line)) for line in LINES]
    types = Counter()
    for h in combinations(range(13), 4):
        zeros = frozenset(h)
        gates, outputs, target = construct(zeros)
        assert Counter(op for op, _, _ in gates) == {"or": 39, "and": 1}
        values = pins.copy()
        for op, a, b in gates:
            values.append(values[a] | values[b] if op == "or" else values[a] & values[b])
        missing = index[full ^ bitmask(zeros)]
        for w, out in enumerate(outputs):
            assert values[out] ^ line_values[w] == ((1 << missing) if w == target else 0)
        assert line_values[target] & (1 << missing)
        types[max(len(line & zeros) for line in LINES)] += 1
    return {"omitted_weight_nine_rows": sum(types.values()), "heavy_inputs_per_circuit": len(rows),
            "outputs_per_circuit": len(LINES), "or_gates": 39, "and_gates": 1,
            "four_point_sets_by_maximum_collinearity": dict(sorted(types.items()))}



def canonical_patterns():
    """Return one packed circuit per orbit under cyclic relabelling of the points."""
    patterns = []
    for subset in combinations(range(13), 4):
        zeros = frozenset(subset)
        mask = bitmask(zeros)
        if any(bitmask({(i + t) % 13 for i in zeros}) < mask for t in range(1, 13)):
            continue
        gates, outputs, target = construct(zeros)
        program = 0
        for index, (op, left, right) in enumerate(gates):
            digit = left + (right << 6) + ((op == "and") << 12)
            program |= digit << (13 * index)
        outputs_word = sum(wire << (6 * i) for i, wire in enumerate(outputs))
        patterns.append((mask, target, program, outputs_word))
    return sorted(patterns)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--patterns", action="store_true", help="emit the 55 Lean circuit definitions")
    if parser.parse_args().patterns:
        for i, (mask, target, program, outputs) in enumerate(canonical_patterns()):
            print(f"def pattern{i} : Packed := ⟨{mask}, {target}, {program}, {outputs}⟩")
    else:
        print(json.dumps(checked(), indent=2))
