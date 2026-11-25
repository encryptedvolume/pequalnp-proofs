"""Enumerate all least circuits for the four-vertex path after ordering each commutative pair."""
from itertools import combinations_with_replacement
from collections import Counter
import json


def classify():
    inputs = tuple(sum(1 << r for r in range(16) if r >> i & 1) for i in range(4))
    a, b, x, y = inputs
    target = (a & x) | (a & y) | (b & x)
    counts = Counter()

    def top_stuck(gates, values):
        readers = [{j for j, (_, a, b) in enumerate(gates) if a == w or b == w} for w in range(8)]
        for subset in range(16):
            top = {j for j in range(4) if subset >> j & 1}
            if any(gates[j][0] or (j != 3 and not any(readers[4+j] == {k} for k in top)) for j in top):
                continue
            if all(value & ~target or not any(not gates[j][0] for j in readers[w])
                   or readers[w] <= top for w, value in enumerate(values)):
                return True
        return False

    def extend(values, left, right, valid, gates, depth):
        for i, j in combinations_with_replacement(range(len(values)), 2):
            for meet in (False, True):
                out = values[i] & values[j] if meet else values[i] | values[j]
                good = valid and (not meet or (left[i] and right[j]) or (left[j] and right[i]))
                if depth == 4:
                    counts["gate_lists"] += 1
                    if out == target:
                        counts["computes_path"] += 1
                        counts["two_level" if good else "violates_two_level"] += 1
                        stuck = top_stuck(gates + ((meet, i, j),), values + (out,))
                        counts["top_stuck" if stuck else "not_top_stuck"] += 1
                        if stuck and not good:
                            counts["counterexamples"] += 1
                else:
                    extend(values + (out,), left + (not meet and left[i] and left[j],),
                           right + (not meet and right[i] and right[j],), good, gates + ((meet, i, j),), depth + 1)

    # Left and right membership is forced on the primary inputs. An OR belongs to
    # a side exactly when both operands can belong to that side. An AND belongs
    # to neither. This constructs the largest two candidate sets for the definition.
    extend(inputs, (True, True, False, False), (False, False, True, True), True, (), 1)
    return {**counts, "counterexamples": counts["counterexamples"]}


if __name__ == "__main__":
    print(json.dumps(classify(), indent=2))
