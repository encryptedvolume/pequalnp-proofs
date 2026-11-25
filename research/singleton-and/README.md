# AND gates on singleton inputs

For each four-cycle-free bipartite graph with one through four vertices per side, the edge function has a minimum-size monotone fan-in-two circuit in which every AND gate outputs false when just one vertex input is true. The input to the edge function is any subset of vertices. An output of true means that the subset contains both endpoints of an edge.

| Vertices per side | Labelled graphs | Classes under relabelling and side exchange | Largest minimum gate count |
| ---: | ---: | ---: | ---: |
| 1 | 2 | 2 | 1 |
| 2 | 15 | 5 | 4 |
| 3 | 334 | 16 | 8 |
| 4 | 18,521 | 59 | 12 |

The six-cycle needs eight gates. Its exact lower bound and a minimum circuit satisfying the singleton condition are proved in Lean using the project's circuit definitions. [Six-cycle proof](../../lean/PEqualNP/Examples/CycleSingletonAND.lean)

## Reproduce the census

From this directory, run the following commands with Python 3.10 or newer.

```sh
python3 check_census.py census.json
python3 search_census.py 4 four.json
python3 check_census.py four.json
```

Each record gives a graph mask, the number of its distinct labellings, the optimum size and a circuit attaining it. Bit `n*u+v` denotes the edge from left vertex `u` to right vertex `v`. Wires `0` through `2*n-1` are the input vertices in left-then-right order. Each gate appends one new wire. For the empty graph, the project permits an out-of-range output wire, which evaluates to false.

The verifier checks the upper bound by relabelling each supplied circuit to every labelled matrix in its class, evaluating every gate on the entire Boolean cube, and inspecting every AND gate at every singleton. It independently enumerates all four-cycle-free matrices to check coverage.

For the lower bound, trace the output wire of any circuit backwards. Each gate replaces one needed wire value by at most two, so a circuit with `k` remaining gates can need at most `k+1` distinct current values. For a nonconstant target, a constant gate or a gate equal to an already available value can be removed from this trace. For each positive input and negative input, some needed wire must be true on the positive input and false on the negative input. AND and OR preserve coordinatewise order.

The search tests this condition at minimal positive and maximal negative inputs and explores successor states recursively. The verifier enumerates layers from every feasible input subset, intersects wire values at each minimal positive input, and compares against every negative input. It rules out the budget one below each listed optimum. The finite census uses these executable checks. The unrestricted statement for arbitrary side sizes remains open.

## Minimality on the four-vertex path

The path has a four-gate optimum. Its three prime clauses give a five-gate circuit computing the same edge function. Lean proves that the five-gate circuit satisfies the project's top-stuck condition and fails its two-level condition. The latter requires each AND to combine a left-only OR wire with a right-only OR wire. [Path proof](../../lean/PEqualNP/Examples/PathFourTopForm.lean)

`python3 optimal_path_shapes.py` checks every four-gate circuit on the four path vertices with each commutative pair of operands placed in ascending order. Repeated operands are included. A minimum circuit must output the last gate, since an earlier output would give a circuit with at most three gates. Of the 1,411,200 gate lists, 12 compute the path. Exactly six satisfy the top-stuck condition, and all six are two-level. The script checks all 16 possible top sets for each circuit computing the path.
