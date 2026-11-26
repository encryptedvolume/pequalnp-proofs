"""Reproduce the six- and seven-vertex partial-function AND-count census.

The 156 isomorphism classes at order six have equal minimum AND-count and
biclique-cover number. At order seven, 12 of the 1,044 classes save one AND.
They account for 26,862 labelled graphs. Eleven use three ANDs against a
four-biclique minimum. One uses four ANDs against a five-biclique minimum.
Each of the twelve contains an induced diamond (four vertices with five edges).

A false test input is a maximal independent vertex set. Each one-vertex
extension of such a set is a true test input. Each paid gate is the AND
of two freely chosen ORs of vertices and earlier gates. The output is also
a free OR. The graph mask and each biclique mask index the lexicographically
ordered unordered vertex pairs, starting at bit zero. A circuit witness
numbers input vertices first and gate outputs in evaluation order.

graphs.json records a minimum cover for every graph class. A smaller circuit
is included whenever one exists. refutations.json.gz contains one proof per
nonempty graph for circuits with one fewer AND than its recorded minimum.
Unused gates may be appended, so that refutation also excludes smaller sizes.

Generate with Python 3.11+, python-sat 1.9.dev24, and drat-trim on PATH.
Verification uses the Python standard library and drat-trim.
    python census.py generate
    python census.py verify

The verifier rebuilds each SAT formula, checks its stored DRAT certificate,
simulates the upper-bound circuit, and checks the biclique covers directly.
"""
import argparse
import gzip
import hashlib
import itertools
import json
import math
import subprocess
import tempfile
from functools import lru_cache, reduce
from operator import or_
from pathlib import Path

HERE = Path(__file__).resolve().parent


def union(parts):
    return reduce(or_, parts, 0)


class Graphs:
    def __init__(self, order):
        self.n = order
        self.full = (1 << order) - 1
        self.edges = list(itertools.combinations(range(order), 2))
        self.edge_ends = [(1 << a) | (1 << b) for a, b in self.edges]
        self.permutations = [
            [self.edges.index(tuple(sorted((p[a], p[b])))) for a, b in self.edges]
            for p in itertools.permutations(range(order))
        ]
        self.bicliques = self.all_bicliques()

    def representatives(self):
        seen = bytearray(1 << len(self.edges))
        for graph, visited in enumerate(seen):
            if visited:
                continue
            indices = [i for i in range(len(self.edges)) if graph & (1 << i)]
            orbit = {sum(1 << p[i] for i in indices) for p in self.permutations}
            assert min(orbit) == graph and not any(seen[g] for g in orbit)
            for g in orbit:
                seen[g] = 1
            yield graph, len(orbit)
        assert all(seen)

    def all_bicliques(self):
        result = {}
        for left in range(1, self.full + 1):
            for right in range(left + 1, self.full + 1):
                if left & right:
                    continue
                mask = sum(1 << i for i, e in enumerate(self.edge_ends)
                           if e & left and e & right)
                result[mask] = (left, right)
        return result

    def maximal_bicliques(self, graph):
        valid = [m for m in self.bicliques if m & graph == m]
        maximal = []
        for m in sorted(valid, key=lambda x: (-x.bit_count(), x)):
            if not any(m & w == m for w in maximal):
                maximal.append(m)
        return maximal

    def induced_diamond(self, graph):
        for vertices in itertools.combinations(range(self.n), 4):
            pairs = itertools.combinations(vertices, 2)
            if sum(bool(graph & (1 << self.edges.index(edge))) for edge in pairs) == 5:
                return True
        return False

    def observations(self, graph):
        edges = [e for i, e in enumerate(self.edge_ends) if graph & (1 << i)]
        independent = {u for u in range(self.full + 1) if all(u & e != e for e in edges)}
        neg = {u for u in independent
               if all((u & (1 << i)) or (u | (1 << i)) not in independent for i in range(self.n))}
        pos = {u | (1 << i) for u in neg for i in range(self.n) if not u & (1 << i)}
        assert neg.isdisjoint(pos)
        return [(u, False) for u in sorted(neg)] + [(u, True) for u in sorted(pos)]


def minimum_cover(graph, maximal):
    by_edge = {bit: [m for m in maximal if m & (1 << bit)]
               for bit in range(graph.bit_length()) if graph & (1 << bit)}

    @lru_cache(None)
    def cover(left):
        if left == 0:
            return ()
        options = min((c for bit, c in by_edge.items() if left & (1 << bit)), key=len)
        return min(((m,) + cover(left & ~m) for m in options), key=len)

    return list(cover(graph))


def verify_cover(graph, maximal, witness):
    assert all(m in maximal for m in witness) and union(witness) == graph
    if not witness:
        assert graph == 0
        return
    # Every biclique extends to a maximal one. A smaller cover could be padded.
    for selection in itertools.combinations(maximal, len(witness) - 1):
        assert union(selection) != graph


class CNF:
    def __init__(self):
        self.count = 0
        self.clauses = []

    def var(self):
        self.count += 1
        return self.count

    def both(self, a, b):
        y = self.var()
        self.clauses.extend([[-y, a], [-y, b], [y, -a, -b]])
        return y

    def some(self, terms):
        y = self.var()
        self.clauses.append([-y, *terms])
        self.clauses.extend([[-v, y] for v in terms])
        return y

    def dimacs(self):
        header = f'p cnf {self.count} {len(self.clauses)}\n'
        body = ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in self.clauses)
        return (header + body).encode('ascii')


def encode(n, size, obs):
    f = CNF()
    sides = [[[f.var() for _ in range(n + i)] for _ in range(2)] for i in range(size)]
    output = [f.var() for _ in range(n + size)]
    for u, positive in obs:
        values = []

        def evaluate_side(select):
            terms = [select[i] for i in range(n) if u & (1 << i)]
            terms.extend(f.both(sel, val) for sel, val in zip(select[n:], values))
            return f.some(terms)

        for left, right in sides:
            lhs = evaluate_side(left)
            rhs = evaluate_side(right)
            values.append(f.both(lhs, rhs))
        value = evaluate_side(output)
        f.clauses.append([value if positive else -value])
    return f, sides, output


def simulate(n, gates, output, u):
    values = [bool(u & (1 << i)) for i in range(n)]
    for left, right in gates:
        assert all(0 <= i < len(values) for i in left + right)
        values.append(any(values[i] for i in left) and any(values[i] for i in right))
    assert all(0 <= i < len(values) for i in output)
    return any(values[i] for i in output)


def cover_circuit(data, cover):
    def vertices(mask):
        return [i for i in range(data.n) if mask & (1 << i)]
    gates = [[vertices(s) for s in data.bicliques[m]] for m in cover]
    return gates, list(range(data.n, data.n + len(gates)))


def check_upper(n, gates, output, obs):
    assert all(simulate(n, gates, output, u) == goal for u, goal in obs)


def verified_drat(drat, folder, cnf, proof):
    cnf_path = folder / 'instance.cnf'
    proof_path = folder / 'refutation.drat'
    cnf_path.write_bytes(cnf)
    proof_path.write_bytes(proof)
    check = subprocess.run([drat, str(cnf_path), str(proof_path)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert check.returncode == 0 and b's VERIFIED' in check.stdout, check.stdout[-700:]


def find_optimum(data, g, cover, obs, drat, folder):
    from pysat.solvers import Solver
    gates, output = cover_circuit(data, cover)
    for size in reversed(range(len(cover))):
        formula, sides, out = encode(data.n, size, obs)
        with Solver(name='cadical195', bootstrap_with=formula.clauses) as solver:
            sat = solver.solve()
            if sat:
                model = set(solver.get_model())
                def selected(bits):
                    return [i for i, var in enumerate(bits) if var in model]
                gates = [[selected(a), selected(b)] for a, b in sides]
                output = selected(out)
                check_upper(data.n, gates, output, obs)
                continue
        # Replay an independently produced proof with a separate proof checker.
        with Solver(name='glucose4', bootstrap_with=formula.clauses, with_proof=True) as solver:
            assert solver.solve() is False
            proof = ('\n'.join(solver.get_proof()) + '\n').encode('ascii')
        binary = formula.dimacs()
        verified_drat(drat, folder, binary, proof)
        return gates, output, (hashlib.sha256(binary).hexdigest(), proof.decode('ascii'))
    assert not gates
    return gates, output, None


def census(mode, drat):
    generating = mode == 'generate'
    rows_path = HERE / 'graphs.json'
    proofs_path = HERE / 'refutations.json.gz'
    if generating:
        rows, proofs = [], {}
    else:
        rows = json.loads(rows_path.read_text())
        proofs = json.loads(gzip.decompress(proofs_path.read_bytes()))
    total = 0
    seen_keys = set()
    with tempfile.TemporaryDirectory() as scratch:
        for n, class_count in [(6, 156), (7, 1044)]:
            data = Graphs(n)
            count = labelled = improvements = improved_labels = diamond_free = 0
            for g, orbit in data.representatives():
                key = f'{n}-{g}'
                maximal = data.maximal_bicliques(g)
                obs = data.observations(g)
                if generating:
                    cover = minimum_cover(g, maximal)
                    gates, out, cert = find_optimum(data, g, cover, obs, drat, Path(scratch))
                    row = {'n': n, 'mask': g, 'labellings': orbit, 'cover': cover,
                           'andCount': len(gates)}
                    if len(gates) < len(cover):
                        row.update(gates=gates, output=out)
                    if cert:
                        proofs[key] = cert
                    rows.append(row)
                else:
                    row = rows[total]
                    assert (row['n'], row['mask'], row['labellings']) == (n, g, orbit)
                    cover = row['cover']
                    gates, out = ((row['gates'], row['output']) if 'gates' in row
                                  else cover_circuit(data, cover))
                    if row['andCount'] > 0:
                        sha, proof = proofs[key]
                        binary = encode(n, row['andCount'] - 1, obs)[0].dimacs()
                        assert hashlib.sha256(binary).hexdigest() == sha
                        verified_drat(drat, Path(scratch), binary, proof.encode('ascii'))
                verify_cover(g, maximal, cover)
                check_upper(n, gates, out, obs)
                assert 0 <= row['andCount'] == len(gates) <= len(cover)
                if gates:
                    seen_keys.add(key)
                has_diamond = data.induced_diamond(g)
                diamond_free += int(not has_diamond)
                if len(gates) < len(cover):
                    assert has_diamond
                    improvements += 1
                    improved_labels += orbit
                count += 1
                labelled += orbit
                total += 1
            assert count == class_count and labelled == (1 << math.comb(n, 2))
            print(f'{n} vertices: {count} classes, {improvements} improvements, '
                  f'{improved_labels} labelled improvements, {diamond_free} diamond-free classes', flush=True)
        assert len(rows) == total and seen_keys == set(proofs)
        print(f'{len(proofs)} DRAT refutations verified', flush=True)
    if generating:
        rows_path.write_text(json.dumps(rows, separators=(',', ':'))+'\n')
        payload = json.dumps(proofs, separators=(',', ':')).encode('ascii')
        proofs_path.write_bytes(gzip.compress(payload, mtime=0))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['generate', 'verify'])
    parser.add_argument('--drat-trim', default='drat-trim', help='path to the drat-trim executable')
    args = parser.parse_args()
    census(args.mode, args.drat_trim)
