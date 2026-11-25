"""Write a standalone Lean proof of the exact positive circuit size of a nonconstant 4-by-4 graph.

Run python3 rep44_proof.py MASK SIZE FILE. The filename supplies the theorem name.
The source template is the checked mask-4459 proof in this checkout. --template
selects another copy of that file. A successful run writes Lean source; use Lean
to check the resulting theorem before submitting a project assignment.
"""
import argparse
from itertools import combinations
from pathlib import Path
import re

from rep44_search import FULL, PINS, search, separation_test, successors

TEMPLATE_MODULE = "PEqualNP.Outside.L_meta_5982"
TEMPLATE_PATH = Path("lean/PEqualNP/Outside/L_meta_5982.lean")

ROOT_LEMMAS = r"""
-- Test the finitely many subsets of inputs that could supply a successful circuit.
def rootsOK (k : Nat) (roots : List Pool) : Bool :=
  pins.sublists.all fun xs =>
    if xs.toFinset.card ≤ k+1 && separates xs then roots.contains xs.toFinset else true

theorem rootKnown {k j : Nat} {s : Pool} {roots : List Pool} (hj : j ≤ k)
    (hs : ∀ a ∈ s, a ∈ pins) (t : Trace j s) (ok : rootsOK k roots = true) : s ∈ roots := by
  let xs := pins.filter fun a => decide (a ∈ s)
  have he : xs.toFinset = s := by
    ext a
    simp only [xs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨hs a ha,ha⟩⟩
  have hm : xs ∈ pins.sublists := List.mem_sublists.mpr List.filter_sublist
  have hi := List.all_eq_true.mp ok xs hm
  have hc : xs.toFinset.card ≤ k+1 := he ▸ (traceCard t).trans (by omega)
  have hv := separates_trace xs (he ▸ t)
  have yes : (decide (xs.toFinset.card ≤ k+1) && separates xs) = true := by
    simp only [decide_eq_true hc, hv, Bool.and_self]
  change (if decide (xs.toFinset.card ≤ k+1) && separates xs then roots.contains xs.toFinset else true) = true at hi
  rw [yes] at hi
  rw [← he]
  exact List.contains_iff_mem.mp hi
"""

def bad_list(indices, budget):
    term = f"(nilbad {budget})"
    for i in reversed(indices):
        term = f"(consbad n{i} {term})"
    return term


def pool_list(indices):
    return "[" + ", ".join(f"w{i}.toFinset" for i in indices) + "]"


def graph_type(mask, size):
    return f"PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => ({mask} : ℕ).testBit (4*u.val+v.val)) {size}"


def render_upper(mask, size, circuit):
    gates = circuit["gates"]
    items = [f"⟨.{op},[{','.join(map(str, pins))}]⟩" for op, pins in gates]
    syntax = ", ".join(items)
    cases = "|".join("rfl" for _ in gates)
    split = "    rcases hg with rfl\n    simp" if len(gates) == 1 else f"    rcases hg with ({cases}) <;> simp"
    return f"""
def upperCircuit : Circuit := ⟨[{syntax}], {circuit["output"]}⟩

theorem upper : {graph_type(mask, size)} := by
  refine ⟨upperCircuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [upperCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
{split}
  · decide +kernel
"""


def render_state(i, node, ids, separates):
    remaining, state = node
    next_ids = []
    if remaining:
        viable = successors(state, remaining, separates)
        next_ids = sorted({ids[remaining - 1, nxt] for _, nxt in viable})
    numbers = ",".join(map(str, state))
    return f"""
def w{i} : List Mask := [{numbers}]
theorem n{i} : impossible {remaining} w{i}.toFinset :=
  closeState (known := {pool_list(next_ids)}) w{i} (by decide) (by decide +kernel) {bad_list(next_ids, max(0, remaining - 1))}
"""


def generate(mask, size, name, template):
    if mask in (0, FULL) or size < 1:
        raise ValueError("this exact-size theorem requires a nonconstant graph and a positive size")
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
        raise ValueError("the output filename must be a Lean declaration name")
    upper, _ = search(mask, size)
    if not upper["circuit_found"]:
        raise ValueError("no circuit was found at the proposed upper bound")
    budget = size - 1
    lower, levels = search(mask, budget, True)
    if lower["circuit_found"]:
        raise ValueError("a smaller circuit exists")
    module = f"PEqualNP.Outside.{name}"
    head, marker, _ = template.partition("-- Wires 10, 12 and 14")
    if not marker or TEMPLATE_MODULE not in head:
        raise ValueError("the mask-4459 proof template is missing its circuit header")
    positives = [i for i in range(16) if mask >> i & 1]
    head = head.replace(TEMPLATE_MODULE, module)
    head = re.sub(r"\b4459\b", str(mask), head)
    head, count = re.subn(r"def positives : List Nat := \[[^\]]*\]", f"def positives : List Nat := {positives}", head)
    if count != 1:
        raise ValueError("the mask-4459 proof template is missing its positive rows")
    separates = separation_test(mask)
    nodes = sorted((k, tuple(ws)) for k, layer in levels.items() for ws in layer)
    ids = {node: i for i, node in enumerate(nodes)}
    roots = [
        ids[budget, root]
        for n in range(1, min(8, budget + 1) + 1)
        for root in combinations(sorted(PINS), n)
        if separates(root)
    ]
    parts = ["import Mathlib.Data.List.Sublists\n", head, render_upper(mask, size, upper), ROOT_LEMMAS]
    parts.extend(render_state(i, node, ids, separates) for i, node in enumerate(nodes))
    parts.append(f"""
theorem lower : ¬ {graph_type(mask, budget)} := by
  rintro ⟨C,hm,hs,hr⟩
  obtain ⟨k,hk,s,hsub,ht⟩ := extract C.gates pins C.output (desiredMask hm hr)
  have hroot : rootsOK {budget} {pool_list(roots)} = true := by decide +kernel
  have hbad : ∀ t ∈ {pool_list(roots)}, impossible {budget} t := {bad_list(roots, budget)}
  have hle := hk.trans hs
  exact hbad s (rootKnown hle hsub ht hroot) k hle ht

end {module}

theorem {module} :
    {graph_type(mask, size)} ∧
      ¬ {graph_type(mask, budget)} := by
  exact ⟨{module}.upper, {module}.lower⟩
""")
    return "".join(parts), len(nodes)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mask", type=lambda s: int(s, 0))
    parser.add_argument("size", type=int)
    parser.add_argument("output", type=Path)
    parser.add_argument("--template", type=Path, default=Path(__file__).resolve().parents[2] / TEMPLATE_PATH)
    args = parser.parse_args()
    try:
        text, count = generate(args.mask, args.size, args.output.stem, args.template.read_text())
        with args.output.open("x") as output_file:
            output_file.write(text)
    except (ValueError, OSError) as error:
        parser.exit(1, f"{error}\n")
    print(f"Wrote {args.output} with {count} lower-bound states.")
