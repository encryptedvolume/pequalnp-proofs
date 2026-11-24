import PEqualNP.Defs.MetaComplexityLgpMono

namespace Pentagons

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) :=
  [(0,1), (1,2), (2,3), (3,4), (4,0), (1,5), (5,6), (6,7), (7,0)]

-- Wires 8 through 16 compute the edge terms. The remaining eight gates join them.
def circuit : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[1,2]⟩, ⟨.and,[2,3]⟩, ⟨.and,[3,4]⟩, ⟨.and,[4,0]⟩,
    ⟨.and,[1,5]⟩, ⟨.and,[5,6]⟩, ⟨.and,[6,7]⟩, ⟨.and,[7,0]⟩,
    ⟨.or,[8,9]⟩, ⟨.or,[10,11]⟩, ⟨.or,[12,13]⟩, ⟨.or,[14,15]⟩,
    ⟨.or,[17,18]⟩, ⟨.or,[19,20]⟩, ⟨.or,[21,22]⟩, ⟨.or,[23,16]⟩], 24⟩

private def isOr : GateOp → Bool
  | .or => true
  | _ => false

theorem eight_or_gates : (circuit.gates.filter fun g => isOr g.op).length = 8 := rfl

theorem fan_in_two : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem computes :
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  decide +kernel

end Pentagons
