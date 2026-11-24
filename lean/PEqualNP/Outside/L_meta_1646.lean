import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G _ hNoFour U hEdges x Y hChosen R π hBlocks hCover
  have adjY (y) (hy : y ∈ Y) : G.Adj x y :=
    hEdges _ (hChosen y hy)
  -- A block meeting Y can contain only one neighbour of x.
  have uniqueInBlock (B) (hB : B ∈ π) (y z : Fin n)
      (hyB : y ∈ B) (hy : y ∈ Y) (hzB : z ∈ B) (hxz : G.Adj x z) : y = z := by
    rcases (hBlocks B hB).2 with hOne | ⟨_, c, hCenter, hUnused⟩
    · exact Finset.card_le_one.mp hOne.le y hyB z hzB
    · by_cases hxc : x = c
      · subst c
        exact False.elim (hUnused y hyB (hChosen y hy))
      · apply Finset.card_le_one.mp (hNoFour x c hxc)
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, adjY y hy, hCenter y hyB⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz, hCenter z hzB⟩
  -- Assign each vertex to one covering block. The preceding property makes this injective.
  have countCover (blocks : Finset (Finset (Fin n))) (hSub : blocks ⊆ π)
      (cover : ∀ v ∈ R ∩ Y, ∃ B ∈ blocks, v ∈ B) : (R ∩ Y).card ≤ blocks.card := by
    have chooseBlock (v : ↥(R ∩ Y)) : ∃ B ∈ blocks, v.val ∈ B := cover _ v.property
    choose block hBlock hContains using chooseBlock
    let assign : ↥(R ∩ Y) → ↥blocks := fun v => ⟨block v, hBlock v⟩
    have hinj : Function.Injective assign := by
      intro v w hEq
      have same : block v = block w := congrArg (fun b : ↥blocks => b.val) hEq
      apply Subtype.ext
      exact uniqueInBlock _ (hSub (hBlock v)) _ _ (hContains v)
        (Finset.mem_inter.mp v.property).2 (same.symm ▸ hContains w)
        (adjY _ (Finset.mem_inter.mp w.property).2)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective assign hinj
  constructor
  · exact countCover π (fun _ h => h) (fun v hv => hCover v (Finset.mem_inter.mp hv).1)
  · intro hAdj hNotSubset
    obtain ⟨r, hr, hrOutside⟩ : ∃ r ∈ R, r ∉ Y := by
      by_contra! hall
      exact hNotSubset (fun _ hm => hall _ hm)
    obtain ⟨extra, hExtra, hrExtra⟩ := hCover r hr
    -- A block containing r cannot cover any vertex of the intersection.
    have coverRest (y) (hy : y ∈ R ∩ Y) : ∃ B ∈ π.erase extra, y ∈ B := by
      obtain ⟨hyR, hyY⟩ := Finset.mem_inter.mp hy
      obtain ⟨B, hB, hyB⟩ := hCover y hyR
      refine ⟨B, Finset.mem_erase.mpr ⟨?_, hB⟩, hyB⟩
      intro heq
      subst B
      exact hrOutside (uniqueInBlock extra hExtra y r hyB hyY hrExtra (hAdj r hr) ▸ hyY)
    have h := countCover (π.erase extra) (Finset.erase_subset _ _) coverRest
    have hCard := Finset.card_erase_of_mem hExtra
    have hPos := Finset.card_pos.mpr ⟨extra, hExtra⟩
    omega
