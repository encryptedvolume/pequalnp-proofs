import Mathlib
import PEqualNP.Outside.L_meta_1018

namespace HeavySlice

open PEqualNP.CircuitLowerBounds

def support (x : Fin 13 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter fun i => x i = true

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

lemma lineSize : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

-- Agreement on weight nine determines a monotone line output on all heavier inputs.
theorem weightNineSuffices (gates : List Gate) (out : Fin 13 → ℕ)
    (hMono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hNine : ∀ w (x : Fin 13 → Bool), (support x).card = 9 →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ i ∈ line w, x i = true)) :
    ∀ w (x : Fin 13 → Bool), 9 ≤ (support x).card →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ i ∈ line w, x i = true) := by
  classical
  intro w x hx
  by_cases h : ∃ i ∈ line w, x i = true
  · obtain ⟨p, hp, hxp⟩ := h
    have single : ({p} : Finset (Fin 13)) ⊆ support x := by simpa [support] using hxp
    obtain ⟨s, hs, hsub, hcard⟩ := Finset.exists_subsuperset_card_eq single (by simp : ({p} : Finset (Fin 13)).card ≤ 9) hx
    let y : Fin 13 → Bool := fun i => decide (i ∈ s)
    have hsup : support y = s := by ext i; simp [support, y]
    have hym (i) (hi : y i = true) : x i = true :=
      (Finset.mem_filter.mp (hsub (of_decide_eq_true hi))).2
    have hpy : y p = true := decide_eq_true (hs (Finset.mem_singleton_self p))
    have hy := hNine w y (hsup ▸ hcard)
    have hytrue : Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = true := by
      rw [hy]; exact decide_eq_true ⟨p, hp, hpy⟩
    have htrue : Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true :=
      PEqualNP.Outside.L_meta_1018.W_mono gates hMono (out w) y x hym hytrue
    rw [htrue]; exact (decide_eq_true ⟨p, hp, hxp⟩).symm
  · have sub : support x ⊆ (line w)ᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (fun hm => h ⟨i, hm, (Finset.mem_filter.mp hi).2⟩)
    have bound := Finset.card_le_card sub
    simp only [Finset.card_compl, Fintype.card_fin, lineSize] at bound
    exact hNine w x (by omega)


-- The thirteen line complements account for every possible false positive, even on light inputs.
theorem outputTrueHitsLine (gates : List Gate) (out : Fin 13 → ℕ)
    (hMono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hOff : ∀ w, Circuit.eval ⟨gates, out w⟩
      (List.ofFn (fun i : Fin 13 => decide (i ∉ line w))) = false) :
    ∀ w (x : Fin 13 → Bool), Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true →
      ∃ i ∈ line w, x i = true := by
  intro w x hx
  by_contra h
  have leOff (i) (hi : x i = true) : decide (i ∉ line w) = true :=
    decide_eq_true (fun hiL => h ⟨i, hiL, hi⟩)
  have hoffTrue : Circuit.eval ⟨gates, out w⟩
      (List.ofFn (fun i : Fin 13 => decide (i ∉ line w))) = true :=
    PEqualNP.Outside.L_meta_1018.W_mono gates hMono (out w) x _ leOff hx
  rw [hOff w] at hoffTrue
  contradiction

end HeavySlice
