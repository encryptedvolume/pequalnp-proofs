import PEqualNP.Defs.NotBracket
import Mathlib.Logic.Relation

/-!
L-meta-17828 asks whether a single negation ever saves gates for a monotone output.
Cut the negated wire to get monotone cofactors lo and hi. On the sensitive inputs
where the two differ, the negated bit is forced.

Comparable sensitive inputs must have the same bit. Consequently a connected
comparability graph permits a constant replacement. In general the upward closure
of the sensitive inputs requiring true is the least monotone replacement. The
theorems establish existence and order. Bounding the cost of computing this
replacement is the remaining circuit-size question.
-/

namespace OneNotSensitivity

open PEqualNP.NotBracket

variable {α : Type*}

/-- Inputs where changing the extra Boolean wire changes the output. -/
def Sensitive (lo hi : α → Bool) (x : α) : Prop :=
  lo x = false ∧ hi x = true

def choose (lo hi s : α → Bool) (x : α) : Bool :=
  if s x then hi x else lo x

def ComparableInside [Preorder α] (lo hi : α → Bool) (x y : α) : Prop :=
  Sensitive lo hi x ∧ Sensitive lo hi y ∧ (x ≤ y ∨ y ≤ x)

theorem choose_eq_selector {lo hi s : α → Bool} {x : α} (hx : Sensitive lo hi x) :
    choose lo hi s x = s x := by
  rcases hx with ⟨hl, hh⟩
  cases hs : s x <;> simp [choose, hs, hl, hh]

theorem same_output_iff {lo hi s t : α → Bool} (hb : ∀ x, lo x ≤ hi x) :
    choose lo hi s = choose lo hi t ↔ ∀ x, Sensitive lo hi x → s x = t x := by
  constructor
  · intro he x hx
    simpa only [choose_eq_selector hx] using congrFun he x
  · intro h
    funext x
    by_cases hx : Sensitive lo hi x
    · rw [choose_eq_selector hx, choose_eq_selector hx, h x hx]
    · have hle := hb x
      cases hl : lo x <;> cases hh : hi x <;> simp_all [Sensitive, choose, show ¬(true ≤ false) from by decide]

variable [Preorder α]

theorem monotone_choice_iff {lo hi h : α → Bool} (hl : Monotone lo) (hh : Monotone hi)
    (hb : ∀ x, lo x ≤ hi x) (hm : Monotone h) :
    Monotone (choose lo hi (fun x => !(h x))) ↔
      ∀ x y, Sensitive lo hi x → Sensitive lo hi y → x ≤ y → h x = h y := by
  constructor
  · intro hf x y hx hy hxy
    have hneg := hf hxy
    rw [choose_eq_selector hx, choose_eq_selector hy] at hneg
    have hpos := hm hxy
    cases ex : h x <;> cases ey : h y <;> simp_all [show ¬(true ≤ false) from by decide]
  · intro hconst x y hxy
    have hlxy := hl hxy
    have hhxy := hh hxy
    have hpos := hm hxy
    have hbx := hb x
    have hby := hb y
    have hfix := hconst x y
    cases h1 : lo x <;> cases h2 : hi x <;> cases h3 : lo y <;> cases h4 : hi y <;>
      cases h5 : h x <;> cases h6 : h y <;> simp_all [choose, Sensitive]

theorem climb {lo hi h : α → Bool}
    (hconst : ∀ x y, Sensitive lo hi x → Sensitive lo hi y → x ≤ y → h x = h y)
    {x y : α} (path : Relation.ReflTransGen (ComparableInside lo hi) x y) : h x = h y := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
    obtain ⟨ha, hb, hab | hba⟩ := step
    · exact ih.trans (hconst _ _ ha hb hab)
    · exact ih.trans (hconst _ _ hb ha hba).symm

theorem constant_on_connected_sensitivity {lo hi h : α → Bool}
    (hl : Monotone lo) (hh : Monotone hi) (hb : ∀ x, lo x ≤ hi x) (hm : Monotone h)
    (hf : Monotone (choose lo hi (fun x => !(h x))))
    (conn : ∀ x y, Sensitive lo hi x → Sensitive lo hi y →
      Relation.ReflTransGen (ComparableInside lo hi) x y) :
    ∃ b : Bool, choose lo hi (fun _ => b) = choose lo hi (fun x => !(h x)) := by
  by_cases hex : ∃ x, Sensitive lo hi x
  · obtain ⟨x, hx⟩ := hex
    refine ⟨!(h x), (same_output_iff hb).2 ?_⟩
    intro y hy
    exact congrArg Bool.not (climb ((monotone_choice_iff hl hh hb hm).1 hf) (conn x y hx hy))
  · exact ⟨false, (same_output_iff hb).2 (fun x hx => False.elim (hex ⟨x, hx⟩))⟩

/-- The least monotone wire that agrees with the negated wire on its sensitive inputs. -/
noncomputable def leastSelector (lo hi h : α → Bool) (x : α) : Bool := by
  classical
  exact decide (∃ y, y ≤ x ∧ Sensitive lo hi y ∧ h y = false)

theorem leastSelector_true {lo hi h : α → Bool} {x : α} :
    leastSelector lo hi h x = true ↔ ∃ y, y ≤ x ∧ Sensitive lo hi y ∧ h y = false := by
  classical
  simp [leastSelector]

theorem leastSelector_mono (lo hi h : α → Bool) : Monotone (leastSelector lo hi h) := by
  intro x y hxy
  cases hx : leastSelector lo hi h x
  · exact Bool.false_le _
  · obtain ⟨w, hw, hs, h0⟩ := leastSelector_true.mp hx
    rw [leastSelector_true.mpr ⟨w, hw.trans hxy, hs, h0⟩]

theorem leastSelector_works {lo hi h : α → Bool} (hb : ∀ x, lo x ≤ hi x)
    (hc : ∀ x y, Sensitive lo hi x → Sensitive lo hi y → x ≤ y → h x = h y) :
    choose lo hi (leastSelector lo hi h) = choose lo hi (fun x => !(h x)) := by
  apply (same_output_iff hb).2
  intro x hx
  cases ex : h x
  · exact leastSelector_true.mpr ⟨x, le_rfl, hx, ex⟩
  · cases he : leastSelector lo hi h x
    · rfl
    · obtain ⟨w, hw, hs, h0⟩ := leastSelector_true.mp he
      have := hc w x hs hx hw
      simp_all

theorem leastSelector_le {lo hi h s : α → Bool} (hb : ∀ x, lo x ≤ hi x) (hm : Monotone s)
    (he : choose lo hi s = choose lo hi (fun x => !(h x))) :
    ∀ x, leastSelector lo hi h x ≤ s x := by
  intro x
  cases hx : leastSelector lo hi h x
  · exact Bool.false_le _
  · obtain ⟨y, hy, hs, h0⟩ := leastSelector_true.mp hx
    have h1 := (same_output_iff hb).1 he y hs
    simpa [h1, h0] using hm hy

theorem withZ_le {n : Nat} {x y : Fin n → Bool} {a b : Bool} (hxy : x ≤ y) (hab : a ≤ b) :
    withZ x a ≤ withZ y b := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [withZ] using hab
  · simpa [withZ] using hxy j

/-- Apply the connectivity test directly to each output of the project's bracket. -/
theorem project_connected_output {n m : Nat} {f G h} (B : IsNotBracket n m f G h) (i : Fin m)
    (conn : ∀ x y, Sensitive (fun z => G i (withZ z false)) (fun z => G i (withZ z true)) x →
      Sensitive (fun z => G i (withZ z false)) (fun z => G i (withZ z true)) y →
      Relation.ReflTransGen (ComparableInside (fun z => G i (withZ z false))
        (fun z => G i (withZ z true))) x y) :
    ∃ b : Bool, ∀ x, G i (withZ x b) = f i x := by
  obtain ⟨hf, hG, hm, he⟩ := B
  let lo := fun x => G i (withZ x false)
  let hi := fun x => G i (withZ x true)
  have hl : Monotone lo := fun _ _ hxy => hG i (withZ_le hxy le_rfl)
  have hh : Monotone hi := fun _ _ hxy => hG i (withZ_le hxy le_rfl)
  have hb : ∀ x, lo x ≤ hi x := fun _ => hG i (withZ_le le_rfl (by decide))
  have eq : choose lo hi (fun x => !(h x)) = f i := by
    funext x
    have hx := he i x
    cases e : h x <;> simpa [choose, lo, hi, e] using hx
  obtain ⟨b, eb⟩ := constant_on_connected_sensitivity hl hh hb hm (eq ▸ hf i) conn
  refine ⟨b, ?_⟩
  intro x
  have hx := congrFun (eb.trans eq) x
  cases b <;> simpa [choose, lo, hi] using hx

/-- Sharpness on two inputs. With the second input negated, majority returns the first.
The two constant substitutions fail on opposite, incomparable points of the Boolean square. -/
theorem two_incomparable_witnesses :
    let lo := fun p : Bool × Bool => p.1 && p.2
    let hi := fun p : Bool × Bool => p.1 || p.2
    let h := fun p : Bool × Bool => p.2
    let f := fun p : Bool × Bool => p.1
    choose lo hi (fun p => !(h p)) = f ∧
      (∀ b, choose lo hi (fun _ => b) ≠ f) ∧
      (∀ p, Sensitive lo hi p ↔ p = (true, false) ∨ p = (false, true)) ∧
      (∀ p, leastSelector lo hi h p = f p) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext p
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  · intro b he
    cases b
    · have hbad := congrFun he (true, false)
      contradiction
    · have hbad := congrFun he (false, true)
      contradiction
  · rintro ⟨a,b⟩
    cases a <;> cases b <;> simp [Sensitive]
  · rintro ⟨a,b⟩
    apply Bool.eq_iff_iff.mpr
    rw [leastSelector_true]
    cases a <;> cases b <;> simp [Sensitive, Prod.exists]

end OneNotSensitivity
