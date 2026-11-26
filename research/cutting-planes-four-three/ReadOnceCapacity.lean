import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

/-!
Four pigeons contribute six pair constraints to each hole. This proof considers
addition and rounded division and allows inequalities from any holes to be combined.
Each source pair may occur at most once in the expanded proof tree. Pigeon clauses,
Boolean bounds and multiplication are outside this fragment.

The 107 local states form a finite invariant. Lean checks the base cases and closure
under every permitted operation, including arbitrarily large divisors. The projection
lemma then applies the invariant to any number of holes. An upper bound with one unit
of coefficient on each variable must allow at least two units per hole.
-/

namespace PigeonholeReadOnce

abbrev Mask := BitVec 6
abbrev Coeff := Nat × Nat × Nat × Nat
abbrev Line := Coeff × Nat

def zero : Coeff := (0, 0, 0, 0)
def ones : Coeff := (1, 1, 1, 1)
def coeffs (a : Coeff) : List Nat := [a.1, a.2.1, a.2.2.1, a.2.2.2]
def plus (a b : Coeff) : Coeff :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2+b.2.2.2)
def quotient (a : Coeff) (d : Nat) : Coeff :=
  (a.1/d, a.2.1/d, a.2.2.1/d, a.2.2.2/d)
def name (i : Fin 6) : Mask := (1 : Mask) <<< i.val
def edge (i : Fin 6) : Coeff :=
  ![(1,1,0,0), (1,0,1,0), (1,0,0,1), (0,1,1,0), (0,1,0,1), (0,0,1,1)] i

def rows (m : Mask) : List Line :=
  match m.toNat with
  | 0 => [((0, 0, 0, 0), 0)]
  | 1 => [((1, 1, 0, 0), 1)]
  | 2 => [((1, 0, 1, 0), 1)]
  | 3 => [((2, 1, 1, 0), 2)]
  | 4 => [((1, 0, 0, 1), 1)]
  | 5 => [((2, 1, 0, 1), 2)]
  | 6 => [((2, 0, 1, 1), 2)]
  | 7 => [((3, 1, 1, 1), 3)]
  | 8 => [((0, 1, 1, 0), 1)]
  | 9 => [((1, 2, 1, 0), 2)]
  | 10 => [((1, 1, 2, 0), 2)]
  | 11 => [((1, 1, 1, 0), 1), ((2, 2, 2, 0), 3)]
  | 12 => [((1, 1, 1, 1), 2)]
  | 13 => [((2, 2, 1, 1), 3)]
  | 14 => [((2, 1, 2, 1), 3)]
  | 15 => [((2, 1, 1, 1), 2), ((3, 2, 2, 1), 4)]
  | 16 => [((0, 1, 0, 1), 1)]
  | 17 => [((1, 2, 0, 1), 2)]
  | 18 => [((1, 1, 1, 1), 2)]
  | 19 => [((2, 2, 1, 1), 3)]
  | 20 => [((1, 1, 0, 2), 2)]
  | 21 => [((1, 1, 0, 1), 1), ((2, 2, 0, 2), 3)]
  | 22 => [((2, 1, 1, 2), 3)]
  | 23 => [((2, 1, 1, 1), 2), ((3, 2, 1, 2), 4)]
  | 24 => [((0, 2, 1, 1), 2)]
  | 25 => [((1, 3, 1, 1), 3)]
  | 26 => [((1, 2, 2, 1), 3)]
  | 27 => [((1, 2, 1, 1), 2), ((2, 3, 2, 1), 4)]
  | 28 => [((1, 2, 1, 2), 3)]
  | 29 => [((1, 2, 1, 1), 2), ((2, 3, 1, 2), 4)]
  | 30 => [((1, 1, 1, 1), 2), ((2, 2, 2, 2), 4)]
  | 31 => [((2, 2, 1, 1), 3), ((2, 2, 1, 2), 3), ((2, 2, 2, 1), 3), ((3, 3, 2, 2), 5)]
  | 32 => [((0, 0, 1, 1), 1)]
  | 33 => [((1, 1, 1, 1), 2)]
  | 34 => [((1, 0, 2, 1), 2)]
  | 35 => [((2, 1, 2, 1), 3)]
  | 36 => [((1, 0, 1, 2), 2)]
  | 37 => [((2, 1, 1, 2), 3)]
  | 38 => [((1, 0, 1, 1), 1), ((2, 0, 2, 2), 3)]
  | 39 => [((2, 1, 1, 1), 2), ((3, 1, 2, 2), 4)]
  | 40 => [((0, 1, 2, 1), 2)]
  | 41 => [((1, 2, 2, 1), 3)]
  | 42 => [((1, 1, 3, 1), 3)]
  | 43 => [((1, 1, 2, 1), 2), ((2, 2, 3, 1), 4)]
  | 44 => [((1, 1, 2, 2), 3)]
  | 45 => [((1, 1, 1, 1), 2), ((2, 2, 2, 2), 4)]
  | 46 => [((1, 1, 2, 1), 2), ((2, 1, 3, 2), 4)]
  | 47 => [((2, 1, 2, 1), 3), ((2, 1, 2, 2), 3), ((2, 2, 2, 1), 3), ((3, 2, 3, 2), 5)]
  | 48 => [((0, 1, 1, 2), 2)]
  | 49 => [((1, 2, 1, 2), 3)]
  | 50 => [((1, 1, 2, 2), 3)]
  | 51 => [((1, 1, 1, 1), 2), ((2, 2, 2, 2), 4)]
  | 52 => [((1, 1, 1, 3), 3)]
  | 53 => [((1, 1, 1, 2), 2), ((2, 2, 1, 3), 4)]
  | 54 => [((1, 1, 1, 2), 2), ((2, 1, 2, 3), 4)]
  | 55 => [((2, 1, 1, 2), 3), ((2, 1, 2, 2), 3), ((2, 2, 1, 2), 3), ((3, 2, 2, 3), 5)]
  | 56 => [((0, 1, 1, 1), 1), ((0, 2, 2, 2), 3)]
  | 57 => [((1, 2, 1, 1), 2), ((1, 3, 2, 2), 4)]
  | 58 => [((1, 1, 2, 1), 2), ((1, 2, 3, 2), 4)]
  | 59 => [((1, 2, 2, 1), 3), ((1, 2, 2, 2), 3), ((2, 2, 2, 1), 3), ((2, 3, 3, 2), 5)]
  | 60 => [((1, 1, 1, 2), 2), ((1, 2, 2, 3), 4)]
  | 61 => [((1, 2, 1, 2), 3), ((1, 2, 2, 2), 3), ((2, 2, 1, 2), 3), ((2, 3, 2, 3), 5)]
  | 62 => [((1, 1, 2, 2), 3), ((1, 2, 2, 2), 3), ((2, 1, 2, 2), 3), ((2, 2, 3, 3), 5)]
  | 63 => [((1, 1, 1, 1), 2), ((2, 2, 2, 2), 4), ((2, 2, 2, 3), 4), ((2, 2, 3, 2), 4), ((2, 3, 2, 2), 4), ((3, 2, 2, 2), 4), ((3, 3, 3, 3), 6)]
  | _ => []

def All (s : List Line) (p : Line → Prop) [DecidablePred p] := s.all (fun x => decide (p x))

theorem fromAll {s : List Line} {p : Line → Prop} [DecidablePred p] (hs : All s p = true)
    {x} (hx : x ∈ s) : p x :=
  of_decide_eq_true (List.all_eq_true.mp hs x hx)

def sumTest (a b : Mask) : Bool :=
  if (a &&& b) = 0 then
    All (rows a) (fun x => All (rows b) (fun y => (plus x.1 y.1, x.2+y.2) ∈ rows (a ||| b)) = true)
  else true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem sumsChecked : ∀ a b : Mask, sumTest a b = true := by decide +kernel

def divTest (a : Mask) (d : Nat) : Bool :=
  All (rows a) (fun x => (∀ k ∈ coeffs x.1, d ∣ k) →
    (quotient x.1 d, x.2/d) ∈ rows a)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem divsChecked : ∀ a : Mask, divTest a 1 && divTest a 2 && divTest a 3 = true := by decide +kernel

set_option maxRecDepth 12000 in
theorem magsChecked : ∀ a : Mask, All (rows a) (fun x => x = (zero, 0) ∨
    ∃ k ∈ coeffs x.1, 0 < k ∧ k ≤ 3) = true := by decide +kernel

set_option maxRecDepth 12000 in
theorem endsChecked : ∀ a : Mask, All (rows a) (fun x => x.1 = ones → 2 ≤ x.2) = true := by
  decide +kernel

/-- Upper-form inequalities. The mask records the unordered pairs of pigeons used at this hole. -/
inductive ReadOnce : Mask → Coeff → Nat → Prop
  | nil : ReadOnce 0 zero 0
  | ax (i : Fin 6) : ReadOnce (name i) (edge i) 1
  | add {a b x y p q} : ReadOnce a x p → ReadOnce b y q → a &&& b = 0 →
      ReadOnce (a ||| b) (plus x y) (p+q)
  | div {a x p} (d : Nat) : ReadOnce a x p → 0 < d → (∀ k ∈ coeffs x, d ∣ k) →
      ReadOnce a (quotient x d) (p/d)

theorem inTable {a x p} (h : ReadOnce a x p) : (x,p) ∈ rows a := by
  induction h with
  | nil => decide
  | ax i => fin_cases i <;> decide
  | @add a b x y p q _ _ hab ih jh =>
    have ht := sumsChecked a b
    simp only [sumTest, hab, ite_true] at ht
    exact fromAll (fromAll ht ih) jh
  | @div a x p d _ hd hdiv ih =>
    by_cases hsmall : d ≤ 3
    · have ht := divsChecked a
      simp only [Bool.and_eq_true] at ht
      have good : divTest a d = true := by
        rcases (show d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl
        · exact ht.1.1
        · exact ht.1.2
        · exact ht.2
      exact (fromAll good ih) hdiv
    · rcases fromAll (magsChecked a) ih with he | ⟨k,hk,hpos,hk3⟩
      · change (x,p) = (zero,0) at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        simpa [zero, quotient] using ih
      · exact False.elim (by have := Nat.le_of_dvd hpos (hdiv k hk); omega)

theorem single_hole {a p} (h : ReadOnce a ones p) : 2 ≤ p :=
  (fromAll (endsChecked a) (inTable h)) rfl

/-- Pair clauses from several holes may be interleaved in any order, including before division. -/
inductive Mixed (n : Nat) : (Fin n → Mask) → (Fin n → Coeff) → Nat → Prop
  | nil : Mixed n (fun _ => 0) (fun _ => zero) 0
  | ax (hole : Fin n) (i : Fin 6) :
      Mixed n (fun j => if j = hole then name i else 0)
        (fun j => if j = hole then edge i else zero) 1
  | add {a b x y p q} : Mixed n a x p → Mixed n b y q → (∀ j, a j &&& b j = 0) →
      Mixed n (fun j => a j ||| b j) (fun j => plus (x j) (y j)) (p+q)
  | div {a x p} (d : Nat) : Mixed n a x p → 0 < d → (∀ j k, k ∈ coeffs (x j) → d ∣ k) →
      Mixed n a (fun j => quotient (x j) d) (p/d)

theorem project_bounds {n a x p} (h : Mixed n a x p) :
    ∃ t : Fin n → Nat, (∀ j, ReadOnce (a j) (x j) (t j)) ∧ ∑ j, t j ≤ p := by
  induction h with
  | nil => exact ⟨fun _ => 0, fun _ => .nil, by simp⟩
  | ax hole i =>
    refine ⟨fun j => if j = hole then 1 else 0, ?_, by simp⟩
    intro j
    by_cases h : j = hole
    · simpa [h] using ReadOnce.ax i
    · simpa [h] using ReadOnce.nil
  | add _ _ hsep ih jh =>
    obtain ⟨t, ht, hp⟩ := ih
    obtain ⟨u, hu, hq⟩ := jh
    exact ⟨fun j => t j + u j, fun j => .add (ht j) (hu j) (hsep j),
      by rw [Finset.sum_add_distrib]; exact Nat.add_le_add hp hq⟩
  | div d _ hd hdiv ih =>
    obtain ⟨t, ht, hp⟩ := ih
    refine ⟨fun j => t j / d, fun j => .div d (ht j) hd (hdiv j), ?_⟩
    apply (Nat.le_div_iff_mul_le hd).2
    rw [Finset.sum_mul]
    exact le_trans (Finset.sum_le_sum fun j _ => Nat.div_mul_le_self (t j) d) hp

theorem mixed_capacity {n a p} (h : Mixed n a (fun _ => ones) p) : 2*n ≤ p := by
  obtain ⟨t, ht, hp⟩ := project_bounds h
  have lower := Finset.sum_le_sum (s := Finset.univ) (fun j _ => single_hole (ht j))
  simpa [Nat.mul_comm] using le_trans lower hp

theorem three_holes {a p} (h : Mixed 3 a (fun _ => ones) p) : 6 ≤ p := mixed_capacity h

/-- Two disjoint pairs attain the one-hole bound. -/
theorem single_two : ∃ m, ReadOnce m ones 2 := by
  let i : Fin 6 := 0
  let j : Fin 6 := 5
  have h := ReadOnce.add (ReadOnce.ax i) (ReadOnce.ax j)
    (show name i &&& name j = 0 by decide)
  exact ⟨_, (show plus (edge i) (edge j) = ones by decide) ▸ h⟩

end PigeonholeReadOnce
