import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The exact single-hole line count for the four-pigeon clique inequality is fourteen.

Work over the four Boolean variables for one hole. Allow the six pair clauses, Boolean
bounds, binary addition, multiplication by a nonnegative integer and rounded division
as in the project. Delete lines outside the dependency graph of the capacity conclusion.

* All six distinct pair clauses are necessary. Omitting pair {i,j} admits the assignment
  with just i and j set. Boolean bounds and the remaining pair clauses hold there.
* A connected derivation with L source lines uses at least L - 1 binary additions.
  Count premise occurrences as edges, with multiplicity: B binary and U unary operations
  supply 2B + U edges on L + B + U vertices. Equality makes the dependency graph a tree.
* Two genuine roundings are necessary. Before any rounding, all four unit points, zero,
  and the all-halves point satisfy every line. For a first rounded line written with
  upper-bound sign and quotient coefficients, the following theorem says it holds at
  the all-thirds point. It uses both the unit points and the all-halves point. Sums,
  nonnegative multiples and exact divisions preserve validity at that point. The
  desired capacity inequality fails there, since 4/3 > 1.
* Thirteen lines would therefore use exactly six pair axioms, five additions, and two
  roundings. Equality in the graph count gives a read-once tree. There is no room for
  a Boolean bound or a multiplication. All coefficients have the same sign, so after
  reversing the inequalities this is exactly the one-hole read-once system in
  ReadOnceCapacity.lean. Its kernel-checked single_hole theorem forces an upper bound
  of at least two for coefficient vector (1,1,1,1).
* Fourteen suffice: round the three pairs of a triangle to get T ≤ 1. Add twice that
  inequality to the three pairs incident to the fourth vertex d. This gives
  3(T+d) ≤ 5. Dividing by three gives T+d ≤ 1. The first fourteen lines of
  PigeonholeFourThree.lean replay this construction in the project's integer model.

The resource-count and graph-to-tree steps above are mathematical arguments.
The arithmetic supporting the rank argument is checked below.
-/

namespace PigeonholeOneHole

theorem thirds_from_bounds (a b c e bound : ℤ) (_hn : 0 ≤ bound)
    (ha : a ≤ bound) (hb : b ≤ bound) (hc : c ≤ bound) (he : e ≤ bound)
    (hh : (a+b+c+e)/2 ≤ bound) : a+b+c+e ≤ 3*bound := by
  by_cases h : bound = 0 <;> omega

theorem one_round_at_thirds (a b c e k t : ℤ) (hk : 0 < k) (hn : 0 ≤ t)
    (ha : a*k ≤ t) (hb : b*k ≤ t) (hc : c*k ≤ t) (he : e*k ≤ t)
    (hh : (a+b+c+e)*k ≤ 2*t) : a+b+c+e ≤ 3*(t/k) := by
  apply thirds_from_bounds
  · exact Int.ediv_nonneg hn hk.le
  · exact (Int.le_ediv_iff_mul_le hk).2 ha
  · exact (Int.le_ediv_iff_mul_le hk).2 hb
  · exact (Int.le_ediv_iff_mul_le hk).2 hc
  · exact (Int.le_ediv_iff_mul_le hk).2 he
  · apply (Int.le_ediv_iff_mul_le hk).2
    let s := a+b+c+e
    have hhalf : s / 2 * 2 ≤ s := Int.ediv_mul_le _ (by decide)
    have hprod : s / 2 * 2 * k ≤ 2*t := (mul_le_mul_of_nonneg_right hhalf hk.le).trans hh
    change s / 2 * k ≤ t
    have hnorm : 2*(s/2*k) = (s/2)*2*k := by ring
    rw [← hnorm] at hprod
    linarith only [hprod]

end PigeonholeOneHole
