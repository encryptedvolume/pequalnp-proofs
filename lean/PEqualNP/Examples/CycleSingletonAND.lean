import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.MetaComplexityLgpMono

/-!
For the incidence six-cycle, eight monotone fan-in-two gates are necessary on the
full six-input Boolean cube. An eight-gate circuit achieves the minimum with every
AND false on every singleton. The theorem `cycleNormalized` gives a replacement
for any monotone circuit computing the six-cycle edge function.
-/

namespace CycleSingletonAND

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev Mask := BitVec 64
abbrev Pool := Finset Mask

def target : Mask := 18374403832151735296
def full : Mask := BitVec.allOnes 64
def pins : List Mask := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320]

def combine (meet : Bool) (a b : Mask) : Mask := if meet then a &&& b else a ||| b

def maskGate (ws : List Mask) (g : Gate) : Mask :=
  let meet := match g.op with | .and => true | _ => false
  match g.inputs with
  | [] => if meet then full else 0
  | [i] => ws.getD i 0
  | i :: j :: _ => combine meet (ws.getD i 0) (ws.getD j 0)

def legal (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def readBit (r : Nat) (x : Mask) := x.getLsbD r

theorem atWire (ws : List Mask) (r i : Nat) :
    (ws.map (readBit r)).getD i false = readBit r (ws.getD i 0) := by
  have z : readBit r 0 = false := by simp [readBit]
  simpa only [z] using List.getD_map (l := ws) (n := i) (d := (0 : Mask)) (readBit r)

theorem gateBits (ws : List Mask) {g : Gate} (hg : legal g) (r : Nat) (hr : r < 64) :
    readBit r (maskGate ws g) =
      g.op.eval (g.inputs.map fun i => (ws.map (readBit r)).getD i false) := by
  rcases g with ⟨op, args⟩
  obtain ⟨hop, hlen⟩ := hg
  change op = GateOp.and ∨ op = GateOp.or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil => rcases hop with rfl | rfl
           · exact (BitVec.getLsbD_allOnes.trans (decide_eq_true hr))
           · simp [maskGate, readBit, GateOp.eval]
  | cons i rest =>
    cases rest with
    | nil => rcases hop with rfl | rfl <;> simp [maskGate, GateOp.eval, -List.getD_eq_getElem?_getD, atWire]
    | cons j rest =>
      have he : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
      subst rest
      rcases hop with rfl | rfl <;>
        simp [maskGate, GateOp.eval, combine, -List.getD_eq_getElem?_getD, atWire, readBit]

def applyGate (ws : List Mask) (g : Gate) := ws ++ [maskGate ws g]

theorem runBits (gs : List Gate) (h : ∀ g ∈ gs, legal g) (ws : List Mask) (r : Nat) (hr : r < 64) :
    (gs.foldl applyGate ws).map (readBit r) =
      gs.foldl (fun bs g => bs ++ [g.op.eval (g.inputs.map fun i => bs.getD i false)]) (ws.map (readBit r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    simp [applyGate, gateBits ws (h g (by simp)) r hr]

def incidence (p l : Fin 3) : Prop := (238 : Nat).testBit (3*p.val+l.val) = true

theorem noFourCycle : ∀ p q l m : Fin 3, p ≠ q → l ≠ m →
    ¬ (incidence p l ∧ incidence p m ∧ incidence q l ∧ incidence q m) := by
  unfold incidence
  decide +kernel

def computes (C : Circuit) : Prop :=
  ∀ z : Fin 6 → Bool, circuitFun 6 C z = true ↔
    ∃ p l : Fin 3, incidence p l ∧ z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true

theorem desiredMask {C : Circuit} (hm : Monotone2 C) (hc : computes C) :
    (C.gates.foldl applyGate pins).getD C.output 0 = target := by
  have hlegal : ∀ g ∈ C.gates, legal g := fun g hg => hm g hg
  have hp : ∀ r : Fin 64, pins.map (readBit r.val) = List.ofFn (fun i : Fin 6 => r.val.testBit i.val) := by decide +kernel
  have ht : ∀ r : Fin 64, readBit r.val target = true ↔ ∃ p l : Fin 3,
      (238 : Nat).testBit (3*p.val+l.val) = true ∧ r.val.testBit (Fin.castAdd 3 p).val = true ∧
      r.val.testBit (Fin.natAdd 3 l).val = true := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  change readBit r _ = readBit r _
  rw [← atWire, runBits C.gates hlegal pins r hr, hp ⟨r,hr⟩]
  exact Bool.eq_iff_iff.mpr ((hc _).trans (ht ⟨r,hr⟩).symm)

def nontriv (a : Mask) : Prop := a ≠ 0 ∧ a ≠ full

-- Each 64-bit word gives the values of a wire on all assignments to the six vertex inputs.
-- A state records the wire values still needed to compute the designated output.
-- Reading a gate backwards replaces its output by its two operands.
def Trace : Nat → Pool → Prop
  | 0, s => s = {target}
  | k+1, prev => ∃ (s : Pool) (c a b : Mask) (op : Bool), c ∈ s ∧
      nontriv a ∧ nontriv b ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ c = combine op a b ∧
      Trace k s ∧ prev = insert a (insert b (s.erase c))

theorem Trace.done : Trace 0 {target} := rfl

theorem Trace.join {k : Nat} {s : Pool} (c a b : Mask) (op : Bool) (hc : c ∈ s)
    (ha : nontriv a) (hb : nontriv b) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (how : c = combine op a b) (tail : Trace k s) :
    Trace (k+1) (insert a (insert b (s.erase c))) :=
  ⟨s,c,a,b,op,hc,ha,hb,hab,hca,hcb,how,tail,rfl⟩

theorem traceNontriv {k s} (t : Trace k s) : ∀ a ∈ s, nontriv a := by
  induction k generalizing s with
  | zero =>
    change s = {target} at t
    subst s

    intro a ha
    obtain rfl : a = target := by simpa using ha
    exact ⟨by decide, by decide⟩
  | succ k step =>
    obtain ⟨s,c,a,b,op,hc,ha,hb,hab,hca,hcb,how,tail,rfl⟩ := t
    have ih := step tail
    intro d hd
    simp only [Finset.mem_insert,Finset.mem_erase] at hd
    rcases hd with rfl | rfl | ⟨_,hd⟩
    · exact ha
    · exact hb
    · exact ih _ hd

theorem traceCard {k s} (t : Trace k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero =>
    change s = {target} at t
    subst s
    simp
  | succ k step =>
    obtain ⟨s,c,a,b,op,hc,ha,hb,hab,hca,hcb,how,tail,rfl⟩ := t
    have ih := step tail
    have e := Finset.card_erase_add_one hc
    have h₁ := Finset.card_insert_le a (insert b (s.erase c))
    have h₂ := Finset.card_insert_le b (s.erase c)
    omega

theorem inPool (ws : List Mask) (i : Nat) (hn : ws.getD i 0 ≠ 0) : ws.getD i 0 ∈ ws := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ i)] at hn

theorem newGate (ws : List Mask) (g : Gate) (hn : nontriv (maskGate ws g))
    (fresh : maskGate ws g ∉ ws) :
    ∃ a ∈ ws, ∃ b ∈ ws, ∃ op, nontriv a ∧ nontriv b ∧ a ≠ b ∧
      maskGate ws g ≠ a ∧ maskGate ws g ≠ b ∧ maskGate ws g = combine op a b := by
  rcases g with ⟨op, args⟩
  cases args with
  | nil => cases op <;> simp [nontriv,maskGate] at hn
  | cons i rest =>
    cases rest with
    | nil => exact (fresh (inPool ws i hn.1)).elim
    | cons j rest =>
      let a := ws.getD i 0
      let b := ws.getD j 0
      let m := match op with | GateOp.and => true | _ => false
      change nontriv (combine m a b) at hn
      change combine m a b ∉ ws at fresh
      have ea : a = 0 ∨ a ∈ ws := or_iff_not_imp_left.mpr (inPool ws i)
      have eb : b = 0 ∨ b ∈ ws := or_iff_not_imp_left.mpr (inPool ws j)
      have ca : combine m a b ≠ a := fun e => ea.elim (fun h => hn.1 (e.trans h)) (fun h => fresh (by rw [e]; exact h))
      have cb : combine m a b ≠ b := fun e => eb.elim (fun h => hn.1 (e.trans h)) (fun h => fresh (by rw [e]; exact h))
      have za (x : Mask) : (0 : Mask) &&& x = 0 := by simp
      have az (x : Mask) : x &&& (0 : Mask) = 0 := by simp
      have zo (x : Mask) : (0 : Mask) ||| x = x := by simp
      have oz (x : Mask) : x ||| (0 : Mask) = x := by simp
      have ha : nontriv a := by
        constructor <;> intro h <;> cases hm : m <;>
          simp only [combine, hm, Bool.false_eq_true, ite_false, ite_true, h, full, BitVec.allOnes_and, BitVec.allOnes_or, za, zo] at ca cb <;> first | exact ca rfl | exact cb rfl
      have hb : nontriv b := by
        constructor <;> intro h <;> cases hm : m <;>
          simp only [combine, hm, Bool.false_eq_true, ite_false, ite_true, h, full, BitVec.and_allOnes, BitVec.or_allOnes, az, oz] at ca cb <;> first | exact ca rfl | exact cb rfl
      have hab : a ≠ b := by intro h; cases hm : m <;> simp [combine, hm, h] at cb
      exact ⟨a, ea.resolve_left ha.1, b, eb.resolve_left hb.1, m, ha, hb, hab, ca, cb, rfl⟩

theorem extract (gs : List Gate) (ws : List Mask) (o : Nat)
    (h : (gs.foldl applyGate ws).getD o 0 = target) :
    ∃ k ≤ gs.length, ∃ s : Pool, (∀ a ∈ s, a ∈ ws) ∧ Trace k s := by
  induction gs generalizing ws with
  | nil =>
    have ht : target ≠ 0 := by decide
    have htmem : target ∈ ws := h ▸ inPool ws o (h ▸ ht)
    exact ⟨0, by simp, {target}, by simpa, Trace.done⟩
  | cons g gs ih =>
    obtain ⟨k,hk,s,hs,t⟩ := ih (applyGate ws g) h
    let c := maskGate ws g
    have hs' (a) (ha : a ∈ s) : a ∈ ws ∨ a = c := by simpa [applyGate,c] using hs a ha
    by_cases stay : ∀ a ∈ s, a ∈ ws
    · exact ⟨k, by simp; omega, s, stay, t⟩
    · push Not at stay
      obtain ⟨d,hd,hdw⟩ := stay
      obtain rfl : d = c := (hs' d hd).resolve_left hdw
      obtain ⟨a,aw,b,bw,op,ha,hb,hab,hca,hcb,how⟩ := newGate ws g (traceNontriv t c hd) hdw
      refine ⟨k+1, by simp; omega, _, ?_, Trace.join c a b op hd ha hb hab hca hcb how t⟩
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_erase] at hv
      rcases hv with rfl | rfl | ⟨hne,hv⟩
      · exact aw
      · exact bw
      · exact (hs' v hv).resolve_right hne

theorem traceDist {k s} (t : Trace k s) (p n : Nat)
    (hp : target.getLsbD p = true) (hn : target.getLsbD n = false) :
    ∃ w ∈ s, w.getLsbD p = true ∧ w.getLsbD n = false := by
  induction k generalizing s with
  | zero =>
    change s = {target} at t
    subst s
    exact ⟨target, by simp, hp, hn⟩
  | succ k step =>
    obtain ⟨s,c,a,b,op,hc,ha,hb,hab,hca,hcb,how,tail,rfl⟩ := t
    have ih := step tail
    obtain ⟨w,hw,wp,wn⟩ := ih
    by_cases he : w = c
    · subst w
      have hor : (a.getLsbD p = true ∧ a.getLsbD n = false) ∨ (b.getLsbD p = true ∧ b.getLsbD n = false) := by
        rw [how] at wp wn
        cases op <;> simp only [combine, Bool.false_eq_true, ite_false, ite_true,
          BitVec.getLsbD_or, BitVec.getLsbD_and, Bool.or_eq_true, Bool.and_eq_true,
          Bool.or_eq_false_iff, Bool.and_eq_false_imp] at wp wn <;>
          cases h₁ : a.getLsbD p <;> cases h₂ : a.getLsbD n <;> cases h₃ : b.getLsbD p <;> cases h₄ : b.getLsbD n <;> simp_all
      exact hor.elim (fun h => ⟨a, by simp, h⟩) (fun h => ⟨b, by simp, h⟩)
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hw⟩)), wp, wn⟩

-- A positive and a negative row must have some remaining wire that is high only on the positive row.
-- Intersecting the high wires at a positive row identifies all negatives that still escape detection.
def positives : List Nat := [10, 12, 17, 20, 33, 34]

def survivors (p : Nat) : List Mask → Mask
  | [] => ~~~target
  | w :: ws => if w.getLsbD p then w &&& survivors p ws else survivors p ws

def separates (ws : List Mask) : Bool := positives.all fun p => survivors p ws == 0

theorem survivor_spec (ws : List Mask) (p n : Nat) (hn : n < 64)
    (h : (survivors p ws).getLsbD n = true) :
    target.getLsbD n = false ∧ ∀ w ∈ ws, w.getLsbD p = true → w.getLsbD n = true := by
  induction ws with
  | nil => simpa [survivors, BitVec.getLsbD_not, hn] using h
  | cons w ws ih =>
    by_cases hp : w.getLsbD p = true
    · simp only [survivors, hp, ite_true, BitVec.getLsbD_and, Bool.and_eq_true] at h
      obtain ⟨ht,hws⟩ := ih h.2
      refine ⟨ht, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact fun _ => h.1
      · exact hws z hz
    · simp only [survivors, hp, Bool.false_eq_true, ite_false] at h
      obtain ⟨ht,hws⟩ := ih h
      refine ⟨ht, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact fun hz' => (hp hz').elim
      · exact hws z hz

theorem separates_trace {k} (ws : List Mask) (t : Trace k ws.toFinset) : separates ws = true := by
  have hp : ∀ p ∈ positives, target.getLsbD p = true := by decide
  apply List.all_eq_true.mpr
  intro p hm
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  rw [show (0 : Mask).getLsbD n = false by simp]
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨neg,all⟩ := survivor_spec ws p n hn h
  obtain ⟨w,hw,wp,wn⟩ := traceDist t p n (hp p hm) neg
  rw [all w (List.mem_toFinset.mp hw) wp] at wn
  contradiction

def next (ws : List Mask) (a b c : Mask) (ka kb : Bool) : List Mask :=
  c :: ws.filter fun w => (w != a || ka) && (w != b || kb)

theorem next_eq (ws : List Mask) {s : Pool} {a b c : Mask} (hc : c ∈ s)
    (hws : ws.toFinset = insert a (insert b (s.erase c))) :
    (next ws a b c (decide (a ∈ s)) (decide (b ∈ s))).toFinset = s := by
  ext v
  have hmem : v ∈ ws ↔ v = a ∨ v = b ∨ v ≠ c ∧ v ∈ s := by
    rw [← List.mem_toFinset, hws]
    simp
  simp only [next, List.mem_toFinset, List.mem_cons, List.mem_filter, Bool.and_eq_true,
    Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, hmem]
  by_cases va : v = a <;> by_cases vb : v = b <;> by_cases vc : v = c <;> grind

def both (f : Bool → Bool) := f false && f true

theorem both_at {f : Bool → Bool} (h : both f = true) (b : Bool) : f b = true := by
  cases b <;> simp_all [both]

-- Every viable successor with the remaining gate budget must occur in the supplied list.
def closedStep (budget : Nat) (known : List Pool) (ws : List Mask) : Bool :=
  ws.all fun a => ws.all fun b => both fun op =>
    let c := combine op a b
    if ws.contains c || (c == 0 || c == full) then true else both fun ka => both fun kb =>
      let zs := next ws a b c ka kb
      if zs.toFinset.card ≤ budget && separates zs then known.contains zs.toFinset else true

theorem listedChild {s : Pool} {k budget : Nat} {known : List Pool} (t : Trace k s) (hk : k+1 ≤ budget)
    (ws : List Mask) (a b c : Mask) (op : Bool) (how : c = combine op a b) (hc : c ∈ s)
    (ca : c ≠ a) (cb : c ≠ b) (hws : ws.toFinset = insert a (insert b (s.erase c)))
    (hh : closedStep budget known ws = true) : s ∈ known := by
  have ma : a ∈ ws := List.mem_toFinset.mp (hws ▸ Finset.mem_insert_self _ _)
  have mb : b ∈ ws := List.mem_toFinset.mp (hws ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nc : c ∉ ws := by rw [← List.mem_toFinset, hws]; simp [ca,cb]
  have hn : ws.contains c = false := by simpa using nc
  have h := both_at (List.all_eq_true.mp (List.all_eq_true.mp hh a ma) b mb) op
  have non := traceNontriv t c hc
  have h₀ : (c == 0) = false := by simpa using non.1
  have h₁ : (c == full) = false := by simpa using non.2
  simp only [← how, hn, h₀, h₁, Bool.or_false, Bool.false_eq_true, ite_false] at h
  have h' := both_at (both_at h (decide (a ∈ s))) (decide (b ∈ s))
  let zs := next ws a b c (decide (a ∈ s)) (decide (b ∈ s))
  have he : zs.toFinset = s := next_eq ws hc hws
  have hsize : zs.toFinset.card ≤ budget := he ▸ (traceCard t).trans hk
  have hsep := separates_trace zs (he ▸ t)
  change (if decide (zs.toFinset.card ≤ budget) && separates zs then known.contains zs.toFinset else true) = true at h'
  have yes : (decide (zs.toFinset.card ≤ budget) && separates zs) = true :=
    by simp only [decide_eq_true hsize, hsep, Bool.and_self]
  rw [yes] at h'
  rw [← he]
  exact List.contains_iff_mem.mp h'

def impossible (budget : Nat) (s : Pool) : Prop := ∀ k ≤ budget, ¬ Trace k s

theorem closeState {budget : Nat} {known : List Pool} (ws : List Mask) (hnt : target ∉ ws)
    (ok : closedStep budget known ws = true)
    (ih : ∀ s ∈ known, impossible (budget-1) s) : impossible budget ws.toFinset := by
  suffices ∀ {k s}, Trace k s → k ≤ budget → ws.toFinset = s → False by
    exact fun k hk tr => this tr hk rfl
  intro k s tr hk he
  cases k with
  | zero =>
    change s = {target} at tr
    exact hnt (List.mem_toFinset.mp ((he.trans tr) ▸ Finset.mem_singleton_self _))
  | succ k =>
    obtain ⟨ss,c,a,b,op,hc,ha,hb,hab,ca,cb,how,tt,rfl⟩ := tr
    have hs := listedChild tt hk ws a b c op how hc ca cb he ok
    exact ih _ hs _ (by omega) tt

theorem nilbad (k : Nat) : ∀ t ∈ ([] : List Pool), impossible k t := by simp

theorem consbad {k : Nat} {s : Pool} {ss : List Pool} (h : impossible k s)
    (hs : ∀ t ∈ ss, impossible k t) : ∀ t ∈ s :: ss, impossible k t := by
  intro t ht
  exact (List.mem_cons.mp ht).elim (fun he => he ▸ h) (hs t)


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
def w0 : List Mask := [12297829382472990720,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n0 : impossible 5 w0.toFinset :=
  closeState (known := []) w0 (by decide) (by decide +kernel) (nilbad 4)

def w1 : List Mask := [12297829382473034410,14757395258954271744,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n1 : impossible 5 w1.toFinset :=
  closeState (known := []) w1 (by decide) (by decide +kernel) (nilbad 4)

def w2 : List Mask := [12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720]
theorem n2 : impossible 5 w2.toFinset :=
  closeState (known := []) w2 (by decide) (by decide +kernel) (nilbad 4)

def w3 : List Mask := [12297829382473034410,14757395258967641292,17361640450346250240,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n3 : impossible 5 w3.toFinset :=
  closeState (known := []) w3 (by decide) (by decide +kernel) (nilbad 4)

def w4 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18084767257870336000,18374966859414961920,18446744069414584320]
theorem n4 : impossible 5 w4.toFinset :=
  closeState (known := []) w4 (by decide) (by decide +kernel) (nilbad 4)

def w5 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18158790778715962368,18446462603027742720,18446744069414584320]
theorem n5 : impossible 5 w5.toFinset :=
  closeState (known := []) w5 (by decide) (by decide +kernel) (nilbad 4)

def w6 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072277852160]
theorem n6 : impossible 5 w6.toFinset :=
  closeState (known := []) w6 (by decide) (by decide +kernel) (nilbad 4)

def w7 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072837188608]
theorem n7 : impossible 5 w7.toFinset :=
  closeState (known := []) w7 (by decide) (by decide +kernel) (nilbad 4)

def w8 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073441177600]
theorem n8 : impossible 5 w8.toFinset :=
  closeState (known := []) w8 (by decide) (by decide +kernel) (nilbad 4)

def w9 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073456844800]
theorem n9 : impossible 5 w9.toFinset :=
  closeState (known := []) w9 (by decide) (by decide +kernel) (nilbad 4)

def w10 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400]
theorem n10 : impossible 5 w10.toFinset :=
  closeState (known := []) w10 (by decide) (by decide +kernel) (nilbad 4)

def w11 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446650250148904960,18446744069414584320]
theorem n11 : impossible 5 w11.toFinset :=
  closeState (known := []) w11 (by decide) (by decide +kernel) (nilbad 4)

def w12 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446686903399861248,18446744069414584320]
theorem n12 : impossible 5 w12.toFinset :=
  closeState (known := []) w12 (by decide) (by decide +kernel) (nilbad 4)

def w13 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446687779573137408,18446744069414584320]
theorem n13 : impossible 5 w13.toFinset :=
  closeState (known := []) w13 (by decide) (by decide +kernel) (nilbad 4)

def w14 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744069414584320]
theorem n14 : impossible 5 w14.toFinset :=
  closeState (known := []) w14 (by decide) (by decide +kernel) (nilbad 4)

def w15 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446742978492825600,18446744069414584320]
theorem n15 : impossible 5 w15.toFinset :=
  closeState (known := []) w15 (by decide) (by decide +kernel) (nilbad 4)

def w16 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18422817605466914560,18446462603027742720,18446744069414584320]
theorem n16 : impossible 5 w16.toFinset :=
  closeState (known := []) w16 (by decide) (by decide +kernel) (nilbad 4)

def w17 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18422818335600213760,18446462603027742720,18446744069414584320]
theorem n17 : impossible 5 w17.toFinset :=
  closeState (known := []) w17 (by decide) (by decide +kernel) (nilbad 4)

def w18 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18432388630837264128,18446462603027742720,18446744069414584320]
theorem n18 : impossible 5 w18.toFinset :=
  closeState (known := []) w18 (by decide) (by decide +kernel) (nilbad 4)

def w19 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18442520853841248000,18446462603027742720,18446744069414584320]
theorem n19 : impossible 5 w19.toFinset :=
  closeState (known := []) w19 (by decide) (by decide +kernel) (nilbad 4)

def w20 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18446462603027742720,18446742978476179200,18446744069414584320]
theorem n20 : impossible 5 w20.toFinset :=
  closeState (known := []) w20 (by decide) (by decide +kernel) (nilbad 4)

def w21 : List Mask := [12297829382473034410,14757395258967641292,17940362863843014904,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n21 : impossible 5 w21.toFinset :=
  closeState (known := []) w21 (by decide) (by decide +kernel) (nilbad 4)

def w22 : List Mask := [12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n22 : impossible 5 w22.toFinset :=
  closeState (known := []) w22 (by decide) (by decide +kernel) (nilbad 4)

def w23 : List Mask := [12297829382473034410,14757395258967641292,18085043209350738160,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n23 : impossible 5 w23.toFinset :=
  closeState (known := []) w23 (by decide) (by decide +kernel) (nilbad 4)

def w24 : List Mask := [12297829382473034410,14757395258967641292,18226345803934399728,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n24 : impossible 5 w24.toFinset :=
  closeState (known := []) w24 (by decide) (by decide +kernel) (nilbad 4)

def w25 : List Mask := [12297829382473034410,14757395258967641292,18229723554993205488,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n25 : impossible 5 w25.toFinset :=
  closeState (known := []) w25 (by decide) (by decide +kernel) (nilbad 4)

def w26 : List Mask := [12297829382473034410,17072280789786094828,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n26 : impossible 5 w26.toFinset :=
  closeState (known := []) w26 (by decide) (by decide +kernel) (nilbad 4)

def w27 : List Mask := [12297829382473034410,17216923606038006988,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n27 : impossible 5 w27.toFinset :=
  closeState (known := []) w27 (by decide) (by decide +kernel) (nilbad 4)

def w28 : List Mask := [12297829382473034410,17216961134889585868,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n28 : impossible 5 w28.toFinset :=
  closeState (known := []) w28 (by decide) (by decide +kernel) (nilbad 4)

def w29 : List Mask := [12297829382473034410,17361641481138401520,18216212550151634124,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n29 : impossible 5 w29.toFinset :=
  closeState (known := []) w29 (by decide) (by decide +kernel) (nilbad 4)

def w30 : List Mask := [12297829382473034410,17361641481138401520,18229670572478745804,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n30 : impossible 5 w30.toFinset :=
  closeState (known := []) w30 (by decide) (by decide +kernel) (nilbad 4)

def w31 : List Mask := [14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n31 : impossible 5 w31.toFinset :=
  closeState (known := []) w31 (by decide) (by decide +kernel) (nilbad 4)

def w32 : List Mask := [14757395258967641292,17197820544983690922,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n32 : impossible 5 w32.toFinset :=
  closeState (known := []) w32 (by decide) (by decide +kernel) (nilbad 4)

def w33 : List Mask := [14757395258967641292,17216961134316923562,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n33 : impossible 5 w33.toFinset :=
  closeState (known := []) w33 (by decide) (by decide +kernel) (nilbad 4)

def w34 : List Mask := [14757395258967641292,17361641481138401520,18062524867779689130,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n34 : impossible 5 w34.toFinset :=
  closeState (known := []) w34 (by decide) (by decide +kernel) (nilbad 4)

def w35 : List Mask := [14757395258967641292,17361641481138401520,18084954904991541930,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n35 : impossible 5 w35.toFinset :=
  closeState (known := []) w35 (by decide) (by decide +kernel) (nilbad 4)

def w36 : List Mask := [9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n36 : impossible 6 w36.toFinset :=
  closeState (known := [w21.toFinset]) w36 (by decide) (by decide +kernel) (consbad n21 (nilbad 5))

def w37 : List Mask := [11574427654092267680,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n37 : impossible 6 w37.toFinset :=
  closeState (known := [w26.toFinset]) w37 (by decide) (by decide +kernel) (consbad n26 (nilbad 5))

def w38 : List Mask := [12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n38 : impossible 6 w38.toFinset :=
  closeState (known := []) w38 (by decide) (by decide +kernel) (nilbad 5)

def w39 : List Mask := [12297641735351828480,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n39 : impossible 6 w39.toFinset :=
  closeState (known := [w6.toFinset, w16.toFinset, w22.toFinset, w27.toFinset]) w39 (by decide) (by decide +kernel) (consbad n6 (consbad n16 (consbad n22 (consbad n27 (nilbad 5)))))

def w40 : List Mask := [12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n40 : impossible 6 w40.toFinset :=
  closeState (known := [w11.toFinset, w17.toFinset, w23.toFinset, w28.toFinset]) w40 (by decide) (by decide +kernel) (consbad n11 (consbad n17 (consbad n23 (consbad n28 (nilbad 5)))))

def w41 : List Mask := [12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n41 : impossible 6 w41.toFinset :=
  closeState (known := [w31.toFinset]) w41 (by decide) (by decide +kernel) (consbad n31 (nilbad 5))

def w42 : List Mask := [12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n42 : impossible 6 w42.toFinset :=
  closeState (known := [w7.toFinset, w12.toFinset, w24.toFinset, w32.toFinset]) w42 (by decide) (by decide +kernel) (consbad n7 (consbad n12 (consbad n24 (consbad n32 (nilbad 5)))))

def w43 : List Mask := [12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n43 : impossible 6 w43.toFinset :=
  closeState (known := []) w43 (by decide) (by decide +kernel) (nilbad 5)

def w44 : List Mask := [12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n44 : impossible 6 w44.toFinset :=
  closeState (known := [w13.toFinset, w18.toFinset, w25.toFinset, w33.toFinset]) w44 (by decide) (by decide +kernel) (consbad n13 (consbad n18 (consbad n25 (consbad n33 (nilbad 5)))))

def w45 : List Mask := [12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n45 : impossible 6 w45.toFinset :=
  closeState (known := [w2.toFinset]) w45 (by decide) (by decide +kernel) (consbad n2 (nilbad 5))

def w46 : List Mask := [12297829382473034410,14757395258967641292,17294086455919964160,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n46 : impossible 6 w46.toFinset :=
  closeState (known := [w8.toFinset, w14.toFinset, w29.toFinset, w34.toFinset]) w46 (by decide) (by decide +kernel) (consbad n8 (consbad n14 (consbad n29 (consbad n34 (nilbad 5)))))

def w47 : List Mask := [12297829382473034410,14757395258967641292,17361376567555522560,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n47 : impossible 6 w47.toFinset :=
  closeState (known := [w9.toFinset, w19.toFinset, w30.toFinset, w35.toFinset]) w47 (by decide) (by decide +kernel) (consbad n9 (consbad n19 (consbad n30 (consbad n35 (nilbad 5)))))

def w48 : List Mask := [12297829382473034410,14757395258967641292,17361641477096079360,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n48 : impossible 6 w48.toFinset :=
  closeState (known := []) w48 (by decide) (by decide +kernel) (nilbad 5)

def w49 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18085043209519168250,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n49 : impossible 6 w49.toFinset :=
  closeState (known := [w4.toFinset]) w49 (by decide) (by decide +kernel) (consbad n4 (nilbad 5))

def w50 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n50 : impossible 6 w50.toFinset :=
  closeState (known := [w5.toFinset]) w50 (by decide) (by decide +kernel) (consbad n5 (nilbad 5))

def w51 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n51 : impossible 6 w51.toFinset :=
  closeState (known := [w10.toFinset]) w51 (by decide) (by decide +kernel) (consbad n10 (nilbad 5))

def w52 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n52 : impossible 6 w52.toFinset :=
  closeState (known := [w15.toFinset]) w52 (by decide) (by decide +kernel) (consbad n15 (nilbad 5))

def w53 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720,18446744069414584320]
theorem n53 : impossible 6 w53.toFinset :=
  closeState (known := []) w53 (by decide) (by decide +kernel) (nilbad 5)

def w54 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320]
theorem n54 : impossible 6 w54.toFinset :=
  closeState (known := []) w54 (by decide) (by decide +kernel) (nilbad 5)

def w55 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720,18446744069414584320]
theorem n55 : impossible 6 w55.toFinset :=
  closeState (known := []) w55 (by decide) (by decide +kernel) (nilbad 5)

def w56 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462598732840960,18446462603027742720,18446744069414584320]
theorem n56 : impossible 6 w56.toFinset :=
  closeState (known := [w20.toFinset]) w56 (by decide) (by decide +kernel) (consbad n20 (nilbad 5))

def w57 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446650250148948650,18446744069414584320]
theorem n57 : impossible 6 w57.toFinset :=
  closeState (known := []) w57 (by decide) (by decide +kernel) (nilbad 5)

def w58 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446687779573189836,18446744069414584320]
theorem n58 : impossible 6 w58.toFinset :=
  closeState (known := []) w58 (by decide) (by decide +kernel) (nilbad 5)

def w59 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320]
theorem n59 : impossible 6 w59.toFinset :=
  closeState (known := []) w59 (by decide) (by decide +kernel) (nilbad 5)

def w60 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880,18446744069414584320]
theorem n60 : impossible 6 w60.toFinset :=
  closeState (known := [w3.toFinset]) w60 (by decide) (by decide +kernel) (consbad n3 (nilbad 5))

def w61 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072277895850]
theorem n61 : impossible 6 w61.toFinset :=
  closeState (known := []) w61 (by decide) (by decide +kernel) (nilbad 5)

def w62 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850558156]
theorem n62 : impossible 6 w62.toFinset :=
  closeState (known := []) w62 (by decide) (by decide +kernel) (nilbad 5)

def w63 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073456906480]
theorem n63 : impossible 6 w63.toFinset :=
  closeState (known := []) w63 (by decide) (by decide +kernel) (nilbad 5)

def w64 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680]
theorem n64 : impossible 6 w64.toFinset :=
  closeState (known := [w1.toFinset]) w64 (by decide) (by decide +kernel) (consbad n1 (nilbad 5))

def w65 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073709486080]
theorem n65 : impossible 6 w65.toFinset :=
  closeState (known := [w0.toFinset]) w65 (by decide) (by decide +kernel) (consbad n0 (nilbad 5))

def w66 : List Mask := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
theorem n66 : impossible 7 w66.toFinset :=
  closeState (known := [w36.toFinset, w37.toFinset, w38.toFinset, w39.toFinset, w40.toFinset, w41.toFinset, w42.toFinset, w43.toFinset, w44.toFinset, w45.toFinset, w46.toFinset, w47.toFinset, w48.toFinset, w49.toFinset, w50.toFinset, w51.toFinset, w52.toFinset, w53.toFinset, w54.toFinset, w55.toFinset, w56.toFinset, w57.toFinset, w58.toFinset, w59.toFinset, w60.toFinset, w61.toFinset, w62.toFinset, w63.toFinset, w64.toFinset, w65.toFinset]) w66 (by decide) (by decide +kernel) (consbad n36 (consbad n37 (consbad n38 (consbad n39 (consbad n40 (consbad n41 (consbad n42 (consbad n43 (consbad n44 (consbad n45 (consbad n46 (consbad n47 (consbad n48 (consbad n49 (consbad n50 (consbad n51 (consbad n52 (consbad n53 (consbad n54 (consbad n55 (consbad n56 (consbad n57 (consbad n58 (consbad n59 (consbad n60 (consbad n61 (consbad n62 (consbad n63 (consbad n64 (consbad n65 (nilbad 6)))))))))))))))))))))))))))))))

theorem lower (C : Circuit) (hm : Monotone2 C) (hC : computes C) : 8 ≤ C.size := by
  by_contra! hsmall
  obtain ⟨k,hk,S,hs,ht⟩ := extract C.gates pins C.output (desiredMask hm hC)
  have hlo : k ≤ 7 := by change C.gates.length < 8 at hsmall; omega
  have hroot : rootsOK 7 [w66.toFinset] = true := by decide +kernel
  have hn : ∀ v ∈ [w66.toFinset], impossible 7 v := (consbad n66 (nilbad 7))
  exact hn S (rootKnown hlo hs ht hroot) k hlo ht

def witness : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[1,2]⟩, ⟨.and,[6,5]⟩, ⟨.and,[7,4]⟩, ⟨.or,[9,10]⟩, ⟨.and,[8,3]⟩, ⟨.or,[12,11]⟩],13⟩

theorem witnessSize : witness.size = 8 := rfl

def isAnd (op : GateOp) : Bool := match op with | .and => true | _ => false

theorem witnessMono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp

theorem witnessBack : ReadsBack 6 witness := by
  have hr : ∀ j : Fin 8, ∀ i ∈ (gateAt witness j.val).inputs, i < 6+j.val := by decide +kernel
  intro j hj
  exact hr ⟨j,hj⟩

theorem witnessComputes : computes witness := by
  unfold computes incidence
  decide +kernel

theorem witnessClean : ∀ j < witness.gates.length, (gateAt witness j).op = GateOp.and →
    ∀ v : Fin 6, (witness.wires (List.ofFn fun i : Fin 6 => decide (i = v))).getD (6+j) false = false := by
  have hc : ∀ j : Fin 8, isAnd (gateAt witness j.val).op = true →
      ∀ v : Fin 6, (witness.wires (List.ofFn fun i : Fin 6 => decide (i = v))).getD (6+j.val) false = false := by decide +kernel
  intro j hj hop
  exact hc ⟨j,hj⟩ (hop ▸ rfl)

theorem cycleNormalized (C : Circuit) (hm : Monotone2 C) (hC : computes C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 6 D ∧ D.size ≤ C.size ∧ computes D ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ v : Fin 6, (D.wires (List.ofFn fun i : Fin 6 => decide (i = v))).getD (6+j) false = false := by
  exact ⟨witness, witnessMono, witnessBack, lower C hm hC, witnessComputes, witnessClean⟩

end CycleSingletonAND
