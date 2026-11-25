import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto
import PEqualNP.Defs.TopForm
import PEqualNP.Defs.MetaComplexityLgpMono

/-!
The four-vertex path has an optimum exact fan-in-two circuit of four gates. Its
edge function also has a five-gate circuit that is top-stuck and fails the
two-level condition. This exhibits the effect of allowing a single extra gate in
the structure conjecture for four-cycle-free bipartite graphs.
-/

namespace PathFourTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev Mask := BitVec 16
abbrev Pool := Finset Mask

def target : Mask := 60128
def full : Mask := BitVec.allOnes 16
def pins : List Mask := [43690, 52428, 61680, 65280]

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

theorem gateBits (ws : List Mask) {g : Gate} (hg : legal g) (r : Nat) (hr : r < 16) :
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

theorem runBits (gs : List Gate) (h : ∀ g ∈ gs, legal g) (ws : List Mask) (r : Nat) (hr : r < 16) :
    (gs.foldl applyGate ws).map (readBit r) =
      gs.foldl (fun bs g => bs ++ [g.op.eval (g.inputs.map fun i => bs.getD i false)]) (ws.map (readBit r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
    simp [applyGate, gateBits ws (h g (by simp)) r hr]

def incidence (p l : Fin 2) : Prop := (7 : Nat).testBit (2*p.val+l.val) = true

theorem noFourCycle : ∀ p q l m : Fin 2, p ≠ q → l ≠ m →
    ¬ (incidence p l ∧ incidence p m ∧ incidence q l ∧ incidence q m) := by
  unfold incidence
  decide +kernel

def computes (C : Circuit) : Prop :=
  ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
    ∃ p l : Fin 2, incidence p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true

theorem desiredMask {C : Circuit} (hm : Monotone2 C) (hc : computes C) :
    (C.gates.foldl applyGate pins).getD C.output 0 = target := by
  have hlegal : ∀ g ∈ C.gates, legal g := fun g hg => hm g hg
  have hp : ∀ r : Fin 16, pins.map (readBit r.val) = List.ofFn (fun i : Fin 4 => r.val.testBit i.val) := by decide +kernel
  have ht : ∀ r : Fin 16, readBit r.val target = true ↔ ∃ p l : Fin 2,
      (7 : Nat).testBit (2*p.val+l.val) = true ∧ r.val.testBit (Fin.castAdd 2 p).val = true ∧
      r.val.testBit (Fin.natAdd 2 l).val = true := by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  change readBit r _ = readBit r _
  rw [← atWire, runBits C.gates hlegal pins r hr, hp ⟨r,hr⟩]
  exact Bool.eq_iff_iff.mpr ((hc _).trans (ht ⟨r,hr⟩).symm)

def nontriv (a : Mask) : Prop := a ≠ 0 ∧ a ≠ full

-- Each 16-bit word gives the values of a wire on all assignments to the four vertex inputs.
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
def positives : List Nat := [5, 6, 9]

def survivors (p : Nat) : List Mask → Mask
  | [] => ~~~target
  | w :: ws => if w.getLsbD p then w &&& survivors p ws else survivors p ws

def separates (ws : List Mask) : Bool := positives.all fun p => survivors p ws == 0

theorem survivor_spec (ws : List Mask) (p n : Nat) (hn : n < 16)
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

def inputState : List Mask := [43690, 52428, 61680, 65280]

theorem noThree : impossible 3 inputState.toFinset :=
  closeState (known := []) inputState (by decide) (by decide +kernel) (nilbad 2)

theorem lower (C : Circuit) (hm : Monotone2 C) (hC : computes C) : 4 ≤ C.size := by
  by_contra! hsmall
  obtain ⟨k,hk,S,hs,ht⟩ := extract C.gates pins C.output (desiredMask hm hC)
  have hlo : k ≤ 3 := by change C.gates.length < 4 at hsmall; omega
  have ok : rootsOK 3 [inputState.toFinset] = true := by decide +kernel
  have he : S = inputState.toFinset := by simpa using rootKnown hlo hs ht ok
  exact noThree k hlo (he ▸ ht)

def best : Circuit := ⟨[⟨.or,[2,3]⟩, ⟨.and,[0,4]⟩, ⟨.and,[1,2]⟩, ⟨.or,[5,6]⟩],7⟩

-- The three OR gates compute the prime clauses of the path's edge function.
def clauses : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[2,3]⟩, ⟨.or,[0,2]⟩, ⟨.and,[4,5]⟩, ⟨.and,[7,6]⟩],8⟩

def hit (z : Fin 4 → Bool) : Prop :=
  ∃ p l : Fin 2, incidence p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true

def topStuck (C : Circuit) : Prop :=
  ∃ T : Finset Nat, (∀ i ∈ T, i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      (4+i = C.output ∨ ∃ k ∈ T, ∀ j < C.gates.length, (4+i ∈ (gateAt C j).inputs ↔ j = k))) ∧
    ∀ w : Nat, (∀ z : Fin 4 → Bool, (C.wires (List.ofFn z)).getD w false = true → hit z) →
      (∃ k < C.gates.length, (gateAt C k).op = GateOp.or ∧ w ∈ (gateAt C k).inputs) →
      ∀ k < C.gates.length, w ∈ (gateAt C k).inputs → k ∈ T

def twoLevel (C : Circuit) : Prop :=
  ∃ P L : Finset Nat, (∀ w ∈ P, w < 2 ∨ ∃ i < C.gates.length, w = 4+i ∧
       (gateAt C i).op = GateOp.or ∧ ∀ u ∈ (gateAt C i).inputs, u ∈ P) ∧
    (∀ w ∈ L, (2 ≤ w ∧ w < 4) ∨ ∃ i < C.gates.length, w = 4+i ∧
       (gateAt C i).op = GateOp.or ∧ ∀ u ∈ (gateAt C i).inputs, u ∈ L) ∧
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and →
      ∃ a b, (gateAt C i).inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))

def isOr (op : GateOp) : Bool := match op with | .or => true | _ => false

theorem clausesStuck : topStuck clauses := by
  refine ⟨∅, by simp, ?_⟩
  intro w hbelow hread
  have hIn : ∀ j : Fin 5, isOr (gateAt clauses j.val).op = true →
      ∀ w ∈ (gateAt clauses j.val).inputs, w < 4 := by decide +kernel
  obtain ⟨j,hj,hop,hw⟩ := hread
  have hi : w < 4 := hIn ⟨j,hj⟩ (hop ▸ rfl) w hw
  have hx : ∀ v : Fin 4, (clauses.wires (List.ofFn fun i : Fin 4 => decide (i = v))).getD v.val false = true := by decide +kernel
  have hy : ∀ v : Fin 4, ¬ hit (fun i => decide (i = v)) := by unfold hit incidence; decide +kernel
  exact (hy ⟨w,hi⟩ (hbelow _ (hx ⟨w,hi⟩))).elim

theorem clausesNotTwoLevel : ¬ twoLevel clauses := by
  rintro ⟨P,L,hP,hL,hh⟩
  have mixed {U : Finset Nat} (h : ∀ u ∈ U, u < 4 ∨ ∃ i < clauses.gates.length,
      u = 4+i ∧ (gateAt clauses i).op = GateOp.or ∧ ∀ a ∈ (gateAt clauses i).inputs, a ∈ U) : 7 ∉ U := by
    intro hu
    rcases h 7 hu with h | ⟨i,_,hi,hop,_⟩
    · omega
    · obtain rfl : i = 3 := by omega
      change GateOp.and = GateOp.or at hop
      contradiction
  have np : 7 ∉ P := mixed (fun w hw => (hP w hw).imp (fun h => by omega) id)
  have nl : 7 ∉ L := mixed (fun w hw => (hL w hw).imp And.right id)
  obtain ⟨a,b,hab,roles⟩ := hh 4 (by decide) rfl
  change [7,6] = [a,b] at hab
  obtain rfl : a = 7 := (List.cons.inj hab).1.symm
  exact roles.elim (fun h => np h.1) (fun h => nl h.1)

theorem sharpness :
    PEqualNP.TopForm.IsAO2 4 best ∧ PEqualNP.TopForm.IsAO2 4 clauses ∧ computes best ∧ computes clauses ∧
    (∀ D : Circuit, PEqualNP.TopForm.IsAO2 4 D → computes D → best.size ≤ D.size) ∧
    clauses.size = best.size + 1 ∧ topStuck clauses ∧ ¬ twoLevel clauses := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_, ?_, rfl, clausesStuck, clausesNotTwoLevel⟩
  · unfold computes incidence; decide +kernel
  · unfold computes incidence; decide +kernel
  · intro D hD hfun
    apply lower D _ hfun
    intro g hg
    exact ⟨hD.1 g hg, (hD.2.2 g hg).le⟩

end PathFourTopForm
