import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5982

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Mask := BitVec 16
abbrev Pool := Finset Mask

def target : Mask := 4459
def full : Mask := BitVec.allOnes 16
def pins : List Mask := [15,240,3840,61440,4369,8738,17476,34952]

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

theorem desiredMask {C : Circuit} (hm : Monotone2 C)
    (hc : Represents (fun u v : Fin 4 => (4459 : Nat).testBit (4*u.val+v.val)) C) :
    (C.gates.foldl applyGate pins).getD C.output 0 = target := by
  have hlegal : ∀ g ∈ C.gates, legal g := fun g hg => hm g hg
  have hp : ∀ u v : Fin 4, pins.map (readBit (4*u.val+v.val)) = oneEach u v := by decide +kernel
  have ht : ∀ u v : Fin 4, readBit (4*u.val+v.val) target = (4459 : Nat).testBit (4*u.val+v.val) := by decide
  have hi : ∀ j : Fin 16, ∃ u v : Fin 4, 4*u.val+v.val = j.val := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  obtain ⟨u,v,e⟩ := hi ⟨r,hr⟩
  change 4*u.val+v.val = r at e
  change readBit r _ = readBit r _
  rw [← atWire, runBits C.gates hlegal pins r hr, ← e, hp, ht]
  exact hc u v

def nontriv (a : Mask) : Prop := a ≠ 0 ∧ a ≠ full

-- Each sixteen-bit word gives the values of a wire on the sixteen graph entries.
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
def positives : List Nat := [0,1,3,5,6,8,12]

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


-- Wires 10, 12 and 14 implement the three distinct row neighbourhoods.
def upperCircuit : Circuit :=
  ⟨[⟨.or,[4,5]⟩, ⟨.or,[8,7]⟩, ⟨.and,[0,9]⟩,
    ⟨.or,[5,6]⟩, ⟨.and,[1,11]⟩, ⟨.or,[2,3]⟩, ⟨.and,[13,4]⟩,
    ⟨.or,[10,12]⟩, ⟨.or,[15,14]⟩], 16⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨upperCircuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [upperCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp
  · decide +kernel


def w0 : List Mask := [15,13154,39417]
theorem n0 : impossible 2 w0.toFinset :=
  closeState (known := []) w0 (by decide) (by decide +kernel) (nilbad 1)

def w1 : List Mask := [4431,8738,39417]
theorem n1 : impossible 2 w1.toFinset :=
  closeState (known := []) w1 (by decide) (by decide +kernel) (nilbad 1)

def w2 : List Mask := [8738,21839,39417]
theorem n2 : impossible 2 w2.toFinset :=
  closeState (known := []) w2 (by decide) (by decide +kernel) (nilbad 1)

def w3 : List Mask := [13090,17487,39417]
theorem n3 : impossible 2 w3.toFinset :=
  closeState (known := []) w3 (by decide) (by decide +kernel) (nilbad 1)

def w4 : List Mask := [15,96,4369,65450]
theorem n4 : impossible 3 w4.toFinset :=
  closeState (known := []) w4 (by decide) (by decide +kernel) (nilbad 2)

def w5 : List Mask := [15,4416,8738,39417]
theorem n5 : impossible 3 w5.toFinset :=
  closeState (known := [w0.toFinset, w1.toFinset]) w5 (by decide) (by decide +kernel) (consbad n0 (consbad n1 (nilbad 2)))

def w6 : List Mask := [15,4593,8746,65348]
theorem n6 : impossible 3 w6.toFinset :=
  closeState (known := []) w6 (by decide) (by decide +kernel) (nilbad 2)

def w7 : List Mask := [15,4593,12074,62532]
theorem n7 : impossible 3 w7.toFinset :=
  closeState (known := []) w7 (by decide) (by decide +kernel) (nilbad 2)

def w8 : List Mask := [15,4593,13154,34952]
theorem n8 : impossible 3 w8.toFinset :=
  closeState (known := [w0.toFinset]) w8 (by decide) (by decide +kernel) (consbad n0 (nilbad 2))

def w9 : List Mask := [15,4593,16226,34952]
theorem n9 : impossible 3 w9.toFinset :=
  closeState (known := []) w9 (by decide) (by decide +kernel) (nilbad 2)

def w10 : List Mask := [15,4593,17476,65322]
theorem n10 : impossible 3 w10.toFinset :=
  closeState (known := []) w10 (by decide) (by decide +kernel) (nilbad 2)

def w11 : List Mask := [15,4593,20292,61994]
theorem n11 : impossible 3 w11.toFinset :=
  closeState (known := []) w11 (by decide) (by decide +kernel) (nilbad 2)

def w12 : List Mask := [15,4593,34952,62306]
theorem n12 : impossible 3 w12.toFinset :=
  closeState (known := []) w12 (by decide) (by decide +kernel) (nilbad 2)

def w13 : List Mask := [15,4593,34952,65378]
theorem n13 : impossible 3 w13.toFinset :=
  closeState (known := []) w13 (by decide) (by decide +kernel) (nilbad 2)

def w14 : List Mask := [15,4593,43690,65382]
theorem n14 : impossible 3 w14.toFinset :=
  closeState (known := []) w14 (by decide) (by decide +kernel) (nilbad 2)

def w15 : List Mask := [15,4593,44970,65382]
theorem n15 : impossible 3 w15.toFinset :=
  closeState (known := []) w15 (by decide) (by decide +kernel) (nilbad 2)

def w16 : List Mask := [15,4593,64170,65382]
theorem n16 : impossible 3 w16.toFinset :=
  closeState (known := []) w16 (by decide) (by decide +kernel) (nilbad 2)

def w17 : List Mask := [15,4593,65382,65450]
theorem n17 : impossible 3 w17.toFinset :=
  closeState (known := []) w17 (by decide) (by decide +kernel) (nilbad 2)

def w18 : List Mask := [15,4601,8738,65348]
theorem n18 : impossible 3 w18.toFinset :=
  closeState (known := []) w18 (by decide) (by decide +kernel) (nilbad 2)

def w19 : List Mask := [15,4601,12066,62532]
theorem n19 : impossible 3 w19.toFinset :=
  closeState (known := []) w19 (by decide) (by decide +kernel) (nilbad 2)

def w20 : List Mask := [15,4601,17476,65314]
theorem n20 : impossible 3 w20.toFinset :=
  closeState (known := []) w20 (by decide) (by decide +kernel) (nilbad 2)

def w21 : List Mask := [15,4601,20292,61986]
theorem n21 : impossible 3 w21.toFinset :=
  closeState (known := []) w21 (by decide) (by decide +kernel) (nilbad 2)

def w22 : List Mask := [15,8738,21828,39417]
theorem n22 : impossible 3 w22.toFinset :=
  closeState (known := [w2.toFinset]) w22 (by decide) (by decide +kernel) (consbad n2 (nilbad 2))

def w23 : List Mask := [15,13090,17476,39417]
theorem n23 : impossible 3 w23.toFinset :=
  closeState (known := [w3.toFinset]) w23 (by decide) (by decide +kernel) (consbad n3 (nilbad 2))

def w24 : List Mask := [79,4593,34952,65314]
theorem n24 : impossible 3 w24.toFinset :=
  closeState (known := []) w24 (by decide) (by decide +kernel) (nilbad 2)

def w25 : List Mask := [240,8738,21839,39321]
theorem n25 : impossible 3 w25.toFinset :=
  closeState (known := [w2.toFinset]) w25 (by decide) (by decide +kernel) (consbad n2 (nilbad 2))

def w26 : List Mask := [240,13090,17487,39321]
theorem n26 : impossible 3 w26.toFinset :=
  closeState (known := [w3.toFinset]) w26 (by decide) (by decide +kernel) (consbad n3 (nilbad 2))

def w27 : List Mask := [335,4593,34952,61986]
theorem n27 : impossible 3 w27.toFinset :=
  closeState (known := []) w27 (by decide) (by decide +kernel) (nilbad 2)

def w28 : List Mask := [4175,4593,12066,34952]
theorem n28 : impossible 3 w28.toFinset :=
  closeState (known := []) w28 (by decide) (by decide +kernel) (nilbad 2)

def w29 : List Mask := [4352,8738,17487,39417]
theorem n29 : impossible 3 w29.toFinset :=
  closeState (known := [w2.toFinset, w3.toFinset]) w29 (by decide) (by decide +kernel) (consbad n2 (consbad n3 (nilbad 2)))

def w30 : List Mask := [4353,8738,17487,35064]
theorem n30 : impossible 3 w30.toFinset :=
  closeState (known := []) w30 (by decide) (by decide +kernel) (nilbad 2)

def w31 : List Mask := [4367,8738,17476,39417]
theorem n31 : impossible 3 w31.toFinset :=
  closeState (known := [w2.toFinset]) w31 (by decide) (by decide +kernel) (consbad n2 (nilbad 2))

def w32 : List Mask := [4369,8738,21839,35064]
theorem n32 : impossible 3 w32.toFinset :=
  closeState (known := [w2.toFinset]) w32 (by decide) (by decide +kernel) (consbad n2 (nilbad 2))

def w33 : List Mask := [4369,13090,17487,35064]
theorem n33 : impossible 3 w33.toFinset :=
  closeState (known := [w3.toFinset]) w33 (by decide) (by decide +kernel) (consbad n3 (nilbad 2))

def w34 : List Mask := [4431,4593,8738,34952]
theorem n34 : impossible 3 w34.toFinset :=
  closeState (known := [w1.toFinset]) w34 (by decide) (by decide +kernel) (consbad n1 (nilbad 2))

def w35 : List Mask := [4593,8738,21839,34952]
theorem n35 : impossible 3 w35.toFinset :=
  closeState (known := [w2.toFinset]) w35 (by decide) (by decide +kernel) (consbad n2 (nilbad 2))

def w36 : List Mask := [4593,8746,17487,65280]
theorem n36 : impossible 3 w36.toFinset :=
  closeState (known := []) w36 (by decide) (by decide +kernel) (nilbad 2)

def w37 : List Mask := [4593,13090,17487,34952]
theorem n37 : impossible 3 w37.toFinset :=
  closeState (known := [w3.toFinset]) w37 (by decide) (by decide +kernel) (consbad n3 (nilbad 2))

def w38 : List Mask := [4593,17487,43690,65314]
theorem n38 : impossible 3 w38.toFinset :=
  closeState (known := []) w38 (by decide) (by decide +kernel) (nilbad 2)

def w39 : List Mask := [4601,8738,17487,65280]
theorem n39 : impossible 3 w39.toFinset :=
  closeState (known := []) w39 (by decide) (by decide +kernel) (nilbad 2)

def w40 : List Mask := [8,15,4593,8738,65348]
theorem n40 : impossible 4 w40.toFinset :=
  closeState (known := [w6.toFinset, w18.toFinset]) w40 (by decide) (by decide +kernel) (consbad n6 (consbad n18 (nilbad 3)))

def w41 : List Mask := [8,15,4593,12066,62532]
theorem n41 : impossible 4 w41.toFinset :=
  closeState (known := [w7.toFinset, w19.toFinset]) w41 (by decide) (by decide +kernel) (consbad n7 (consbad n19 (nilbad 3)))

def w42 : List Mask := [8,15,4593,17476,65314]
theorem n42 : impossible 4 w42.toFinset :=
  closeState (known := [w10.toFinset, w20.toFinset]) w42 (by decide) (by decide +kernel) (consbad n10 (consbad n20 (nilbad 3)))

def w43 : List Mask := [8,15,4593,20292,61986]
theorem n43 : impossible 4 w43.toFinset :=
  closeState (known := [w11.toFinset, w21.toFinset]) w43 (by decide) (by decide +kernel) (consbad n11 (consbad n21 (nilbad 3)))

def w44 : List Mask := [8,4593,8738,17487,65280]
theorem n44 : impossible 4 w44.toFinset :=
  closeState (known := [w36.toFinset, w39.toFinset]) w44 (by decide) (by decide +kernel) (consbad n36 (consbad n39 (nilbad 3)))

def w45 : List Mask := [15,64,4593,34952,65314]
theorem n45 : impossible 4 w45.toFinset :=
  closeState (known := [w13.toFinset, w24.toFinset]) w45 (by decide) (by decide +kernel) (consbad n13 (consbad n24 (nilbad 3)))

def w46 : List Mask := [15,96,3840,4369,64170]
theorem n46 : impossible 4 w46.toFinset :=
  closeState (known := [w4.toFinset]) w46 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w47 : List Mask := [15,96,4369,8738,65416]
theorem n47 : impossible 4 w47.toFinset :=
  closeState (known := [w4.toFinset]) w47 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w48 : List Mask := [15,96,4369,12066,63624]
theorem n48 : impossible 4 w48.toFinset :=
  closeState (known := [w4.toFinset]) w48 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w49 : List Mask := [15,96,4369,34952,65314]
theorem n49 : impossible 4 w49.toFinset :=
  closeState (known := [w4.toFinset]) w49 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w50 : List Mask := [15,96,4369,36744,61986]
theorem n50 : impossible 4 w50.toFinset :=
  closeState (known := [w4.toFinset]) w50 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w51 : List Mask := [15,96,4369,43690,65280]
theorem n51 : impossible 4 w51.toFinset :=
  closeState (known := [w4.toFinset]) w51 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w52 : List Mask := [15,96,4369,44970,61440]
theorem n52 : impossible 4 w52.toFinset :=
  closeState (known := [w4.toFinset]) w52 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w53 : List Mask := [15,240,4369,8746,65348]
theorem n53 : impossible 4 w53.toFinset :=
  closeState (known := [w6.toFinset]) w53 (by decide) (by decide +kernel) (consbad n6 (nilbad 3))

def w54 : List Mask := [15,240,4369,8802,65416]
theorem n54 : impossible 4 w54.toFinset :=
  closeState (known := []) w54 (by decide) (by decide +kernel) (nilbad 3)

def w55 : List Mask := [15,240,4369,12074,62532]
theorem n55 : impossible 4 w55.toFinset :=
  closeState (known := [w7.toFinset]) w55 (by decide) (by decide +kernel) (consbad n7 (nilbad 3))

def w56 : List Mask := [15,240,4369,12130,63624]
theorem n56 : impossible 4 w56.toFinset :=
  closeState (known := []) w56 (by decide) (by decide +kernel) (nilbad 3)

def w57 : List Mask := [15,240,4369,17476,65322]
theorem n57 : impossible 4 w57.toFinset :=
  closeState (known := [w10.toFinset]) w57 (by decide) (by decide +kernel) (consbad n10 (nilbad 3))

def w58 : List Mask := [15,240,4369,20292,61994]
theorem n58 : impossible 4 w58.toFinset :=
  closeState (known := [w11.toFinset]) w58 (by decide) (by decide +kernel) (consbad n11 (nilbad 3))

def w59 : List Mask := [15,240,4369,26214,65450]
theorem n59 : impossible 4 w59.toFinset :=
  closeState (known := [w4.toFinset]) w59 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w60 : List Mask := [15,240,4369,28518,64170]
theorem n60 : impossible 4 w60.toFinset :=
  closeState (known := []) w60 (by decide) (by decide +kernel) (nilbad 3)

def w61 : List Mask := [15,240,4369,28518,65450]
theorem n61 : impossible 4 w61.toFinset :=
  closeState (known := [w4.toFinset]) w61 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w62 : List Mask := [15,240,4369,34952,65378]
theorem n62 : impossible 4 w62.toFinset :=
  closeState (known := [w13.toFinset]) w62 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w63 : List Mask := [15,240,4369,36744,62050]
theorem n63 : impossible 4 w63.toFinset :=
  closeState (known := []) w63 (by decide) (by decide +kernel) (nilbad 3)

def w64 : List Mask := [15,240,4369,43690,65382]
theorem n64 : impossible 4 w64.toFinset :=
  closeState (known := [w14.toFinset]) w64 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w65 : List Mask := [15,240,4369,44970,63078]
theorem n65 : impossible 4 w65.toFinset :=
  closeState (known := []) w65 (by decide) (by decide +kernel) (nilbad 3)

def w66 : List Mask := [15,240,4369,44970,65382]
theorem n66 : impossible 4 w66.toFinset :=
  closeState (known := [w15.toFinset]) w66 (by decide) (by decide +kernel) (consbad n15 (nilbad 3))

def w67 : List Mask := [15,240,4369,63078,65450]
theorem n67 : impossible 4 w67.toFinset :=
  closeState (known := [w4.toFinset]) w67 (by decide) (by decide +kernel) (consbad n4 (nilbad 3))

def w68 : List Mask := [15,240,4369,64170,65382]
theorem n68 : impossible 4 w68.toFinset :=
  closeState (known := [w16.toFinset]) w68 (by decide) (by decide +kernel) (consbad n16 (nilbad 3))

def w69 : List Mask := [15,240,4369,65382,65450]
theorem n69 : impossible 4 w69.toFinset :=
  closeState (known := [w4.toFinset, w17.toFinset]) w69 (by decide) (by decide +kernel) (consbad n4 (consbad n17 (nilbad 3)))

def w70 : List Mask := [15,240,4377,8738,65348]
theorem n70 : impossible 4 w70.toFinset :=
  closeState (known := [w18.toFinset]) w70 (by decide) (by decide +kernel) (consbad n18 (nilbad 3))

def w71 : List Mask := [15,240,4377,12066,62532]
theorem n71 : impossible 4 w71.toFinset :=
  closeState (known := [w19.toFinset]) w71 (by decide) (by decide +kernel) (consbad n19 (nilbad 3))

def w72 : List Mask := [15,240,4377,17476,65314]
theorem n72 : impossible 4 w72.toFinset :=
  closeState (known := [w20.toFinset]) w72 (by decide) (by decide +kernel) (consbad n20 (nilbad 3))

def w73 : List Mask := [15,240,4377,20292,61986]
theorem n73 : impossible 4 w73.toFinset :=
  closeState (known := [w21.toFinset]) w73 (by decide) (by decide +kernel) (consbad n21 (nilbad 3))

def w74 : List Mask := [15,240,8738,21828,39321]
theorem n74 : impossible 4 w74.toFinset :=
  closeState (known := [w22.toFinset, w25.toFinset]) w74 (by decide) (by decide +kernel) (consbad n22 (consbad n25 (nilbad 3)))

def w75 : List Mask := [15,240,13090,17476,39321]
theorem n75 : impossible 4 w75.toFinset :=
  closeState (known := [w23.toFinset, w26.toFinset]) w75 (by decide) (by decide +kernel) (consbad n23 (consbad n26 (nilbad 3)))

def w76 : List Mask := [15,248,4369,8738,65348]
theorem n76 : impossible 4 w76.toFinset :=
  closeState (known := [w18.toFinset]) w76 (by decide) (by decide +kernel) (consbad n18 (nilbad 3))

def w77 : List Mask := [15,248,4369,12066,62532]
theorem n77 : impossible 4 w77.toFinset :=
  closeState (known := [w19.toFinset]) w77 (by decide) (by decide +kernel) (consbad n19 (nilbad 3))

def w78 : List Mask := [15,248,4369,17476,65314]
theorem n78 : impossible 4 w78.toFinset :=
  closeState (known := [w20.toFinset]) w78 (by decide) (by decide +kernel) (consbad n20 (nilbad 3))

def w79 : List Mask := [15,248,4369,20292,61986]
theorem n79 : impossible 4 w79.toFinset :=
  closeState (known := [w21.toFinset]) w79 (by decide) (by decide +kernel) (consbad n21 (nilbad 3))

def w80 : List Mask := [15,320,4593,34952,61986]
theorem n80 : impossible 4 w80.toFinset :=
  closeState (known := [w12.toFinset, w27.toFinset]) w80 (by decide) (by decide +kernel) (consbad n12 (consbad n27 (nilbad 3)))

def w81 : List Mask := [15,3840,4593,8746,62532]
theorem n81 : impossible 4 w81.toFinset :=
  closeState (known := [w6.toFinset, w7.toFinset]) w81 (by decide) (by decide +kernel) (consbad n6 (consbad n7 (nilbad 3)))

def w82 : List Mask := [15,3840,4593,12898,34952]
theorem n82 : impossible 4 w82.toFinset :=
  closeState (known := [w9.toFinset]) w82 (by decide) (by decide +kernel) (consbad n9 (nilbad 3))

def w83 : List Mask := [15,3840,4593,17476,61994]
theorem n83 : impossible 4 w83.toFinset :=
  closeState (known := [w10.toFinset, w11.toFinset]) w83 (by decide) (by decide +kernel) (consbad n10 (consbad n11 (nilbad 3)))

def w84 : List Mask := [15,3840,4593,34952,62050]
theorem n84 : impossible 4 w84.toFinset :=
  closeState (known := [w13.toFinset]) w84 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w85 : List Mask := [15,3840,4593,43690,63078]
theorem n85 : impossible 4 w85.toFinset :=
  closeState (known := [w14.toFinset]) w85 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w86 : List Mask := [15,3840,4593,63078,64170]
theorem n86 : impossible 4 w86.toFinset :=
  closeState (known := [w16.toFinset]) w86 (by decide) (by decide +kernel) (consbad n16 (nilbad 3))

def w87 : List Mask := [15,3840,4601,8738,62532]
theorem n87 : impossible 4 w87.toFinset :=
  closeState (known := [w18.toFinset, w19.toFinset]) w87 (by decide) (by decide +kernel) (consbad n18 (consbad n19 (nilbad 3)))

def w88 : List Mask := [15,3840,4601,17476,61986]
theorem n88 : impossible 4 w88.toFinset :=
  closeState (known := [w20.toFinset, w21.toFinset]) w88 (by decide) (by decide +kernel) (consbad n20 (consbad n21 (nilbad 3)))

def w89 : List Mask := [15,3848,4593,8738,62532]
theorem n89 : impossible 4 w89.toFinset :=
  closeState (known := [w7.toFinset]) w89 (by decide) (by decide +kernel) (consbad n7 (nilbad 3))

def w90 : List Mask := [15,3848,4593,17476,61986]
theorem n90 : impossible 4 w90.toFinset :=
  closeState (known := [w10.toFinset]) w90 (by decide) (by decide +kernel) (consbad n10 (nilbad 3))

def w91 : List Mask := [15,3904,4593,34952,61986]
theorem n91 : impossible 4 w91.toFinset :=
  closeState (known := [w13.toFinset]) w91 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w92 : List Mask := [15,4160,4593,12066,34952]
theorem n92 : impossible 4 w92.toFinset :=
  closeState (known := [w9.toFinset, w28.toFinset]) w92 (by decide) (by decide +kernel) (consbad n9 (consbad n28 (nilbad 3)))

def w93 : List Mask := [15,4352,8738,17476,39417]
theorem n93 : impossible 4 w93.toFinset :=
  closeState (known := [w22.toFinset, w23.toFinset, w29.toFinset, w31.toFinset]) w93 (by decide) (by decide +kernel) (consbad n22 (consbad n23 (consbad n29 (consbad n31 (nilbad 3)))))

def w94 : List Mask := [15,4353,8738,17476,35064]
theorem n94 : impossible 4 w94.toFinset :=
  closeState (known := [w30.toFinset]) w94 (by decide) (by decide +kernel) (consbad n30 (nilbad 3))

def w95 : List Mask := [15,4369,8738,21828,35064]
theorem n95 : impossible 4 w95.toFinset :=
  closeState (known := [w22.toFinset, w32.toFinset]) w95 (by decide) (by decide +kernel) (consbad n22 (consbad n32 (nilbad 3)))

def w96 : List Mask := [15,4369,8802,35064,65280]
theorem n96 : impossible 4 w96.toFinset :=
  closeState (known := []) w96 (by decide) (by decide +kernel) (nilbad 3)

def w97 : List Mask := [15,4369,13090,17476,35064]
theorem n97 : impossible 4 w97.toFinset :=
  closeState (known := [w23.toFinset, w33.toFinset]) w97 (by decide) (by decide +kernel) (consbad n23 (consbad n33 (nilbad 3)))

def w98 : List Mask := [15,4369,26214,35064,65314]
theorem n98 : impossible 4 w98.toFinset :=
  closeState (known := []) w98 (by decide) (by decide +kernel) (nilbad 3)

def w99 : List Mask := [15,4416,4593,8738,34952]
theorem n99 : impossible 4 w99.toFinset :=
  closeState (known := [w5.toFinset, w8.toFinset, w34.toFinset]) w99 (by decide) (by decide +kernel) (consbad n5 (consbad n8 (consbad n34 (nilbad 3))))

def w100 : List Mask := [15,4593,8000,8738,34952]
theorem n100 : impossible 4 w100.toFinset :=
  closeState (known := [w9.toFinset]) w100 (by decide) (by decide +kernel) (consbad n9 (nilbad 3))

def w101 : List Mask := [15,4593,8738,17476,65288]
theorem n101 : impossible 4 w101.toFinset :=
  closeState (known := [w10.toFinset]) w101 (by decide) (by decide +kernel) (consbad n10 (nilbad 3))

def w102 : List Mask := [15,4593,8738,20292,61448]
theorem n102 : impossible 4 w102.toFinset :=
  closeState (known := [w11.toFinset]) w102 (by decide) (by decide +kernel) (consbad n11 (nilbad 3))

def w103 : List Mask := [15,4593,8738,21828,34952]
theorem n103 : impossible 4 w103.toFinset :=
  closeState (known := [w22.toFinset, w35.toFinset]) w103 (by decide) (by decide +kernel) (consbad n22 (consbad n35 (nilbad 3)))

def w104 : List Mask := [15,4593,8738,24388,34952]
theorem n104 : impossible 4 w104.toFinset :=
  closeState (known := []) w104 (by decide) (by decide +kernel) (nilbad 3)

def w105 : List Mask := [15,4593,8738,34952,61760]
theorem n105 : impossible 4 w105.toFinset :=
  closeState (known := [w12.toFinset]) w105 (by decide) (by decide +kernel) (consbad n12 (nilbad 3))

def w106 : List Mask := [15,4593,8738,34952,62788]
theorem n106 : impossible 4 w106.toFinset :=
  closeState (known := []) w106 (by decide) (by decide +kernel) (nilbad 3)

def w107 : List Mask := [15,4593,8738,34952,65344]
theorem n107 : impossible 4 w107.toFinset :=
  closeState (known := [w13.toFinset]) w107 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w108 : List Mask := [15,4593,8738,34952,65348]
theorem n108 : impossible 4 w108.toFinset :=
  closeState (known := []) w108 (by decide) (by decide +kernel) (nilbad 3)

def w109 : List Mask := [15,4593,8738,34952,65359]
theorem n109 : impossible 4 w109.toFinset :=
  closeState (known := []) w109 (by decide) (by decide +kernel) (nilbad 3)

def w110 : List Mask := [15,4593,8738,34952,65382]
theorem n110 : impossible 4 w110.toFinset :=
  closeState (known := [w14.toFinset]) w110 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w111 : List Mask := [15,4593,8738,35064,65348]
theorem n111 : impossible 4 w111.toFinset :=
  closeState (known := []) w111 (by decide) (by decide +kernel) (nilbad 3)

def w112 : List Mask := [15,4593,8738,36744,65348]
theorem n112 : impossible 4 w112.toFinset :=
  closeState (known := []) w112 (by decide) (by decide +kernel) (nilbad 3)

def w113 : List Mask := [15,4593,8738,39321,65348]
theorem n113 : impossible 4 w113.toFinset :=
  closeState (known := []) w113 (by decide) (by decide +kernel) (nilbad 3)

def w114 : List Mask := [15,4593,8738,39417,65348]
theorem n114 : impossible 4 w114.toFinset :=
  closeState (known := [w5.toFinset]) w114 (by decide) (by decide +kernel) (consbad n5 (nilbad 3))

def w115 : List Mask := [15,4593,8738,43690,65348]
theorem n115 : impossible 4 w115.toFinset :=
  closeState (known := [w14.toFinset]) w115 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w116 : List Mask := [15,4593,8738,63624,65348]
theorem n116 : impossible 4 w116.toFinset :=
  closeState (known := []) w116 (by decide) (by decide +kernel) (nilbad 3)

def w117 : List Mask := [15,4593,8738,65348,65416]
theorem n117 : impossible 4 w117.toFinset :=
  closeState (known := []) w117 (by decide) (by decide +kernel) (nilbad 3)

def w118 : List Mask := [15,4593,8746,17476,65280]
theorem n118 : impossible 4 w118.toFinset :=
  closeState (known := [w6.toFinset, w10.toFinset, w36.toFinset]) w118 (by decide) (by decide +kernel) (consbad n6 (consbad n10 (consbad n36 (nilbad 3))))

def w119 : List Mask := [15,4593,8746,20292,61440]
theorem n119 : impossible 4 w119.toFinset :=
  closeState (known := [w6.toFinset, w11.toFinset]) w119 (by decide) (by decide +kernel) (consbad n6 (consbad n11 (nilbad 3)))

def w120 : List Mask := [15,4593,8802,34952,65280]
theorem n120 : impossible 4 w120.toFinset :=
  closeState (known := [w13.toFinset]) w120 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w121 : List Mask := [15,4593,8994,34952,62532]
theorem n121 : impossible 4 w121.toFinset :=
  closeState (known := []) w121 (by decide) (by decide +kernel) (nilbad 3)

def w122 : List Mask := [15,4593,9058,34952,61440]
theorem n122 : impossible 4 w122.toFinset :=
  closeState (known := [w12.toFinset]) w122 (by decide) (by decide +kernel) (consbad n12 (nilbad 3))

def w123 : List Mask := [15,4593,12066,17476,61448]
theorem n123 : impossible 4 w123.toFinset :=
  closeState (known := [w10.toFinset]) w123 (by decide) (by decide +kernel) (consbad n10 (nilbad 3))

def w124 : List Mask := [15,4593,12066,21572,34952]
theorem n124 : impossible 4 w124.toFinset :=
  closeState (known := []) w124 (by decide) (by decide +kernel) (nilbad 3)

def w125 : List Mask := [15,4593,12066,34952,61504]
theorem n125 : impossible 4 w125.toFinset :=
  closeState (known := [w13.toFinset]) w125 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w126 : List Mask := [15,4593,12066,34952,62543]
theorem n126 : impossible 4 w126.toFinset :=
  closeState (known := []) w126 (by decide) (by decide +kernel) (nilbad 3)

def w127 : List Mask := [15,4593,12066,34952,63078]
theorem n127 : impossible 4 w127.toFinset :=
  closeState (known := []) w127 (by decide) (by decide +kernel) (nilbad 3)

def w128 : List Mask := [15,4593,12066,34952,65348]
theorem n128 : impossible 4 w128.toFinset :=
  closeState (known := []) w128 (by decide) (by decide +kernel) (nilbad 3)

def w129 : List Mask := [15,4593,12066,34952,65382]
theorem n129 : impossible 4 w129.toFinset :=
  closeState (known := [w15.toFinset]) w129 (by decide) (by decide +kernel) (consbad n15 (nilbad 3))

def w130 : List Mask := [15,4593,12066,35064,62532]
theorem n130 : impossible 4 w130.toFinset :=
  closeState (known := []) w130 (by decide) (by decide +kernel) (nilbad 3)

def w131 : List Mask := [15,4593,12066,36744,62532]
theorem n131 : impossible 4 w131.toFinset :=
  closeState (known := []) w131 (by decide) (by decide +kernel) (nilbad 3)

def w132 : List Mask := [15,4593,12066,39321,62532]
theorem n132 : impossible 4 w132.toFinset :=
  closeState (known := []) w132 (by decide) (by decide +kernel) (nilbad 3)

def w133 : List Mask := [15,4593,12066,39417,62532]
theorem n133 : impossible 4 w133.toFinset :=
  closeState (known := []) w133 (by decide) (by decide +kernel) (nilbad 3)

def w134 : List Mask := [15,4593,12066,43690,62532]
theorem n134 : impossible 4 w134.toFinset :=
  closeState (known := [w14.toFinset]) w134 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w135 : List Mask := [15,4593,12066,44970,62532]
theorem n135 : impossible 4 w135.toFinset :=
  closeState (known := [w15.toFinset]) w135 (by decide) (by decide +kernel) (consbad n15 (nilbad 3))

def w136 : List Mask := [15,4593,12066,62532,63624]
theorem n136 : impossible 4 w136.toFinset :=
  closeState (known := []) w136 (by decide) (by decide +kernel) (nilbad 3)

def w137 : List Mask := [15,4593,12074,17476,61440]
theorem n137 : impossible 4 w137.toFinset :=
  closeState (known := [w7.toFinset, w10.toFinset]) w137 (by decide) (by decide +kernel) (consbad n7 (consbad n10 (nilbad 3)))

def w138 : List Mask := [15,4593,12130,34952,61440]
theorem n138 : impossible 4 w138.toFinset :=
  closeState (known := [w13.toFinset]) w138 (by decide) (by decide +kernel) (consbad n13 (nilbad 3))

def w139 : List Mask := [15,4593,12834,20292,34952]
theorem n139 : impossible 4 w139.toFinset :=
  closeState (known := []) w139 (by decide) (by decide +kernel) (nilbad 3)

def w140 : List Mask := [15,4593,13090,17476,34952]
theorem n140 : impossible 4 w140.toFinset :=
  closeState (known := [w23.toFinset, w37.toFinset]) w140 (by decide) (by decide +kernel) (consbad n23 (consbad n37 (nilbad 3)))

def w141 : List Mask := [15,4593,16162,17476,34952]
theorem n141 : impossible 4 w141.toFinset :=
  closeState (known := []) w141 (by decide) (by decide +kernel) (nilbad 3)

def w142 : List Mask := [15,4593,17476,34952,62242]
theorem n142 : impossible 4 w142.toFinset :=
  closeState (known := []) w142 (by decide) (by decide +kernel) (nilbad 3)

def w143 : List Mask := [15,4593,17476,34952,65314]
theorem n143 : impossible 4 w143.toFinset :=
  closeState (known := []) w143 (by decide) (by decide +kernel) (nilbad 3)

def w144 : List Mask := [15,4593,17476,35064,65314]
theorem n144 : impossible 4 w144.toFinset :=
  closeState (known := []) w144 (by decide) (by decide +kernel) (nilbad 3)

def w145 : List Mask := [15,4593,17476,36744,65314]
theorem n145 : impossible 4 w145.toFinset :=
  closeState (known := []) w145 (by decide) (by decide +kernel) (nilbad 3)

def w146 : List Mask := [15,4593,17476,39321,65314]
theorem n146 : impossible 4 w146.toFinset :=
  closeState (known := []) w146 (by decide) (by decide +kernel) (nilbad 3)

def w147 : List Mask := [15,4593,17476,39417,65314]
theorem n147 : impossible 4 w147.toFinset :=
  closeState (known := []) w147 (by decide) (by decide +kernel) (nilbad 3)

def w148 : List Mask := [15,4593,17476,43690,65314]
theorem n148 : impossible 4 w148.toFinset :=
  closeState (known := [w14.toFinset, w38.toFinset]) w148 (by decide) (by decide +kernel) (consbad n14 (consbad n38 (nilbad 3)))

def w149 : List Mask := [15,4593,17476,44970,65314]
theorem n149 : impossible 4 w149.toFinset :=
  closeState (known := [w15.toFinset]) w149 (by decide) (by decide +kernel) (consbad n15 (nilbad 3))

def w150 : List Mask := [15,4593,17476,63624,65314]
theorem n150 : impossible 4 w150.toFinset :=
  closeState (known := []) w150 (by decide) (by decide +kernel) (nilbad 3)

def w151 : List Mask := [15,4593,17476,64170,65314]
theorem n151 : impossible 4 w151.toFinset :=
  closeState (known := [w16.toFinset]) w151 (by decide) (by decide +kernel) (consbad n16 (nilbad 3))

def w152 : List Mask := [15,4593,17476,65314,65416]
theorem n152 : impossible 4 w152.toFinset :=
  closeState (known := []) w152 (by decide) (by decide +kernel) (nilbad 3)

def w153 : List Mask := [15,4593,17476,65314,65450]
theorem n153 : impossible 4 w153.toFinset :=
  closeState (known := [w17.toFinset]) w153 (by decide) (by decide +kernel) (consbad n17 (nilbad 3))

def w154 : List Mask := [15,4593,17487,34952,65314]
theorem n154 : impossible 4 w154.toFinset :=
  closeState (known := []) w154 (by decide) (by decide +kernel) (nilbad 3)

def w155 : List Mask := [15,4593,17732,34952,61986]
theorem n155 : impossible 4 w155.toFinset :=
  closeState (known := []) w155 (by decide) (by decide +kernel) (nilbad 3)

def w156 : List Mask := [15,4593,20292,34952,65314]
theorem n156 : impossible 4 w156.toFinset :=
  closeState (known := []) w156 (by decide) (by decide +kernel) (nilbad 3)

def w157 : List Mask := [15,4593,20292,35064,61986]
theorem n157 : impossible 4 w157.toFinset :=
  closeState (known := []) w157 (by decide) (by decide +kernel) (nilbad 3)

def w158 : List Mask := [15,4593,20292,36744,61986]
theorem n158 : impossible 4 w158.toFinset :=
  closeState (known := []) w158 (by decide) (by decide +kernel) (nilbad 3)

def w159 : List Mask := [15,4593,20292,39321,61986]
theorem n159 : impossible 4 w159.toFinset :=
  closeState (known := []) w159 (by decide) (by decide +kernel) (nilbad 3)

def w160 : List Mask := [15,4593,20292,39417,61986]
theorem n160 : impossible 4 w160.toFinset :=
  closeState (known := []) w160 (by decide) (by decide +kernel) (nilbad 3)

def w161 : List Mask := [15,4593,20292,43690,61986]
theorem n161 : impossible 4 w161.toFinset :=
  closeState (known := [w14.toFinset]) w161 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w162 : List Mask := [15,4593,20292,61986,63624]
theorem n162 : impossible 4 w162.toFinset :=
  closeState (known := []) w162 (by decide) (by decide +kernel) (nilbad 3)

def w163 : List Mask := [15,4593,20292,61986,64170]
theorem n163 : impossible 4 w163.toFinset :=
  closeState (known := [w16.toFinset]) w163 (by decide) (by decide +kernel) (consbad n16 (nilbad 3))

def w164 : List Mask := [15,4593,20303,34952,61986]
theorem n164 : impossible 4 w164.toFinset :=
  closeState (known := []) w164 (by decide) (by decide +kernel) (nilbad 3)

def w165 : List Mask := [15,4593,26214,34952,65314]
theorem n165 : impossible 4 w165.toFinset :=
  closeState (known := []) w165 (by decide) (by decide +kernel) (nilbad 3)

def w166 : List Mask := [15,4593,26214,43690,65280]
theorem n166 : impossible 4 w166.toFinset :=
  closeState (known := [w14.toFinset]) w166 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w167 : List Mask := [15,4593,28518,34952,61986]
theorem n167 : impossible 4 w167.toFinset :=
  closeState (known := []) w167 (by decide) (by decide +kernel) (nilbad 3)

def w168 : List Mask := [15,4593,28518,34952,65314]
theorem n168 : impossible 4 w168.toFinset :=
  closeState (known := []) w168 (by decide) (by decide +kernel) (nilbad 3)

def w169 : List Mask := [15,4593,28518,43690,61440]
theorem n169 : impossible 4 w169.toFinset :=
  closeState (known := [w14.toFinset]) w169 (by decide) (by decide +kernel) (consbad n14 (nilbad 3))

def w170 : List Mask := [15,4593,28518,44970,61440]
theorem n170 : impossible 4 w170.toFinset :=
  closeState (known := [w15.toFinset]) w170 (by decide) (by decide +kernel) (consbad n15 (nilbad 3))

def w171 : List Mask := [15,4593,34952,61986,65348]
theorem n171 : impossible 4 w171.toFinset :=
  closeState (known := []) w171 (by decide) (by decide +kernel) (nilbad 3)

def w172 : List Mask := [15,4593,34952,61986,65382]
theorem n172 : impossible 4 w172.toFinset :=
  closeState (known := [w16.toFinset]) w172 (by decide) (by decide +kernel) (consbad n16 (nilbad 3))

def w173 : List Mask := [15,4593,34952,62532,65314]
theorem n173 : impossible 4 w173.toFinset :=
  closeState (known := []) w173 (by decide) (by decide +kernel) (nilbad 3)

def w174 : List Mask := [15,4593,34952,63078,65314]
theorem n174 : impossible 4 w174.toFinset :=
  closeState (known := []) w174 (by decide) (by decide +kernel) (nilbad 3)

def w175 : List Mask := [15,4593,34952,65314,65348]
theorem n175 : impossible 4 w175.toFinset :=
  closeState (known := []) w175 (by decide) (by decide +kernel) (nilbad 3)

def w176 : List Mask := [15,4593,34952,65314,65382]
theorem n176 : impossible 4 w176.toFinset :=
  closeState (known := [w17.toFinset]) w176 (by decide) (by decide +kernel) (consbad n17 (nilbad 3))

def w177 : List Mask := [15,4601,8738,17476,65280]
theorem n177 : impossible 4 w177.toFinset :=
  closeState (known := [w18.toFinset, w20.toFinset, w39.toFinset]) w177 (by decide) (by decide +kernel) (consbad n18 (consbad n20 (consbad n39 (nilbad 3))))

def w178 : List Mask := [15,4601,8738,20292,61440]
theorem n178 : impossible 4 w178.toFinset :=
  closeState (known := [w18.toFinset, w21.toFinset]) w178 (by decide) (by decide +kernel) (consbad n18 (consbad n21 (nilbad 3)))

def w179 : List Mask := [15,4601,12066,17476,61440]
theorem n179 : impossible 4 w179.toFinset :=
  closeState (known := [w19.toFinset, w20.toFinset]) w179 (by decide) (by decide +kernel) (consbad n19 (consbad n20 (nilbad 3)))

def w180 : List Mask := [79,240,4369,8738,65416]
theorem n180 : impossible 4 w180.toFinset :=
  closeState (known := []) w180 (by decide) (by decide +kernel) (nilbad 3)

def w181 : List Mask := [79,240,4369,12066,63624]
theorem n181 : impossible 4 w181.toFinset :=
  closeState (known := []) w181 (by decide) (by decide +kernel) (nilbad 3)

def w182 : List Mask := [79,240,4369,34952,65314]
theorem n182 : impossible 4 w182.toFinset :=
  closeState (known := [w24.toFinset]) w182 (by decide) (by decide +kernel) (consbad n24 (nilbad 3))

def w183 : List Mask := [79,240,4369,36744,61986]
theorem n183 : impossible 4 w183.toFinset :=
  closeState (known := []) w183 (by decide) (by decide +kernel) (nilbad 3)

def w184 : List Mask := [79,3840,4593,34952,61986]
theorem n184 : impossible 4 w184.toFinset :=
  closeState (known := [w24.toFinset]) w184 (by decide) (by decide +kernel) (consbad n24 (nilbad 3))

def w185 : List Mask := [79,4369,8738,35064,65280]
theorem n185 : impossible 4 w185.toFinset :=
  closeState (known := []) w185 (by decide) (by decide +kernel) (nilbad 3)

def w186 : List Mask := [79,4593,8738,34952,65280]
theorem n186 : impossible 4 w186.toFinset :=
  closeState (known := [w24.toFinset]) w186 (by decide) (by decide +kernel) (consbad n24 (nilbad 3))

def w187 : List Mask := [79,4593,12066,34952,61440]
theorem n187 : impossible 4 w187.toFinset :=
  closeState (known := [w24.toFinset]) w187 (by decide) (by decide +kernel) (consbad n24 (nilbad 3))

def w188 : List Mask := [240,4352,8738,17487,39321]
theorem n188 : impossible 4 w188.toFinset :=
  closeState (known := [w25.toFinset, w26.toFinset, w29.toFinset]) w188 (by decide) (by decide +kernel) (consbad n25 (consbad n26 (consbad n29 (nilbad 3))))

def w189 : List Mask := [240,4353,8738,17487,34952]
theorem n189 : impossible 4 w189.toFinset :=
  closeState (known := [w30.toFinset]) w189 (by decide) (by decide +kernel) (consbad n30 (nilbad 3))

def w190 : List Mask := [240,4367,8738,17476,39321]
theorem n190 : impossible 4 w190.toFinset :=
  closeState (known := [w25.toFinset, w31.toFinset]) w190 (by decide) (by decide +kernel) (consbad n25 (consbad n31 (nilbad 3)))

def w191 : List Mask := [240,4369,8738,17487,39304]
theorem n191 : impossible 4 w191.toFinset :=
  closeState (known := []) w191 (by decide) (by decide +kernel) (nilbad 3)

def w192 : List Mask := [240,4369,8738,21839,34952]
theorem n192 : impossible 4 w192.toFinset :=
  closeState (known := [w25.toFinset, w32.toFinset, w35.toFinset]) w192 (by decide) (by decide +kernel) (consbad n25 (consbad n32 (consbad n35 (nilbad 3))))

def w193 : List Mask := [240,4369,8746,17487,65280]
theorem n193 : impossible 4 w193.toFinset :=
  closeState (known := [w36.toFinset]) w193 (by decide) (by decide +kernel) (consbad n36 (nilbad 3))

def w194 : List Mask := [240,4369,13090,17487,34952]
theorem n194 : impossible 4 w194.toFinset :=
  closeState (known := [w26.toFinset, w33.toFinset, w37.toFinset]) w194 (by decide) (by decide +kernel) (consbad n26 (consbad n33 (consbad n37 (nilbad 3))))

def w195 : List Mask := [240,4369,17487,43690,65314]
theorem n195 : impossible 4 w195.toFinset :=
  closeState (known := [w38.toFinset]) w195 (by decide) (by decide +kernel) (consbad n38 (nilbad 3))

def w196 : List Mask := [240,4377,8738,17487,65280]
theorem n196 : impossible 4 w196.toFinset :=
  closeState (known := [w39.toFinset]) w196 (by decide) (by decide +kernel) (consbad n39 (nilbad 3))

def w197 : List Mask := [248,4369,8738,17487,65280]
theorem n197 : impossible 4 w197.toFinset :=
  closeState (known := [w39.toFinset]) w197 (by decide) (by decide +kernel) (consbad n39 (nilbad 3))

def w198 : List Mask := [271,4593,8738,34952,62532]
theorem n198 : impossible 4 w198.toFinset :=
  closeState (known := []) w198 (by decide) (by decide +kernel) (nilbad 3)

def w199 : List Mask := [271,4593,17476,34952,61986]
theorem n199 : impossible 4 w199.toFinset :=
  closeState (known := []) w199 (by decide) (by decide +kernel) (nilbad 3)

def w200 : List Mask := [335,4593,8738,34952,61440]
theorem n200 : impossible 4 w200.toFinset :=
  closeState (known := [w27.toFinset]) w200 (by decide) (by decide +kernel) (consbad n27 (nilbad 3))

def w201 : List Mask := [3840,4175,4593,8738,34952]
theorem n201 : impossible 4 w201.toFinset :=
  closeState (known := [w28.toFinset]) w201 (by decide) (by decide +kernel) (consbad n28 (nilbad 3))

def w202 : List Mask := [3840,4369,8738,21583,35064]
theorem n202 : impossible 4 w202.toFinset :=
  closeState (known := []) w202 (by decide) (by decide +kernel) (nilbad 3)

def w203 : List Mask := [3840,4369,12834,17487,35064]
theorem n203 : impossible 4 w203.toFinset :=
  closeState (known := []) w203 (by decide) (by decide +kernel) (nilbad 3)

def w204 : List Mask := [3840,4593,8738,21583,34952]
theorem n204 : impossible 4 w204.toFinset :=
  closeState (known := []) w204 (by decide) (by decide +kernel) (nilbad 3)

def w205 : List Mask := [3840,4593,8746,17487,61440]
theorem n205 : impossible 4 w205.toFinset :=
  closeState (known := [w36.toFinset]) w205 (by decide) (by decide +kernel) (consbad n36 (nilbad 3))

def w206 : List Mask := [3840,4593,12834,17487,34952]
theorem n206 : impossible 4 w206.toFinset :=
  closeState (known := []) w206 (by decide) (by decide +kernel) (nilbad 3)

def w207 : List Mask := [3840,4593,17487,43690,61986]
theorem n207 : impossible 4 w207.toFinset :=
  closeState (known := [w38.toFinset]) w207 (by decide) (by decide +kernel) (consbad n38 (nilbad 3))

def w208 : List Mask := [3840,4601,8738,17487,61440]
theorem n208 : impossible 4 w208.toFinset :=
  closeState (known := [w39.toFinset]) w208 (by decide) (by decide +kernel) (consbad n39 (nilbad 3))

def w209 : List Mask := [3855,4593,8738,34952,62543]
theorem n209 : impossible 4 w209.toFinset :=
  closeState (known := []) w209 (by decide) (by decide +kernel) (nilbad 3)

def w210 : List Mask := [3855,4593,17487,34952,61986]
theorem n210 : impossible 4 w210.toFinset :=
  closeState (known := []) w210 (by decide) (by decide +kernel) (nilbad 3)

def w211 : List Mask := [4111,4593,8738,20292,34952]
theorem n211 : impossible 4 w211.toFinset :=
  closeState (known := []) w211 (by decide) (by decide +kernel) (nilbad 3)

def w212 : List Mask := [4111,4593,12066,17476,34952]
theorem n212 : impossible 4 w212.toFinset :=
  closeState (known := []) w212 (by decide) (by decide +kernel) (nilbad 3)

def w213 : List Mask := [4352,4369,8738,17487,35064]
theorem n213 : impossible 4 w213.toFinset :=
  closeState (known := [w29.toFinset, w32.toFinset, w33.toFinset]) w213 (by decide) (by decide +kernel) (consbad n29 (consbad n32 (consbad n33 (nilbad 3))))

def w214 : List Mask := [4352,4593,8738,17487,34952]
theorem n214 : impossible 4 w214.toFinset :=
  closeState (known := [w29.toFinset, w35.toFinset, w37.toFinset]) w214 (by decide) (by decide +kernel) (consbad n29 (consbad n35 (consbad n37 (nilbad 3))))

def w215 : List Mask := [4367,4369,8738,17476,35064]
theorem n215 : impossible 4 w215.toFinset :=
  closeState (known := [w31.toFinset, w32.toFinset]) w215 (by decide) (by decide +kernel) (consbad n31 (consbad n32 (nilbad 3)))

def w216 : List Mask := [4367,4593,8738,17476,34952]
theorem n216 : impossible 4 w216.toFinset :=
  closeState (known := [w31.toFinset, w35.toFinset]) w216 (by decide) (by decide +kernel) (consbad n31 (consbad n35 (nilbad 3)))

def w217 : List Mask := [4369,7936,8738,17487,35064]
theorem n217 : impossible 4 w217.toFinset :=
  closeState (known := []) w217 (by decide) (by decide +kernel) (nilbad 3)

def w218 : List Mask := [4369,8738,17487,35064,61696]
theorem n218 : impossible 4 w218.toFinset :=
  closeState (known := []) w218 (by decide) (by decide +kernel) (nilbad 3)

def w219 : List Mask := [4369,8738,17487,35064,65295]
theorem n219 : impossible 4 w219.toFinset :=
  closeState (known := [w30.toFinset]) w219 (by decide) (by decide +kernel) (consbad n30 (nilbad 3))

def w220 : List Mask := [4369,8738,17487,35064,65314]
theorem n220 : impossible 4 w220.toFinset :=
  closeState (known := []) w220 (by decide) (by decide +kernel) (nilbad 3)

def w221 : List Mask := [4369,8738,17487,35064,65348]
theorem n221 : impossible 4 w221.toFinset :=
  closeState (known := []) w221 (by decide) (by decide +kernel) (nilbad 3)

def w222 : List Mask := [4369,8738,17487,35064,65359]
theorem n222 : impossible 4 w222.toFinset :=
  closeState (known := [w30.toFinset]) w222 (by decide) (by decide +kernel) (consbad n30 (nilbad 3))

def w223 : List Mask := [4369,8738,17487,35064,65416]
theorem n223 : impossible 4 w223.toFinset :=
  closeState (known := []) w223 (by decide) (by decide +kernel) (nilbad 3)

def w224 : List Mask := [4369,8738,17487,39417,65280]
theorem n224 : impossible 4 w224.toFinset :=
  closeState (known := [w29.toFinset]) w224 (by decide) (by decide +kernel) (consbad n29 (nilbad 3))

def w225 : List Mask := [4369,8738,17743,35064,61440]
theorem n225 : impossible 4 w225.toFinset :=
  closeState (known := []) w225 (by decide) (by decide +kernel) (nilbad 3)

def w226 : List Mask := [4369,8738,20303,35064,62543]
theorem n226 : impossible 4 w226.toFinset :=
  closeState (known := []) w226 (by decide) (by decide +kernel) (nilbad 3)

def w227 : List Mask := [4369,8994,17487,35064,61440]
theorem n227 : impossible 4 w227.toFinset :=
  closeState (known := []) w227 (by decide) (by decide +kernel) (nilbad 3)

def w228 : List Mask := [4369,12066,17487,35064,61986]
theorem n228 : impossible 4 w228.toFinset :=
  closeState (known := []) w228 (by decide) (by decide +kernel) (nilbad 3)

def w229 : List Mask := [4593,7936,8738,17487,34952]
theorem n229 : impossible 4 w229.toFinset :=
  closeState (known := []) w229 (by decide) (by decide +kernel) (nilbad 3)

def w230 : List Mask := [4593,8738,17487,34952,61696]
theorem n230 : impossible 4 w230.toFinset :=
  closeState (known := []) w230 (by decide) (by decide +kernel) (nilbad 3)

def w231 : List Mask := [4593,8738,17487,34952,65295]
theorem n231 : impossible 4 w231.toFinset :=
  closeState (known := []) w231 (by decide) (by decide +kernel) (nilbad 3)

def w232 : List Mask := [4593,8738,17487,34952,65314]
theorem n232 : impossible 4 w232.toFinset :=
  closeState (known := [w38.toFinset]) w232 (by decide) (by decide +kernel) (consbad n38 (nilbad 3))

def w233 : List Mask := [4593,8738,17487,34952,65348]
theorem n233 : impossible 4 w233.toFinset :=
  closeState (known := []) w233 (by decide) (by decide +kernel) (nilbad 3)

def w234 : List Mask := [4593,8738,17487,34952,65359]
theorem n234 : impossible 4 w234.toFinset :=
  closeState (known := []) w234 (by decide) (by decide +kernel) (nilbad 3)

def w235 : List Mask := [4593,8738,17487,35064,65280]
theorem n235 : impossible 4 w235.toFinset :=
  closeState (known := []) w235 (by decide) (by decide +kernel) (nilbad 3)

def w236 : List Mask := [4593,8738,17487,39321,65280]
theorem n236 : impossible 4 w236.toFinset :=
  closeState (known := []) w236 (by decide) (by decide +kernel) (nilbad 3)

def w237 : List Mask := [4593,8738,17487,39417,65280]
theorem n237 : impossible 4 w237.toFinset :=
  closeState (known := [w29.toFinset]) w237 (by decide) (by decide +kernel) (consbad n29 (nilbad 3))

def w238 : List Mask := [4593,8738,17487,43690,65280]
theorem n238 : impossible 4 w238.toFinset :=
  closeState (known := [w38.toFinset]) w238 (by decide) (by decide +kernel) (consbad n38 (nilbad 3))

def w239 : List Mask := [4593,8738,17743,34952,61440]
theorem n239 : impossible 4 w239.toFinset :=
  closeState (known := []) w239 (by decide) (by decide +kernel) (nilbad 3)

def w240 : List Mask := [4593,8738,20303,34952,61455]
theorem n240 : impossible 4 w240.toFinset :=
  closeState (known := []) w240 (by decide) (by decide +kernel) (nilbad 3)

def w241 : List Mask := [4593,8738,20303,34952,62543]
theorem n241 : impossible 4 w241.toFinset :=
  closeState (known := []) w241 (by decide) (by decide +kernel) (nilbad 3)

def w242 : List Mask := [4593,8994,17487,34952,61440]
theorem n242 : impossible 4 w242.toFinset :=
  closeState (known := []) w242 (by decide) (by decide +kernel) (nilbad 3)

def w243 : List Mask := [4593,12066,17487,34952,61455]
theorem n243 : impossible 4 w243.toFinset :=
  closeState (known := []) w243 (by decide) (by decide +kernel) (nilbad 3)

def w244 : List Mask := [4593,12066,17487,34952,61986]
theorem n244 : impossible 4 w244.toFinset :=
  closeState (known := []) w244 (by decide) (by decide +kernel) (nilbad 3)

def w245 : List Mask := [4593,12066,17487,43690,61440]
theorem n245 : impossible 4 w245.toFinset :=
  closeState (known := [w38.toFinset]) w245 (by decide) (by decide +kernel) (consbad n38 (nilbad 3))

def w246 : List Mask := [8,15,240,4369,8738,65348]
theorem n246 : impossible 5 w246.toFinset :=
  closeState (known := [w40.toFinset, w53.toFinset, w70.toFinset, w76.toFinset]) w246 (by decide) (by decide +kernel) (consbad n40 (consbad n53 (consbad n70 (consbad n76 (nilbad 4)))))

def w247 : List Mask := [8,15,240,4369,12066,62532]
theorem n247 : impossible 5 w247.toFinset :=
  closeState (known := [w41.toFinset, w55.toFinset, w71.toFinset, w77.toFinset]) w247 (by decide) (by decide +kernel) (consbad n41 (consbad n55 (consbad n71 (consbad n77 (nilbad 4)))))

def w248 : List Mask := [8,15,240,4369,17476,65314]
theorem n248 : impossible 5 w248.toFinset :=
  closeState (known := [w42.toFinset, w57.toFinset, w72.toFinset, w78.toFinset]) w248 (by decide) (by decide +kernel) (consbad n42 (consbad n57 (consbad n72 (consbad n78 (nilbad 4)))))

def w249 : List Mask := [8,15,240,4369,20292,61986]
theorem n249 : impossible 5 w249.toFinset :=
  closeState (known := [w43.toFinset, w58.toFinset, w73.toFinset, w79.toFinset]) w249 (by decide) (by decide +kernel) (consbad n43 (consbad n58 (consbad n73 (consbad n79 (nilbad 4)))))

def w250 : List Mask := [8,15,3840,4593,8738,62532]
theorem n250 : impossible 5 w250.toFinset :=
  closeState (known := [w40.toFinset, w41.toFinset, w81.toFinset, w87.toFinset, w89.toFinset]) w250 (by decide) (by decide +kernel) (consbad n40 (consbad n41 (consbad n81 (consbad n87 (consbad n89 (nilbad 4))))))

def w251 : List Mask := [8,15,3840,4593,17476,61986]
theorem n251 : impossible 5 w251.toFinset :=
  closeState (known := [w42.toFinset, w43.toFinset, w83.toFinset, w88.toFinset, w90.toFinset]) w251 (by decide) (by decide +kernel) (consbad n42 (consbad n43 (consbad n83 (consbad n88 (consbad n90 (nilbad 4))))))

def w252 : List Mask := [8,15,4593,8738,17476,65280]
theorem n252 : impossible 5 w252.toFinset :=
  closeState (known := [w40.toFinset, w42.toFinset, w44.toFinset, w101.toFinset, w118.toFinset, w177.toFinset]) w252 (by decide) (by decide +kernel) (consbad n40 (consbad n42 (consbad n44 (consbad n101 (consbad n118 (consbad n177 (nilbad 4)))))))

def w253 : List Mask := [8,15,4593,8738,20292,61440]
theorem n253 : impossible 5 w253.toFinset :=
  closeState (known := [w40.toFinset, w43.toFinset, w102.toFinset, w119.toFinset, w178.toFinset]) w253 (by decide) (by decide +kernel) (consbad n40 (consbad n43 (consbad n102 (consbad n119 (consbad n178 (nilbad 4))))))

def w254 : List Mask := [8,15,4593,12066,17476,61440]
theorem n254 : impossible 5 w254.toFinset :=
  closeState (known := [w41.toFinset, w42.toFinset, w123.toFinset, w137.toFinset, w179.toFinset]) w254 (by decide) (by decide +kernel) (consbad n41 (consbad n42 (consbad n123 (consbad n137 (consbad n179 (nilbad 4))))))

def w255 : List Mask := [8,240,4369,8738,17487,65280]
theorem n255 : impossible 5 w255.toFinset :=
  closeState (known := [w44.toFinset, w193.toFinset, w196.toFinset, w197.toFinset]) w255 (by decide) (by decide +kernel) (consbad n44 (consbad n193 (consbad n196 (consbad n197 (nilbad 4)))))

def w256 : List Mask := [8,3840,4593,8738,17487,61440]
theorem n256 : impossible 5 w256.toFinset :=
  closeState (known := [w44.toFinset, w205.toFinset, w208.toFinset]) w256 (by decide) (by decide +kernel) (consbad n44 (consbad n205 (consbad n208 (nilbad 4))))

def w257 : List Mask := [15,64,240,4369,8738,65416]
theorem n257 : impossible 5 w257.toFinset :=
  closeState (known := [w54.toFinset, w180.toFinset]) w257 (by decide) (by decide +kernel) (consbad n54 (consbad n180 (nilbad 4)))

def w258 : List Mask := [15,64,240,4369,12066,63624]
theorem n258 : impossible 5 w258.toFinset :=
  closeState (known := [w56.toFinset, w181.toFinset]) w258 (by decide) (by decide +kernel) (consbad n56 (consbad n181 (nilbad 4)))

def w259 : List Mask := [15,64,240,4369,34952,65314]
theorem n259 : impossible 5 w259.toFinset :=
  closeState (known := [w45.toFinset, w62.toFinset, w182.toFinset]) w259 (by decide) (by decide +kernel) (consbad n45 (consbad n62 (consbad n182 (nilbad 4))))

def w260 : List Mask := [15,64,240,4369,36744,61986]
theorem n260 : impossible 5 w260.toFinset :=
  closeState (known := [w63.toFinset, w183.toFinset]) w260 (by decide) (by decide +kernel) (consbad n63 (consbad n183 (nilbad 4)))

def w261 : List Mask := [15,64,3840,4593,34952,61986]
theorem n261 : impossible 5 w261.toFinset :=
  closeState (known := [w45.toFinset, w84.toFinset, w91.toFinset, w184.toFinset]) w261 (by decide) (by decide +kernel) (consbad n45 (consbad n84 (consbad n91 (consbad n184 (nilbad 4)))))

def w262 : List Mask := [15,64,4369,8738,35064,65280]
theorem n262 : impossible 5 w262.toFinset :=
  closeState (known := [w96.toFinset, w185.toFinset]) w262 (by decide) (by decide +kernel) (consbad n96 (consbad n185 (nilbad 4)))

def w263 : List Mask := [15,64,4593,8738,34952,65280]
theorem n263 : impossible 5 w263.toFinset :=
  closeState (known := [w45.toFinset, w107.toFinset, w120.toFinset, w186.toFinset]) w263 (by decide) (by decide +kernel) (consbad n45 (consbad n107 (consbad n120 (consbad n186 (nilbad 4)))))

def w264 : List Mask := [15,64,4593,12066,34952,61440]
theorem n264 : impossible 5 w264.toFinset :=
  closeState (known := [w45.toFinset, w125.toFinset, w138.toFinset, w187.toFinset]) w264 (by decide) (by decide +kernel) (consbad n45 (consbad n125 (consbad n138 (consbad n187 (nilbad 4)))))

def w265 : List Mask := [15,96,3840,4369,8738,63624]
theorem n265 : impossible 5 w265.toFinset :=
  closeState (known := [w46.toFinset, w47.toFinset, w48.toFinset]) w265 (by decide) (by decide +kernel) (consbad n46 (consbad n47 (consbad n48 (nilbad 4))))

def w266 : List Mask := [15,96,3840,4369,34952,61986]
theorem n266 : impossible 5 w266.toFinset :=
  closeState (known := [w46.toFinset, w49.toFinset, w50.toFinset]) w266 (by decide) (by decide +kernel) (consbad n46 (consbad n49 (consbad n50 (nilbad 4))))

def w267 : List Mask := [15,96,3840,4369,43690,61440]
theorem n267 : impossible 5 w267.toFinset :=
  closeState (known := [w46.toFinset, w51.toFinset, w52.toFinset]) w267 (by decide) (by decide +kernel) (consbad n46 (consbad n51 (consbad n52 (nilbad 4))))

def w268 : List Mask := [15,96,4369,8738,34952,65280]
theorem n268 : impossible 5 w268.toFinset :=
  closeState (known := [w47.toFinset, w49.toFinset, w51.toFinset]) w268 (by decide) (by decide +kernel) (consbad n47 (consbad n49 (consbad n51 (nilbad 4))))

def w269 : List Mask := [15,96,4369,8738,36744,61440]
theorem n269 : impossible 5 w269.toFinset :=
  closeState (known := [w47.toFinset, w50.toFinset, w52.toFinset]) w269 (by decide) (by decide +kernel) (consbad n47 (consbad n50 (consbad n52 (nilbad 4))))

def w270 : List Mask := [15,96,4369,12066,34952,61440]
theorem n270 : impossible 5 w270.toFinset :=
  closeState (known := [w48.toFinset, w49.toFinset, w52.toFinset]) w270 (by decide) (by decide +kernel) (consbad n48 (consbad n49 (consbad n52 (nilbad 4))))

def w271 : List Mask := [15,240,3840,4369,8746,62532]
theorem n271 : impossible 5 w271.toFinset :=
  closeState (known := [w53.toFinset, w55.toFinset, w81.toFinset]) w271 (by decide) (by decide +kernel) (consbad n53 (consbad n55 (consbad n81 (nilbad 4))))

def w272 : List Mask := [15,240,3840,4369,8802,63624]
theorem n272 : impossible 5 w272.toFinset :=
  closeState (known := [w54.toFinset, w56.toFinset]) w272 (by decide) (by decide +kernel) (consbad n54 (consbad n56 (nilbad 4)))

def w273 : List Mask := [15,240,3840,4369,17476,61994]
theorem n273 : impossible 5 w273.toFinset :=
  closeState (known := [w57.toFinset, w58.toFinset, w83.toFinset]) w273 (by decide) (by decide +kernel) (consbad n57 (consbad n58 (consbad n83 (nilbad 4))))

def w274 : List Mask := [15,240,3840,4369,26214,64170]
theorem n274 : impossible 5 w274.toFinset :=
  closeState (known := [w46.toFinset, w59.toFinset, w60.toFinset]) w274 (by decide) (by decide +kernel) (consbad n46 (consbad n59 (consbad n60 (nilbad 4))))

def w275 : List Mask := [15,240,3840,4369,34952,62050]
theorem n275 : impossible 5 w275.toFinset :=
  closeState (known := [w62.toFinset, w63.toFinset, w84.toFinset]) w275 (by decide) (by decide +kernel) (consbad n62 (consbad n63 (consbad n84 (nilbad 4))))

def w276 : List Mask := [15,240,3840,4369,43690,63078]
theorem n276 : impossible 5 w276.toFinset :=
  closeState (known := [w64.toFinset, w65.toFinset, w85.toFinset]) w276 (by decide) (by decide +kernel) (consbad n64 (consbad n65 (consbad n85 (nilbad 4))))

def w277 : List Mask := [15,240,3840,4369,63078,64170]
theorem n277 : impossible 5 w277.toFinset :=
  closeState (known := [w46.toFinset, w67.toFinset, w68.toFinset, w86.toFinset]) w277 (by decide) (by decide +kernel) (consbad n46 (consbad n67 (consbad n68 (consbad n86 (nilbad 4)))))

def w278 : List Mask := [15,240,3840,4377,8738,62532]
theorem n278 : impossible 5 w278.toFinset :=
  closeState (known := [w70.toFinset, w71.toFinset, w87.toFinset]) w278 (by decide) (by decide +kernel) (consbad n70 (consbad n71 (consbad n87 (nilbad 4))))

def w279 : List Mask := [15,240,3840,4377,17476,61986]
theorem n279 : impossible 5 w279.toFinset :=
  closeState (known := [w72.toFinset, w73.toFinset, w88.toFinset]) w279 (by decide) (by decide +kernel) (consbad n72 (consbad n73 (consbad n88 (nilbad 4))))

def w280 : List Mask := [15,240,3848,4369,8738,62532]
theorem n280 : impossible 5 w280.toFinset :=
  closeState (known := [w55.toFinset, w89.toFinset]) w280 (by decide) (by decide +kernel) (consbad n55 (consbad n89 (nilbad 4)))

def w281 : List Mask := [15,240,3848,4369,17476,61986]
theorem n281 : impossible 5 w281.toFinset :=
  closeState (known := [w57.toFinset, w90.toFinset]) w281 (by decide) (by decide +kernel) (consbad n57 (consbad n90 (nilbad 4)))

def w282 : List Mask := [15,240,3904,4369,8738,63624]
theorem n282 : impossible 5 w282.toFinset :=
  closeState (known := [w56.toFinset]) w282 (by decide) (by decide +kernel) (consbad n56 (nilbad 4))

def w283 : List Mask := [15,240,3904,4369,34952,61986]
theorem n283 : impossible 5 w283.toFinset :=
  closeState (known := [w62.toFinset, w91.toFinset]) w283 (by decide) (by decide +kernel) (consbad n62 (consbad n91 (nilbad 4)))

def w284 : List Mask := [15,240,4352,8738,17476,39321]
theorem n284 : impossible 5 w284.toFinset :=
  closeState (known := [w74.toFinset, w75.toFinset, w93.toFinset, w188.toFinset, w190.toFinset]) w284 (by decide) (by decide +kernel) (consbad n74 (consbad n75 (consbad n93 (consbad n188 (consbad n190 (nilbad 4))))))

def w285 : List Mask := [15,240,4353,8738,17476,34952]
theorem n285 : impossible 5 w285.toFinset :=
  closeState (known := [w94.toFinset, w189.toFinset]) w285 (by decide) (by decide +kernel) (consbad n94 (consbad n189 (nilbad 4)))

def w286 : List Mask := [15,240,4369,8738,17476,39304]
theorem n286 : impossible 5 w286.toFinset :=
  closeState (known := [w191.toFinset]) w286 (by decide) (by decide +kernel) (consbad n191 (nilbad 4))

def w287 : List Mask := [15,240,4369,8738,17476,40840]
theorem n287 : impossible 5 w287.toFinset :=
  closeState (known := []) w287 (by decide) (by decide +kernel) (nilbad 4)

def w288 : List Mask := [15,240,4369,8738,17476,63880]
theorem n288 : impossible 5 w288.toFinset :=
  closeState (known := []) w288 (by decide) (by decide +kernel) (nilbad 4)

def w289 : List Mask := [15,240,4369,8738,17476,65288]
theorem n289 : impossible 5 w289.toFinset :=
  closeState (known := [w57.toFinset, w101.toFinset]) w289 (by decide) (by decide +kernel) (consbad n57 (consbad n101 (nilbad 4)))

def w290 : List Mask := [15,240,4369,8738,17476,65416]
theorem n290 : impossible 5 w290.toFinset :=
  closeState (known := []) w290 (by decide) (by decide +kernel) (nilbad 4)

def w291 : List Mask := [15,240,4369,8738,17476,65450]
theorem n291 : impossible 5 w291.toFinset :=
  closeState (known := [w59.toFinset]) w291 (by decide) (by decide +kernel) (consbad n59 (nilbad 4))

def w292 : List Mask := [15,240,4369,8738,17487,65416]
theorem n292 : impossible 5 w292.toFinset :=
  closeState (known := []) w292 (by decide) (by decide +kernel) (nilbad 4)

def w293 : List Mask := [15,240,4369,8738,17732,63624]
theorem n293 : impossible 5 w293.toFinset :=
  closeState (known := []) w293 (by decide) (by decide +kernel) (nilbad 4)

def w294 : List Mask := [15,240,4369,8738,20292,39048]
theorem n294 : impossible 5 w294.toFinset :=
  closeState (known := []) w294 (by decide) (by decide +kernel) (nilbad 4)

def w295 : List Mask := [15,240,4369,8738,20292,61448]
theorem n295 : impossible 5 w295.toFinset :=
  closeState (known := [w58.toFinset, w102.toFinset]) w295 (by decide) (by decide +kernel) (consbad n58 (consbad n102 (nilbad 4)))

def w296 : List Mask := [15,240,4369,8738,20292,64170]
theorem n296 : impossible 5 w296.toFinset :=
  closeState (known := [w60.toFinset]) w296 (by decide) (by decide +kernel) (consbad n60 (nilbad 4))

def w297 : List Mask := [15,240,4369,8738,20292,65416]
theorem n297 : impossible 5 w297.toFinset :=
  closeState (known := []) w297 (by decide) (by decide +kernel) (nilbad 4)

def w298 : List Mask := [15,240,4369,8738,20303,63624]
theorem n298 : impossible 5 w298.toFinset :=
  closeState (known := []) w298 (by decide) (by decide +kernel) (nilbad 4)

def w299 : List Mask := [15,240,4369,8738,21572,36744]
theorem n299 : impossible 5 w299.toFinset :=
  closeState (known := []) w299 (by decide) (by decide +kernel) (nilbad 4)

def w300 : List Mask := [15,240,4369,8738,21828,34952]
theorem n300 : impossible 5 w300.toFinset :=
  closeState (known := [w74.toFinset, w95.toFinset, w103.toFinset, w192.toFinset]) w300 (by decide) (by decide +kernel) (consbad n74 (consbad n95 (consbad n103 (consbad n192 (nilbad 4)))))

def w301 : List Mask := [15,240,4369,8738,24388,34952]
theorem n301 : impossible 5 w301.toFinset :=
  closeState (known := [w104.toFinset]) w301 (by decide) (by decide +kernel) (consbad n104 (nilbad 4))

def w302 : List Mask := [15,240,4369,8738,26214,65416]
theorem n302 : impossible 5 w302.toFinset :=
  closeState (known := [w47.toFinset, w59.toFinset]) w302 (by decide) (by decide +kernel) (consbad n47 (consbad n59 (nilbad 4)))

def w303 : List Mask := [15,240,4369,8738,28518,63624]
theorem n303 : impossible 5 w303.toFinset :=
  closeState (known := [w60.toFinset]) w303 (by decide) (by decide +kernel) (consbad n60 (nilbad 4))

def w304 : List Mask := [15,240,4369,8738,34952,62788]
theorem n304 : impossible 5 w304.toFinset :=
  closeState (known := [w106.toFinset]) w304 (by decide) (by decide +kernel) (consbad n106 (nilbad 4))

def w305 : List Mask := [15,240,4369,8738,34952,65344]
theorem n305 : impossible 5 w305.toFinset :=
  closeState (known := [w62.toFinset, w107.toFinset]) w305 (by decide) (by decide +kernel) (consbad n62 (consbad n107 (nilbad 4)))

def w306 : List Mask := [15,240,4369,8738,34952,65348]
theorem n306 : impossible 5 w306.toFinset :=
  closeState (known := [w108.toFinset]) w306 (by decide) (by decide +kernel) (consbad n108 (nilbad 4))

def w307 : List Mask := [15,240,4369,8738,34952,65359]
theorem n307 : impossible 5 w307.toFinset :=
  closeState (known := [w109.toFinset]) w307 (by decide) (by decide +kernel) (consbad n109 (nilbad 4))

def w308 : List Mask := [15,240,4369,8738,34952,65382]
theorem n308 : impossible 5 w308.toFinset :=
  closeState (known := [w64.toFinset, w110.toFinset]) w308 (by decide) (by decide +kernel) (consbad n64 (consbad n110 (nilbad 4)))

def w309 : List Mask := [15,240,4369,8738,35064,65348]
theorem n309 : impossible 5 w309.toFinset :=
  closeState (known := [w111.toFinset]) w309 (by decide) (by decide +kernel) (consbad n111 (nilbad 4))

def w310 : List Mask := [15,240,4369,8738,35208,62532]
theorem n310 : impossible 5 w310.toFinset :=
  closeState (known := []) w310 (by decide) (by decide +kernel) (nilbad 4)

def w311 : List Mask := [15,240,4369,8738,36744,61504]
theorem n311 : impossible 5 w311.toFinset :=
  closeState (known := [w63.toFinset]) w311 (by decide) (by decide +kernel) (consbad n63 (nilbad 4))

def w312 : List Mask := [15,240,4369,8738,36744,62543]
theorem n312 : impossible 5 w312.toFinset :=
  closeState (known := []) w312 (by decide) (by decide +kernel) (nilbad 4)

def w313 : List Mask := [15,240,4369,8738,36744,63078]
theorem n313 : impossible 5 w313.toFinset :=
  closeState (known := [w65.toFinset]) w313 (by decide) (by decide +kernel) (consbad n65 (nilbad 4))

def w314 : List Mask := [15,240,4369,8738,36744,65348]
theorem n314 : impossible 5 w314.toFinset :=
  closeState (known := [w112.toFinset]) w314 (by decide) (by decide +kernel) (consbad n112 (nilbad 4))

def w315 : List Mask := [15,240,4369,8738,39321,65348]
theorem n315 : impossible 5 w315.toFinset :=
  closeState (known := [w113.toFinset]) w315 (by decide) (by decide +kernel) (consbad n113 (nilbad 4))

def w316 : List Mask := [15,240,4369,8738,43690,65348]
theorem n316 : impossible 5 w316.toFinset :=
  closeState (known := [w64.toFinset, w115.toFinset]) w316 (by decide) (by decide +kernel) (consbad n64 (consbad n115 (nilbad 4)))

def w317 : List Mask := [15,240,4369,8738,44970,62532]
theorem n317 : impossible 5 w317.toFinset :=
  closeState (known := [w65.toFinset]) w317 (by decide) (by decide +kernel) (consbad n65 (nilbad 4))

def w318 : List Mask := [15,240,4369,8738,62532,65416]
theorem n318 : impossible 5 w318.toFinset :=
  closeState (known := []) w318 (by decide) (by decide +kernel) (nilbad 4)

def w319 : List Mask := [15,240,4369,8738,63624,65348]
theorem n319 : impossible 5 w319.toFinset :=
  closeState (known := [w116.toFinset]) w319 (by decide) (by decide +kernel) (consbad n116 (nilbad 4))

def w320 : List Mask := [15,240,4369,8738,65348,65416]
theorem n320 : impossible 5 w320.toFinset :=
  closeState (known := [w117.toFinset]) w320 (by decide) (by decide +kernel) (consbad n117 (nilbad 4))

def w321 : List Mask := [15,240,4369,8746,17476,65280]
theorem n321 : impossible 5 w321.toFinset :=
  closeState (known := [w53.toFinset, w57.toFinset, w118.toFinset, w193.toFinset]) w321 (by decide) (by decide +kernel) (consbad n53 (consbad n57 (consbad n118 (consbad n193 (nilbad 4)))))

def w322 : List Mask := [15,240,4369,8746,20292,61440]
theorem n322 : impossible 5 w322.toFinset :=
  closeState (known := [w53.toFinset, w58.toFinset, w119.toFinset]) w322 (by decide) (by decide +kernel) (consbad n53 (consbad n58 (consbad n119 (nilbad 4))))

def w323 : List Mask := [15,240,4369,8802,34952,65280]
theorem n323 : impossible 5 w323.toFinset :=
  closeState (known := [w54.toFinset, w62.toFinset, w96.toFinset, w120.toFinset]) w323 (by decide) (by decide +kernel) (consbad n54 (consbad n62 (consbad n96 (consbad n120 (nilbad 4)))))

def w324 : List Mask := [15,240,4369,8802,36744,61440]
theorem n324 : impossible 5 w324.toFinset :=
  closeState (known := [w54.toFinset, w63.toFinset]) w324 (by decide) (by decide +kernel) (consbad n54 (consbad n63 (nilbad 4)))

def w325 : List Mask := [15,240,4369,8994,17476,63624]
theorem n325 : impossible 5 w325.toFinset :=
  closeState (known := []) w325 (by decide) (by decide +kernel) (nilbad 4)

def w326 : List Mask := [15,240,4369,8994,34952,62532]
theorem n326 : impossible 5 w326.toFinset :=
  closeState (known := [w121.toFinset]) w326 (by decide) (by decide +kernel) (consbad n121 (nilbad 4))

def w327 : List Mask := [15,240,4369,12066,17476,39048]
theorem n327 : impossible 5 w327.toFinset :=
  closeState (known := []) w327 (by decide) (by decide +kernel) (nilbad 4)

def w328 : List Mask := [15,240,4369,12066,17476,61448]
theorem n328 : impossible 5 w328.toFinset :=
  closeState (known := [w57.toFinset, w123.toFinset]) w328 (by decide) (by decide +kernel) (consbad n57 (consbad n123 (nilbad 4)))

def w329 : List Mask := [15,240,4369,12066,17476,64170]
theorem n329 : impossible 5 w329.toFinset :=
  closeState (known := [w60.toFinset]) w329 (by decide) (by decide +kernel) (consbad n60 (nilbad 4))

def w330 : List Mask := [15,240,4369,12066,17476,65416]
theorem n330 : impossible 5 w330.toFinset :=
  closeState (known := []) w330 (by decide) (by decide +kernel) (nilbad 4)

def w331 : List Mask := [15,240,4369,12066,17476,65450]
theorem n331 : impossible 5 w331.toFinset :=
  closeState (known := [w61.toFinset]) w331 (by decide) (by decide +kernel) (consbad n61 (nilbad 4))

def w332 : List Mask := [15,240,4369,12066,17487,63624]
theorem n332 : impossible 5 w332.toFinset :=
  closeState (known := []) w332 (by decide) (by decide +kernel) (nilbad 4)

def w333 : List Mask := [15,240,4369,12066,20292,63624]
theorem n333 : impossible 5 w333.toFinset :=
  closeState (known := []) w333 (by decide) (by decide +kernel) (nilbad 4)

def w334 : List Mask := [15,240,4369,12066,21572,34952]
theorem n334 : impossible 5 w334.toFinset :=
  closeState (known := [w124.toFinset]) w334 (by decide) (by decide +kernel) (consbad n124 (nilbad 4))

def w335 : List Mask := [15,240,4369,12066,26214,63624]
theorem n335 : impossible 5 w335.toFinset :=
  closeState (known := [w48.toFinset, w59.toFinset]) w335 (by decide) (by decide +kernel) (consbad n48 (consbad n59 (nilbad 4)))

def w336 : List Mask := [15,240,4369,12066,28518,63624]
theorem n336 : impossible 5 w336.toFinset :=
  closeState (known := [w48.toFinset, w61.toFinset]) w336 (by decide) (by decide +kernel) (consbad n48 (consbad n61 (nilbad 4)))

def w337 : List Mask := [15,240,4369,12066,34952,61504]
theorem n337 : impossible 5 w337.toFinset :=
  closeState (known := [w62.toFinset, w125.toFinset]) w337 (by decide) (by decide +kernel) (consbad n62 (consbad n125 (nilbad 4)))

def w338 : List Mask := [15,240,4369,12066,34952,62543]
theorem n338 : impossible 5 w338.toFinset :=
  closeState (known := [w126.toFinset]) w338 (by decide) (by decide +kernel) (consbad n126 (nilbad 4))

def w339 : List Mask := [15,240,4369,12066,34952,63078]
theorem n339 : impossible 5 w339.toFinset :=
  closeState (known := [w65.toFinset, w127.toFinset]) w339 (by decide) (by decide +kernel) (consbad n65 (consbad n127 (nilbad 4)))

def w340 : List Mask := [15,240,4369,12066,34952,65348]
theorem n340 : impossible 5 w340.toFinset :=
  closeState (known := [w128.toFinset]) w340 (by decide) (by decide +kernel) (consbad n128 (nilbad 4))

def w341 : List Mask := [15,240,4369,12066,34952,65382]
theorem n341 : impossible 5 w341.toFinset :=
  closeState (known := [w66.toFinset, w129.toFinset]) w341 (by decide) (by decide +kernel) (consbad n66 (consbad n129 (nilbad 4)))

def w342 : List Mask := [15,240,4369,12066,35064,62532]
theorem n342 : impossible 5 w342.toFinset :=
  closeState (known := [w130.toFinset]) w342 (by decide) (by decide +kernel) (consbad n130 (nilbad 4))

def w343 : List Mask := [15,240,4369,12066,36744,62532]
theorem n343 : impossible 5 w343.toFinset :=
  closeState (known := [w131.toFinset]) w343 (by decide) (by decide +kernel) (consbad n131 (nilbad 4))

def w344 : List Mask := [15,240,4369,12066,39321,62532]
theorem n344 : impossible 5 w344.toFinset :=
  closeState (known := [w132.toFinset]) w344 (by decide) (by decide +kernel) (consbad n132 (nilbad 4))

def w345 : List Mask := [15,240,4369,12066,43690,62532]
theorem n345 : impossible 5 w345.toFinset :=
  closeState (known := [w64.toFinset, w134.toFinset]) w345 (by decide) (by decide +kernel) (consbad n64 (consbad n134 (nilbad 4)))

def w346 : List Mask := [15,240,4369,12066,44970,62532]
theorem n346 : impossible 5 w346.toFinset :=
  closeState (known := [w66.toFinset, w135.toFinset]) w346 (by decide) (by decide +kernel) (consbad n66 (consbad n135 (nilbad 4)))

def w347 : List Mask := [15,240,4369,12066,62532,63624]
theorem n347 : impossible 5 w347.toFinset :=
  closeState (known := [w136.toFinset]) w347 (by decide) (by decide +kernel) (consbad n136 (nilbad 4))

def w348 : List Mask := [15,240,4369,12074,17476,61440]
theorem n348 : impossible 5 w348.toFinset :=
  closeState (known := [w55.toFinset, w57.toFinset, w137.toFinset]) w348 (by decide) (by decide +kernel) (consbad n55 (consbad n57 (consbad n137 (nilbad 4))))

def w349 : List Mask := [15,240,4369,12130,34952,61440]
theorem n349 : impossible 5 w349.toFinset :=
  closeState (known := [w56.toFinset, w62.toFinset, w138.toFinset]) w349 (by decide) (by decide +kernel) (consbad n56 (consbad n62 (consbad n138 (nilbad 4))))

def w350 : List Mask := [15,240,4369,12834,17476,36744]
theorem n350 : impossible 5 w350.toFinset :=
  closeState (known := []) w350 (by decide) (by decide +kernel) (nilbad 4)

def w351 : List Mask := [15,240,4369,12834,20292,34952]
theorem n351 : impossible 5 w351.toFinset :=
  closeState (known := [w139.toFinset]) w351 (by decide) (by decide +kernel) (consbad n139 (nilbad 4))

def w352 : List Mask := [15,240,4369,13090,17476,34952]
theorem n352 : impossible 5 w352.toFinset :=
  closeState (known := [w75.toFinset, w97.toFinset, w140.toFinset, w194.toFinset]) w352 (by decide) (by decide +kernel) (consbad n75 (consbad n97 (consbad n140 (consbad n194 (nilbad 4)))))

def w353 : List Mask := [15,240,4369,16162,17476,34952]
theorem n353 : impossible 5 w353.toFinset :=
  closeState (known := [w141.toFinset]) w353 (by decide) (by decide +kernel) (consbad n141 (nilbad 4))

def w354 : List Mask := [15,240,4369,17476,34952,62242]
theorem n354 : impossible 5 w354.toFinset :=
  closeState (known := [w142.toFinset]) w354 (by decide) (by decide +kernel) (consbad n142 (nilbad 4))

def w355 : List Mask := [15,240,4369,17476,34952,65314]
theorem n355 : impossible 5 w355.toFinset :=
  closeState (known := [w143.toFinset]) w355 (by decide) (by decide +kernel) (consbad n143 (nilbad 4))

def w356 : List Mask := [15,240,4369,17476,35064,65314]
theorem n356 : impossible 5 w356.toFinset :=
  closeState (known := [w144.toFinset]) w356 (by decide) (by decide +kernel) (consbad n144 (nilbad 4))

def w357 : List Mask := [15,240,4369,17476,35208,61986]
theorem n357 : impossible 5 w357.toFinset :=
  closeState (known := []) w357 (by decide) (by decide +kernel) (nilbad 4)

def w358 : List Mask := [15,240,4369,17476,36744,65314]
theorem n358 : impossible 5 w358.toFinset :=
  closeState (known := [w145.toFinset]) w358 (by decide) (by decide +kernel) (consbad n145 (nilbad 4))

def w359 : List Mask := [15,240,4369,17476,39321,65314]
theorem n359 : impossible 5 w359.toFinset :=
  closeState (known := [w146.toFinset]) w359 (by decide) (by decide +kernel) (consbad n146 (nilbad 4))

def w360 : List Mask := [15,240,4369,17476,43690,65314]
theorem n360 : impossible 5 w360.toFinset :=
  closeState (known := [w64.toFinset, w148.toFinset, w195.toFinset]) w360 (by decide) (by decide +kernel) (consbad n64 (consbad n148 (consbad n195 (nilbad 4))))

def w361 : List Mask := [15,240,4369,17476,44970,61986]
theorem n361 : impossible 5 w361.toFinset :=
  closeState (known := [w65.toFinset]) w361 (by decide) (by decide +kernel) (consbad n65 (nilbad 4))

def w362 : List Mask := [15,240,4369,17476,44970,65314]
theorem n362 : impossible 5 w362.toFinset :=
  closeState (known := [w66.toFinset, w149.toFinset]) w362 (by decide) (by decide +kernel) (consbad n66 (consbad n149 (nilbad 4)))

def w363 : List Mask := [15,240,4369,17476,61986,65416]
theorem n363 : impossible 5 w363.toFinset :=
  closeState (known := []) w363 (by decide) (by decide +kernel) (nilbad 4)

def w364 : List Mask := [15,240,4369,17476,61986,65450]
theorem n364 : impossible 5 w364.toFinset :=
  closeState (known := [w67.toFinset]) w364 (by decide) (by decide +kernel) (consbad n67 (nilbad 4))

def w365 : List Mask := [15,240,4369,17476,63624,65314]
theorem n365 : impossible 5 w365.toFinset :=
  closeState (known := [w150.toFinset]) w365 (by decide) (by decide +kernel) (consbad n150 (nilbad 4))

def w366 : List Mask := [15,240,4369,17476,64170,65314]
theorem n366 : impossible 5 w366.toFinset :=
  closeState (known := [w68.toFinset, w151.toFinset]) w366 (by decide) (by decide +kernel) (consbad n68 (consbad n151 (nilbad 4)))

def w367 : List Mask := [15,240,4369,17476,65314,65416]
theorem n367 : impossible 5 w367.toFinset :=
  closeState (known := [w152.toFinset]) w367 (by decide) (by decide +kernel) (consbad n152 (nilbad 4))

def w368 : List Mask := [15,240,4369,17476,65314,65450]
theorem n368 : impossible 5 w368.toFinset :=
  closeState (known := [w69.toFinset, w153.toFinset]) w368 (by decide) (by decide +kernel) (consbad n69 (consbad n153 (nilbad 4)))

def w369 : List Mask := [15,240,4369,17487,34952,65314]
theorem n369 : impossible 5 w369.toFinset :=
  closeState (known := [w154.toFinset]) w369 (by decide) (by decide +kernel) (consbad n154 (nilbad 4))

def w370 : List Mask := [15,240,4369,17487,36744,61986]
theorem n370 : impossible 5 w370.toFinset :=
  closeState (known := []) w370 (by decide) (by decide +kernel) (nilbad 4)

def w371 : List Mask := [15,240,4369,17732,34952,61986]
theorem n371 : impossible 5 w371.toFinset :=
  closeState (known := [w155.toFinset]) w371 (by decide) (by decide +kernel) (consbad n155 (nilbad 4))

def w372 : List Mask := [15,240,4369,20292,34952,65314]
theorem n372 : impossible 5 w372.toFinset :=
  closeState (known := [w156.toFinset]) w372 (by decide) (by decide +kernel) (consbad n156 (nilbad 4))

def w373 : List Mask := [15,240,4369,20292,35064,61986]
theorem n373 : impossible 5 w373.toFinset :=
  closeState (known := [w157.toFinset]) w373 (by decide) (by decide +kernel) (consbad n157 (nilbad 4))

def w374 : List Mask := [15,240,4369,20292,36744,61986]
theorem n374 : impossible 5 w374.toFinset :=
  closeState (known := [w158.toFinset]) w374 (by decide) (by decide +kernel) (consbad n158 (nilbad 4))

def w375 : List Mask := [15,240,4369,20292,39321,61986]
theorem n375 : impossible 5 w375.toFinset :=
  closeState (known := [w159.toFinset]) w375 (by decide) (by decide +kernel) (consbad n159 (nilbad 4))

def w376 : List Mask := [15,240,4369,20292,43690,61986]
theorem n376 : impossible 5 w376.toFinset :=
  closeState (known := [w64.toFinset, w161.toFinset]) w376 (by decide) (by decide +kernel) (consbad n64 (consbad n161 (nilbad 4)))

def w377 : List Mask := [15,240,4369,20292,61986,63624]
theorem n377 : impossible 5 w377.toFinset :=
  closeState (known := [w162.toFinset]) w377 (by decide) (by decide +kernel) (consbad n162 (nilbad 4))

def w378 : List Mask := [15,240,4369,20292,61986,64170]
theorem n378 : impossible 5 w378.toFinset :=
  closeState (known := [w68.toFinset, w163.toFinset]) w378 (by decide) (by decide +kernel) (consbad n68 (consbad n163 (nilbad 4)))

def w379 : List Mask := [15,240,4369,20303,34952,61986]
theorem n379 : impossible 5 w379.toFinset :=
  closeState (known := [w164.toFinset]) w379 (by decide) (by decide +kernel) (consbad n164 (nilbad 4))

def w380 : List Mask := [15,240,4369,26214,34952,65314]
theorem n380 : impossible 5 w380.toFinset :=
  closeState (known := [w49.toFinset, w59.toFinset, w98.toFinset, w165.toFinset]) w380 (by decide) (by decide +kernel) (consbad n49 (consbad n59 (consbad n98 (consbad n165 (nilbad 4)))))

def w381 : List Mask := [15,240,4369,26214,36744,61986]
theorem n381 : impossible 5 w381.toFinset :=
  closeState (known := [w50.toFinset, w59.toFinset]) w381 (by decide) (by decide +kernel) (consbad n50 (consbad n59 (nilbad 4)))

def w382 : List Mask := [15,240,4369,26214,43690,65280]
theorem n382 : impossible 5 w382.toFinset :=
  closeState (known := [w51.toFinset, w59.toFinset, w64.toFinset, w166.toFinset]) w382 (by decide) (by decide +kernel) (consbad n51 (consbad n59 (consbad n64 (consbad n166 (nilbad 4)))))

def w383 : List Mask := [15,240,4369,26214,44970,61440]
theorem n383 : impossible 5 w383.toFinset :=
  closeState (known := [w52.toFinset, w59.toFinset, w65.toFinset]) w383 (by decide) (by decide +kernel) (consbad n52 (consbad n59 (consbad n65 (nilbad 4))))

def w384 : List Mask := [15,240,4369,28518,34952,61986]
theorem n384 : impossible 5 w384.toFinset :=
  closeState (known := [w60.toFinset, w167.toFinset]) w384 (by decide) (by decide +kernel) (consbad n60 (consbad n167 (nilbad 4)))

def w385 : List Mask := [15,240,4369,28518,34952,65314]
theorem n385 : impossible 5 w385.toFinset :=
  closeState (known := [w49.toFinset, w61.toFinset, w168.toFinset]) w385 (by decide) (by decide +kernel) (consbad n49 (consbad n61 (consbad n168 (nilbad 4))))

def w386 : List Mask := [15,240,4369,28518,43690,61440]
theorem n386 : impossible 5 w386.toFinset :=
  closeState (known := [w60.toFinset, w64.toFinset, w169.toFinset]) w386 (by decide) (by decide +kernel) (consbad n60 (consbad n64 (consbad n169 (nilbad 4))))

def w387 : List Mask := [15,240,4369,28518,44970,61440]
theorem n387 : impossible 5 w387.toFinset :=
  closeState (known := [w52.toFinset, w61.toFinset, w66.toFinset, w170.toFinset]) w387 (by decide) (by decide +kernel) (consbad n52 (consbad n61 (consbad n66 (consbad n170 (nilbad 4)))))

def w388 : List Mask := [15,240,4369,34952,61986,65348]
theorem n388 : impossible 5 w388.toFinset :=
  closeState (known := [w171.toFinset]) w388 (by decide) (by decide +kernel) (consbad n171 (nilbad 4))

def w389 : List Mask := [15,240,4369,34952,61986,65382]
theorem n389 : impossible 5 w389.toFinset :=
  closeState (known := [w68.toFinset, w172.toFinset]) w389 (by decide) (by decide +kernel) (consbad n68 (consbad n172 (nilbad 4)))

def w390 : List Mask := [15,240,4369,34952,62532,65314]
theorem n390 : impossible 5 w390.toFinset :=
  closeState (known := [w173.toFinset]) w390 (by decide) (by decide +kernel) (consbad n173 (nilbad 4))

def w391 : List Mask := [15,240,4369,34952,63078,65314]
theorem n391 : impossible 5 w391.toFinset :=
  closeState (known := [w49.toFinset, w67.toFinset, w174.toFinset]) w391 (by decide) (by decide +kernel) (consbad n49 (consbad n67 (consbad n174 (nilbad 4))))

def w392 : List Mask := [15,240,4369,34952,65314,65348]
theorem n392 : impossible 5 w392.toFinset :=
  closeState (known := [w175.toFinset]) w392 (by decide) (by decide +kernel) (consbad n175 (nilbad 4))

def w393 : List Mask := [15,240,4369,34952,65314,65382]
theorem n393 : impossible 5 w393.toFinset :=
  closeState (known := [w49.toFinset, w69.toFinset, w176.toFinset]) w393 (by decide) (by decide +kernel) (consbad n49 (consbad n69 (consbad n176 (nilbad 4))))

def w394 : List Mask := [15,240,4369,36744,61986,62532]
theorem n394 : impossible 5 w394.toFinset :=
  closeState (known := []) w394 (by decide) (by decide +kernel) (nilbad 4)

def w395 : List Mask := [15,240,4369,36744,61986,63078]
theorem n395 : impossible 5 w395.toFinset :=
  closeState (known := [w50.toFinset, w67.toFinset]) w395 (by decide) (by decide +kernel) (consbad n50 (consbad n67 (nilbad 4)))

def w396 : List Mask := [15,240,4377,8738,17476,65280]
theorem n396 : impossible 5 w396.toFinset :=
  closeState (known := [w70.toFinset, w72.toFinset, w177.toFinset, w196.toFinset]) w396 (by decide) (by decide +kernel) (consbad n70 (consbad n72 (consbad n177 (consbad n196 (nilbad 4)))))

def w397 : List Mask := [15,240,4377,8738,20292,61440]
theorem n397 : impossible 5 w397.toFinset :=
  closeState (known := [w70.toFinset, w73.toFinset, w178.toFinset]) w397 (by decide) (by decide +kernel) (consbad n70 (consbad n73 (consbad n178 (nilbad 4))))

def w398 : List Mask := [15,240,4377,12066,17476,61440]
theorem n398 : impossible 5 w398.toFinset :=
  closeState (known := [w71.toFinset, w72.toFinset, w179.toFinset]) w398 (by decide) (by decide +kernel) (consbad n71 (consbad n72 (consbad n179 (nilbad 4))))

def w399 : List Mask := [15,240,4593,8738,34952,65348]
theorem n399 : impossible 5 w399.toFinset :=
  closeState (known := [w111.toFinset]) w399 (by decide) (by decide +kernel) (consbad n111 (nilbad 4))

def w400 : List Mask := [15,240,4593,12066,34952,62532]
theorem n400 : impossible 5 w400.toFinset :=
  closeState (known := [w130.toFinset]) w400 (by decide) (by decide +kernel) (consbad n130 (nilbad 4))

def w401 : List Mask := [15,240,4593,17476,34952,65314]
theorem n401 : impossible 5 w401.toFinset :=
  closeState (known := [w45.toFinset, w144.toFinset]) w401 (by decide) (by decide +kernel) (consbad n45 (consbad n144 (nilbad 4)))

def w402 : List Mask := [15,240,4593,20292,34952,61986]
theorem n402 : impossible 5 w402.toFinset :=
  closeState (known := [w157.toFinset]) w402 (by decide) (by decide +kernel) (consbad n157 (nilbad 4))

def w403 : List Mask := [15,248,3840,4369,8738,62532]
theorem n403 : impossible 5 w403.toFinset :=
  closeState (known := [w76.toFinset, w77.toFinset, w87.toFinset]) w403 (by decide) (by decide +kernel) (consbad n76 (consbad n77 (consbad n87 (nilbad 4))))

def w404 : List Mask := [15,248,3840,4369,17476,61986]
theorem n404 : impossible 5 w404.toFinset :=
  closeState (known := [w78.toFinset, w79.toFinset, w88.toFinset]) w404 (by decide) (by decide +kernel) (consbad n78 (consbad n79 (consbad n88 (nilbad 4))))

def w405 : List Mask := [15,248,4369,8738,17476,65280]
theorem n405 : impossible 5 w405.toFinset :=
  closeState (known := [w76.toFinset, w78.toFinset, w177.toFinset, w197.toFinset]) w405 (by decide) (by decide +kernel) (consbad n76 (consbad n78 (consbad n177 (consbad n197 (nilbad 4)))))

def w406 : List Mask := [15,248,4369,8738,20292,61440]
theorem n406 : impossible 5 w406.toFinset :=
  closeState (known := [w76.toFinset, w79.toFinset, w178.toFinset]) w406 (by decide) (by decide +kernel) (consbad n76 (consbad n79 (consbad n178 (nilbad 4))))

def w407 : List Mask := [15,248,4369,12066,17476,61440]
theorem n407 : impossible 5 w407.toFinset :=
  closeState (known := [w77.toFinset, w78.toFinset, w179.toFinset]) w407 (by decide) (by decide +kernel) (consbad n77 (consbad n78 (consbad n179 (nilbad 4))))

def w408 : List Mask := [15,256,4593,8738,34952,62532]
theorem n408 : impossible 5 w408.toFinset :=
  closeState (known := [w106.toFinset, w121.toFinset, w198.toFinset]) w408 (by decide) (by decide +kernel) (consbad n106 (consbad n121 (consbad n198 (nilbad 4))))

def w409 : List Mask := [15,256,4593,17476,34952,61986]
theorem n409 : impossible 5 w409.toFinset :=
  closeState (known := [w142.toFinset, w155.toFinset, w199.toFinset]) w409 (by decide) (by decide +kernel) (consbad n142 (consbad n155 (consbad n199 (nilbad 4))))

def w410 : List Mask := [15,320,4593,8738,34952,61440]
theorem n410 : impossible 5 w410.toFinset :=
  closeState (known := [w80.toFinset, w105.toFinset, w122.toFinset, w200.toFinset]) w410 (by decide) (by decide +kernel) (consbad n80 (consbad n105 (consbad n122 (consbad n200 (nilbad 4)))))

def w411 : List Mask := [15,3840,4160,4593,8738,34952]
theorem n411 : impossible 5 w411.toFinset :=
  closeState (known := [w82.toFinset, w92.toFinset, w100.toFinset, w201.toFinset]) w411 (by decide) (by decide +kernel) (consbad n82 (consbad n92 (consbad n100 (consbad n201 (nilbad 4)))))

def w412 : List Mask := [15,3840,4369,8738,21572,35064]
theorem n412 : impossible 5 w412.toFinset :=
  closeState (known := [w202.toFinset]) w412 (by decide) (by decide +kernel) (consbad n202 (nilbad 4))

def w413 : List Mask := [15,3840,4369,8802,35064,61440]
theorem n413 : impossible 5 w413.toFinset :=
  closeState (known := [w96.toFinset]) w413 (by decide) (by decide +kernel) (consbad n96 (nilbad 4))

def w414 : List Mask := [15,3840,4369,12834,17476,35064]
theorem n414 : impossible 5 w414.toFinset :=
  closeState (known := [w203.toFinset]) w414 (by decide) (by decide +kernel) (consbad n203 (nilbad 4))

def w415 : List Mask := [15,3840,4369,26214,35064,61986]
theorem n415 : impossible 5 w415.toFinset :=
  closeState (known := [w98.toFinset]) w415 (by decide) (by decide +kernel) (consbad n98 (nilbad 4))

def w416 : List Mask := [15,3840,4593,8738,17476,61448]
theorem n416 : impossible 5 w416.toFinset :=
  closeState (known := [w83.toFinset, w101.toFinset, w102.toFinset, w123.toFinset]) w416 (by decide) (by decide +kernel) (consbad n83 (consbad n101 (consbad n102 (consbad n123 (nilbad 4)))))

def w417 : List Mask := [15,3840,4593,8738,21572,34952]
theorem n417 : impossible 5 w417.toFinset :=
  closeState (known := [w104.toFinset, w124.toFinset, w204.toFinset]) w417 (by decide) (by decide +kernel) (consbad n104 (consbad n124 (consbad n204 (nilbad 4))))

def w418 : List Mask := [15,3840,4593,8738,34952,61504]
theorem n418 : impossible 5 w418.toFinset :=
  closeState (known := [w84.toFinset, w107.toFinset, w125.toFinset]) w418 (by decide) (by decide +kernel) (consbad n84 (consbad n107 (consbad n125 (nilbad 4))))

def w419 : List Mask := [15,3840,4593,8738,34952,62543]
theorem n419 : impossible 5 w419.toFinset :=
  closeState (known := [w109.toFinset, w126.toFinset, w209.toFinset]) w419 (by decide) (by decide +kernel) (consbad n109 (consbad n126 (consbad n209 (nilbad 4))))

def w420 : List Mask := [15,3840,4593,8738,34952,63078]
theorem n420 : impossible 5 w420.toFinset :=
  closeState (known := [w85.toFinset, w110.toFinset, w127.toFinset]) w420 (by decide) (by decide +kernel) (consbad n85 (consbad n110 (consbad n127 (nilbad 4))))

def w421 : List Mask := [15,3840,4593,8738,34952,65348]
theorem n421 : impossible 5 w421.toFinset :=
  closeState (known := [w112.toFinset, w128.toFinset]) w421 (by decide) (by decide +kernel) (consbad n112 (consbad n128 (nilbad 4)))

def w422 : List Mask := [15,3840,4593,8738,35064,62532]
theorem n422 : impossible 5 w422.toFinset :=
  closeState (known := [w111.toFinset, w130.toFinset]) w422 (by decide) (by decide +kernel) (consbad n111 (consbad n130 (nilbad 4)))

def w423 : List Mask := [15,3840,4593,8738,36744,62532]
theorem n423 : impossible 5 w423.toFinset :=
  closeState (known := [w112.toFinset, w131.toFinset]) w423 (by decide) (by decide +kernel) (consbad n112 (consbad n131 (nilbad 4)))

def w424 : List Mask := [15,3840,4593,8738,39321,62532]
theorem n424 : impossible 5 w424.toFinset :=
  closeState (known := [w113.toFinset, w132.toFinset]) w424 (by decide) (by decide +kernel) (consbad n113 (consbad n132 (nilbad 4)))

def w425 : List Mask := [15,3840,4593,8738,39417,62532]
theorem n425 : impossible 5 w425.toFinset :=
  closeState (known := [w114.toFinset, w133.toFinset]) w425 (by decide) (by decide +kernel) (consbad n114 (consbad n133 (nilbad 4)))

def w426 : List Mask := [15,3840,4593,8738,43690,62532]
theorem n426 : impossible 5 w426.toFinset :=
  closeState (known := [w85.toFinset, w115.toFinset, w134.toFinset]) w426 (by decide) (by decide +kernel) (consbad n85 (consbad n115 (consbad n134 (nilbad 4))))

def w427 : List Mask := [15,3840,4593,8738,62532,63624]
theorem n427 : impossible 5 w427.toFinset :=
  closeState (known := [w116.toFinset, w136.toFinset]) w427 (by decide) (by decide +kernel) (consbad n116 (consbad n136 (nilbad 4)))

def w428 : List Mask := [15,3840,4593,8746,17476,61440]
theorem n428 : impossible 5 w428.toFinset :=
  closeState (known := [w81.toFinset, w83.toFinset, w118.toFinset, w119.toFinset, w137.toFinset, w205.toFinset]) w428 (by decide) (by decide +kernel) (consbad n81 (consbad n83 (consbad n118 (consbad n119 (consbad n137 (consbad n205 (nilbad 4)))))))

def w429 : List Mask := [15,3840,4593,8802,34952,61440]
theorem n429 : impossible 5 w429.toFinset :=
  closeState (known := [w84.toFinset, w120.toFinset, w138.toFinset]) w429 (by decide) (by decide +kernel) (consbad n84 (consbad n120 (consbad n138 (nilbad 4))))

def w430 : List Mask := [15,3840,4593,12066,34952,62532]
theorem n430 : impossible 5 w430.toFinset :=
  closeState (known := [w128.toFinset, w131.toFinset]) w430 (by decide) (by decide +kernel) (consbad n128 (consbad n131 (nilbad 4)))

def w431 : List Mask := [15,3840,4593,12834,17476,34952]
theorem n431 : impossible 5 w431.toFinset :=
  closeState (known := [w139.toFinset, w141.toFinset, w206.toFinset]) w431 (by decide) (by decide +kernel) (consbad n139 (consbad n141 (consbad n206 (nilbad 4))))

def w432 : List Mask := [15,3840,4593,17476,34952,65314]
theorem n432 : impossible 5 w432.toFinset :=
  closeState (known := [w145.toFinset, w156.toFinset]) w432 (by decide) (by decide +kernel) (consbad n145 (consbad n156 (nilbad 4)))

def w433 : List Mask := [15,3840,4593,17476,35064,61986]
theorem n433 : impossible 5 w433.toFinset :=
  closeState (known := [w144.toFinset, w157.toFinset]) w433 (by decide) (by decide +kernel) (consbad n144 (consbad n157 (nilbad 4)))

def w434 : List Mask := [15,3840,4593,17476,36744,61986]
theorem n434 : impossible 5 w434.toFinset :=
  closeState (known := [w145.toFinset, w158.toFinset]) w434 (by decide) (by decide +kernel) (consbad n145 (consbad n158 (nilbad 4)))

def w435 : List Mask := [15,3840,4593,17476,39321,61986]
theorem n435 : impossible 5 w435.toFinset :=
  closeState (known := [w146.toFinset, w159.toFinset]) w435 (by decide) (by decide +kernel) (consbad n146 (consbad n159 (nilbad 4)))

def w436 : List Mask := [15,3840,4593,17476,39417,61986]
theorem n436 : impossible 5 w436.toFinset :=
  closeState (known := [w147.toFinset, w160.toFinset]) w436 (by decide) (by decide +kernel) (consbad n147 (consbad n160 (nilbad 4)))

def w437 : List Mask := [15,3840,4593,17476,43690,61986]
theorem n437 : impossible 5 w437.toFinset :=
  closeState (known := [w85.toFinset, w148.toFinset, w161.toFinset, w207.toFinset]) w437 (by decide) (by decide +kernel) (consbad n85 (consbad n148 (consbad n161 (consbad n207 (nilbad 4)))))

def w438 : List Mask := [15,3840,4593,17476,61986,63624]
theorem n438 : impossible 5 w438.toFinset :=
  closeState (known := [w150.toFinset, w162.toFinset]) w438 (by decide) (by decide +kernel) (consbad n150 (consbad n162 (nilbad 4)))

def w439 : List Mask := [15,3840,4593,17476,61986,64170]
theorem n439 : impossible 5 w439.toFinset :=
  closeState (known := [w86.toFinset, w151.toFinset, w163.toFinset]) w439 (by decide) (by decide +kernel) (consbad n86 (consbad n151 (consbad n163 (nilbad 4))))

def w440 : List Mask := [15,3840,4593,17487,34952,61986]
theorem n440 : impossible 5 w440.toFinset :=
  closeState (known := [w154.toFinset, w164.toFinset, w210.toFinset]) w440 (by decide) (by decide +kernel) (consbad n154 (consbad n164 (consbad n210 (nilbad 4))))

def w441 : List Mask := [15,3840,4593,20292,34952,61986]
theorem n441 : impossible 5 w441.toFinset :=
  closeState (known := [w156.toFinset, w158.toFinset]) w441 (by decide) (by decide +kernel) (consbad n156 (consbad n158 (nilbad 4)))

def w442 : List Mask := [15,3840,4593,26214,34952,61986]
theorem n442 : impossible 5 w442.toFinset :=
  closeState (known := [w165.toFinset, w167.toFinset]) w442 (by decide) (by decide +kernel) (consbad n165 (consbad n167 (nilbad 4)))

def w443 : List Mask := [15,3840,4593,26214,43690,61440]
theorem n443 : impossible 5 w443.toFinset :=
  closeState (known := [w85.toFinset, w166.toFinset, w169.toFinset]) w443 (by decide) (by decide +kernel) (consbad n85 (consbad n166 (consbad n169 (nilbad 4))))

def w444 : List Mask := [15,3840,4593,34952,61986,62532]
theorem n444 : impossible 5 w444.toFinset :=
  closeState (known := [w171.toFinset, w173.toFinset]) w444 (by decide) (by decide +kernel) (consbad n171 (consbad n173 (nilbad 4)))

def w445 : List Mask := [15,3840,4593,34952,61986,63078]
theorem n445 : impossible 5 w445.toFinset :=
  closeState (known := [w86.toFinset, w172.toFinset, w174.toFinset]) w445 (by decide) (by decide +kernel) (consbad n86 (consbad n172 (consbad n174 (nilbad 4))))

def w446 : List Mask := [15,3840,4601,8738,17476,61440]
theorem n446 : impossible 5 w446.toFinset :=
  closeState (known := [w87.toFinset, w88.toFinset, w177.toFinset, w178.toFinset, w179.toFinset, w208.toFinset]) w446 (by decide) (by decide +kernel) (consbad n87 (consbad n88 (consbad n177 (consbad n178 (consbad n179 (consbad n208 (nilbad 4)))))))

def w447 : List Mask := [15,3848,4593,8738,17476,61440]
theorem n447 : impossible 5 w447.toFinset :=
  closeState (known := [w89.toFinset, w90.toFinset, w101.toFinset, w137.toFinset]) w447 (by decide) (by decide +kernel) (consbad n89 (consbad n90 (consbad n101 (consbad n137 (nilbad 4)))))

def w448 : List Mask := [15,3855,4593,8738,34952,62532]
theorem n448 : impossible 5 w448.toFinset :=
  closeState (known := [w109.toFinset, w209.toFinset]) w448 (by decide) (by decide +kernel) (consbad n109 (consbad n209 (nilbad 4)))

def w449 : List Mask := [15,3855,4593,17476,34952,61986]
theorem n449 : impossible 5 w449.toFinset :=
  closeState (known := [w164.toFinset, w210.toFinset]) w449 (by decide) (by decide +kernel) (consbad n164 (consbad n210 (nilbad 4)))

def w450 : List Mask := [15,3904,4593,8738,34952,61440]
theorem n450 : impossible 5 w450.toFinset :=
  closeState (known := [w91.toFinset, w107.toFinset, w138.toFinset]) w450 (by decide) (by decide +kernel) (consbad n91 (consbad n107 (consbad n138 (nilbad 4))))

def w451 : List Mask := [15,4096,4593,8738,20292,34952]
theorem n451 : impossible 5 w451.toFinset :=
  closeState (known := [w104.toFinset, w139.toFinset, w211.toFinset]) w451 (by decide) (by decide +kernel) (consbad n104 (consbad n139 (consbad n211 (nilbad 4))))

def w452 : List Mask := [15,4096,4593,12066,17476,34952]
theorem n452 : impossible 5 w452.toFinset :=
  closeState (known := [w124.toFinset, w141.toFinset, w212.toFinset]) w452 (by decide) (by decide +kernel) (consbad n124 (consbad n141 (consbad n212 (nilbad 4))))

def w453 : List Mask := [15,4352,4369,8738,17476,35064]
theorem n453 : impossible 5 w453.toFinset :=
  closeState (known := [w93.toFinset, w95.toFinset, w97.toFinset, w213.toFinset, w215.toFinset]) w453 (by decide) (by decide +kernel) (consbad n93 (consbad n95 (consbad n97 (consbad n213 (consbad n215 (nilbad 4))))))

def w454 : List Mask := [15,4352,4593,8738,17476,34952]
theorem n454 : impossible 5 w454.toFinset :=
  closeState (known := [w93.toFinset, w103.toFinset, w140.toFinset, w214.toFinset, w216.toFinset]) w454 (by decide) (by decide +kernel) (consbad n93 (consbad n103 (consbad n140 (consbad n214 (consbad n216 (nilbad 4))))))

def w455 : List Mask := [15,4369,4593,8738,17476,65416]
theorem n455 : impossible 5 w455.toFinset :=
  closeState (known := []) w455 (by decide) (by decide +kernel) (nilbad 4)

def w456 : List Mask := [15,4369,4593,8738,20292,63624]
theorem n456 : impossible 5 w456.toFinset :=
  closeState (known := []) w456 (by decide) (by decide +kernel) (nilbad 4)

def w457 : List Mask := [15,4369,4593,8738,34952,65348]
theorem n457 : impossible 5 w457.toFinset :=
  closeState (known := [w113.toFinset]) w457 (by decide) (by decide +kernel) (consbad n113 (nilbad 4))

def w458 : List Mask := [15,4369,4593,8738,36744,62532]
theorem n458 : impossible 5 w458.toFinset :=
  closeState (known := []) w458 (by decide) (by decide +kernel) (nilbad 4)

def w459 : List Mask := [15,4369,4593,12066,17476,63624]
theorem n459 : impossible 5 w459.toFinset :=
  closeState (known := []) w459 (by decide) (by decide +kernel) (nilbad 4)

def w460 : List Mask := [15,4369,4593,12066,34952,62532]
theorem n460 : impossible 5 w460.toFinset :=
  closeState (known := [w132.toFinset]) w460 (by decide) (by decide +kernel) (consbad n132 (nilbad 4))

def w461 : List Mask := [15,4369,4593,17476,34952,65314]
theorem n461 : impossible 5 w461.toFinset :=
  closeState (known := [w146.toFinset]) w461 (by decide) (by decide +kernel) (consbad n146 (nilbad 4))

def w462 : List Mask := [15,4369,4593,17476,36744,61986]
theorem n462 : impossible 5 w462.toFinset :=
  closeState (known := []) w462 (by decide) (by decide +kernel) (nilbad 4)

def w463 : List Mask := [15,4369,4593,20292,34952,61986]
theorem n463 : impossible 5 w463.toFinset :=
  closeState (known := [w159.toFinset]) w463 (by decide) (by decide +kernel) (consbad n159 (nilbad 4))

def w464 : List Mask := [15,4369,7936,8738,17476,35064]
theorem n464 : impossible 5 w464.toFinset :=
  closeState (known := [w217.toFinset]) w464 (by decide) (by decide +kernel) (consbad n217 (nilbad 4))

def w465 : List Mask := [15,4369,8738,17476,35064,61696]
theorem n465 : impossible 5 w465.toFinset :=
  closeState (known := [w218.toFinset]) w465 (by decide) (by decide +kernel) (consbad n218 (nilbad 4))

def w466 : List Mask := [15,4369,8738,17476,35064,65295]
theorem n466 : impossible 5 w466.toFinset :=
  closeState (known := [w94.toFinset, w219.toFinset]) w466 (by decide) (by decide +kernel) (consbad n94 (consbad n219 (nilbad 4)))

def w467 : List Mask := [15,4369,8738,17476,35064,65314]
theorem n467 : impossible 5 w467.toFinset :=
  closeState (known := [w98.toFinset, w220.toFinset]) w467 (by decide) (by decide +kernel) (consbad n98 (consbad n220 (nilbad 4)))

def w468 : List Mask := [15,4369,8738,17476,35064,65348]
theorem n468 : impossible 5 w468.toFinset :=
  closeState (known := [w221.toFinset]) w468 (by decide) (by decide +kernel) (consbad n221 (nilbad 4))

def w469 : List Mask := [15,4369,8738,17476,35064,65416]
theorem n469 : impossible 5 w469.toFinset :=
  closeState (known := [w223.toFinset]) w469 (by decide) (by decide +kernel) (consbad n223 (nilbad 4))

def w470 : List Mask := [15,4369,8738,17476,39417,65280]
theorem n470 : impossible 5 w470.toFinset :=
  closeState (known := [w93.toFinset, w224.toFinset]) w470 (by decide) (by decide +kernel) (consbad n93 (consbad n224 (nilbad 4)))

def w471 : List Mask := [15,4369,8738,17487,35064,65280]
theorem n471 : impossible 5 w471.toFinset :=
  closeState (known := [w219.toFinset]) w471 (by decide) (by decide +kernel) (consbad n219 (nilbad 4))

def w472 : List Mask := [15,4369,8738,17732,35064,61440]
theorem n472 : impossible 5 w472.toFinset :=
  closeState (known := [w225.toFinset]) w472 (by decide) (by decide +kernel) (consbad n225 (nilbad 4))

def w473 : List Mask := [15,4369,8738,20292,35064,62532]
theorem n473 : impossible 5 w473.toFinset :=
  closeState (known := []) w473 (by decide) (by decide +kernel) (nilbad 4)

def w474 : List Mask := [15,4369,8738,26214,35064,65280]
theorem n474 : impossible 5 w474.toFinset :=
  closeState (known := [w98.toFinset]) w474 (by decide) (by decide +kernel) (consbad n98 (nilbad 4))

def w475 : List Mask := [15,4369,8994,17476,35064,61440]
theorem n475 : impossible 5 w475.toFinset :=
  closeState (known := [w227.toFinset]) w475 (by decide) (by decide +kernel) (consbad n227 (nilbad 4))

def w476 : List Mask := [15,4369,12066,17476,35064,61986]
theorem n476 : impossible 5 w476.toFinset :=
  closeState (known := [w228.toFinset]) w476 (by decide) (by decide +kernel) (consbad n228 (nilbad 4))

def w477 : List Mask := [15,4369,12066,26214,35064,61440]
theorem n477 : impossible 5 w477.toFinset :=
  closeState (known := [w98.toFinset]) w477 (by decide) (by decide +kernel) (consbad n98 (nilbad 4))

def w478 : List Mask := [15,4593,7936,8738,17476,34952]
theorem n478 : impossible 5 w478.toFinset :=
  closeState (known := [w104.toFinset, w141.toFinset, w229.toFinset]) w478 (by decide) (by decide +kernel) (consbad n104 (consbad n141 (consbad n229 (nilbad 4))))

def w479 : List Mask := [15,4593,8738,12066,34952,62532]
theorem n479 : impossible 5 w479.toFinset :=
  closeState (known := [w110.toFinset, w127.toFinset, w134.toFinset]) w479 (by decide) (by decide +kernel) (consbad n110 (consbad n127 (consbad n134 (nilbad 4))))

def w480 : List Mask := [15,4593,8738,17476,34952,61696]
theorem n480 : impossible 5 w480.toFinset :=
  closeState (known := [w106.toFinset, w142.toFinset, w230.toFinset]) w480 (by decide) (by decide +kernel) (consbad n106 (consbad n142 (consbad n230 (nilbad 4))))

def w481 : List Mask := [15,4593,8738,17476,34952,65295]
theorem n481 : impossible 5 w481.toFinset :=
  closeState (known := [w109.toFinset, w231.toFinset]) w481 (by decide) (by decide +kernel) (consbad n109 (consbad n231 (nilbad 4)))

def w482 : List Mask := [15,4593,8738,17476,34952,65314]
theorem n482 : impossible 5 w482.toFinset :=
  closeState (known := [w110.toFinset, w148.toFinset, w165.toFinset, w232.toFinset]) w482 (by decide) (by decide +kernel) (consbad n110 (consbad n148 (consbad n165 (consbad n232 (nilbad 4)))))

def w483 : List Mask := [15,4593,8738,17476,34952,65348]
theorem n483 : impossible 5 w483.toFinset :=
  closeState (known := [w233.toFinset]) w483 (by decide) (by decide +kernel) (consbad n233 (nilbad 4))

def w484 : List Mask := [15,4593,8738,17476,35064,65280]
theorem n484 : impossible 5 w484.toFinset :=
  closeState (known := [w111.toFinset, w144.toFinset, w235.toFinset]) w484 (by decide) (by decide +kernel) (consbad n111 (consbad n144 (consbad n235 (nilbad 4))))

def w485 : List Mask := [15,4593,8738,17476,36744,65280]
theorem n485 : impossible 5 w485.toFinset :=
  closeState (known := [w112.toFinset, w145.toFinset]) w485 (by decide) (by decide +kernel) (consbad n112 (consbad n145 (nilbad 4)))

def w486 : List Mask := [15,4593,8738,17476,39321,65280]
theorem n486 : impossible 5 w486.toFinset :=
  closeState (known := [w113.toFinset, w146.toFinset, w236.toFinset]) w486 (by decide) (by decide +kernel) (consbad n113 (consbad n146 (consbad n236 (nilbad 4))))

def w487 : List Mask := [15,4593,8738,17476,39417,65280]
theorem n487 : impossible 5 w487.toFinset :=
  closeState (known := [w93.toFinset, w114.toFinset, w147.toFinset, w237.toFinset]) w487 (by decide) (by decide +kernel) (consbad n93 (consbad n114 (consbad n147 (consbad n237 (nilbad 4)))))

def w488 : List Mask := [15,4593,8738,17476,43690,65280]
theorem n488 : impossible 5 w488.toFinset :=
  closeState (known := [w115.toFinset, w148.toFinset, w166.toFinset, w238.toFinset]) w488 (by decide) (by decide +kernel) (consbad n115 (consbad n148 (consbad n166 (consbad n238 (nilbad 4)))))

def w489 : List Mask := [15,4593,8738,17476,63624,65280]
theorem n489 : impossible 5 w489.toFinset :=
  closeState (known := [w116.toFinset, w150.toFinset]) w489 (by decide) (by decide +kernel) (consbad n116 (consbad n150 (nilbad 4)))

def w490 : List Mask := [15,4593,8738,17476,65280,65416]
theorem n490 : impossible 5 w490.toFinset :=
  closeState (known := [w117.toFinset, w152.toFinset]) w490 (by decide) (by decide +kernel) (consbad n117 (consbad n152 (nilbad 4)))

def w491 : List Mask := [15,4593,8738,17487,34952,65280]
theorem n491 : impossible 5 w491.toFinset :=
  closeState (known := [w44.toFinset, w109.toFinset, w154.toFinset, w231.toFinset]) w491 (by decide) (by decide +kernel) (consbad n44 (consbad n109 (consbad n154 (consbad n231 (nilbad 4)))))

def w492 : List Mask := [15,4593,8738,17732,34952,61440]
theorem n492 : impossible 5 w492.toFinset :=
  closeState (known := [w106.toFinset, w155.toFinset, w239.toFinset]) w492 (by decide) (by decide +kernel) (consbad n106 (consbad n155 (consbad n239 (nilbad 4))))

def w493 : List Mask := [15,4593,8738,20292,34952,61455]
theorem n493 : impossible 5 w493.toFinset :=
  closeState (known := [w109.toFinset, w240.toFinset]) w493 (by decide) (by decide +kernel) (consbad n109 (consbad n240 (nilbad 4)))

def w494 : List Mask := [15,4593,8738,20292,34952,61986]
theorem n494 : impossible 5 w494.toFinset :=
  closeState (known := [w110.toFinset, w161.toFinset, w167.toFinset]) w494 (by decide) (by decide +kernel) (consbad n110 (consbad n161 (consbad n167 (nilbad 4))))

def w495 : List Mask := [15,4593,8738,20292,34952,62532]
theorem n495 : impossible 5 w495.toFinset :=
  closeState (known := [w108.toFinset]) w495 (by decide) (by decide +kernel) (consbad n108 (nilbad 4))

def w496 : List Mask := [15,4593,8738,20292,34952,65280]
theorem n496 : impossible 5 w496.toFinset :=
  closeState (known := [w108.toFinset, w156.toFinset]) w496 (by decide) (by decide +kernel) (consbad n108 (consbad n156 (nilbad 4)))

def w497 : List Mask := [15,4593,8738,20292,34952,65348]
theorem n497 : impossible 5 w497.toFinset :=
  closeState (known := []) w497 (by decide) (by decide +kernel) (nilbad 4)

def w498 : List Mask := [15,4593,8738,20292,35064,61440]
theorem n498 : impossible 5 w498.toFinset :=
  closeState (known := [w111.toFinset, w157.toFinset]) w498 (by decide) (by decide +kernel) (consbad n111 (consbad n157 (nilbad 4)))

def w499 : List Mask := [15,4593,8738,20292,36744,61440]
theorem n499 : impossible 5 w499.toFinset :=
  closeState (known := [w112.toFinset, w158.toFinset]) w499 (by decide) (by decide +kernel) (consbad n112 (consbad n158 (nilbad 4)))

def w500 : List Mask := [15,4593,8738,20292,39321,61440]
theorem n500 : impossible 5 w500.toFinset :=
  closeState (known := [w113.toFinset, w159.toFinset]) w500 (by decide) (by decide +kernel) (consbad n113 (consbad n159 (nilbad 4)))

def w501 : List Mask := [15,4593,8738,20292,39417,61440]
theorem n501 : impossible 5 w501.toFinset :=
  closeState (known := [w114.toFinset, w160.toFinset]) w501 (by decide) (by decide +kernel) (consbad n114 (consbad n160 (nilbad 4)))

def w502 : List Mask := [15,4593,8738,20292,43690,61440]
theorem n502 : impossible 5 w502.toFinset :=
  closeState (known := [w115.toFinset, w161.toFinset, w169.toFinset]) w502 (by decide) (by decide +kernel) (consbad n115 (consbad n161 (consbad n169 (nilbad 4))))

def w503 : List Mask := [15,4593,8738,20292,61440,63624]
theorem n503 : impossible 5 w503.toFinset :=
  closeState (known := [w116.toFinset, w162.toFinset]) w503 (by decide) (by decide +kernel) (consbad n116 (consbad n162 (nilbad 4)))

def w504 : List Mask := [15,4593,8738,20303,34952,61440]
theorem n504 : impossible 5 w504.toFinset :=
  closeState (known := [w109.toFinset, w164.toFinset, w240.toFinset]) w504 (by decide) (by decide +kernel) (consbad n109 (consbad n164 (consbad n240 (nilbad 4))))

def w505 : List Mask := [15,4593,8738,26214,34952,65280]
theorem n505 : impossible 5 w505.toFinset :=
  closeState (known := [w110.toFinset, w165.toFinset, w166.toFinset]) w505 (by decide) (by decide +kernel) (consbad n110 (consbad n165 (consbad n166 (nilbad 4))))

def w506 : List Mask := [15,4593,8738,28518,34952,61440]
theorem n506 : impossible 5 w506.toFinset :=
  closeState (known := [w110.toFinset, w167.toFinset, w169.toFinset]) w506 (by decide) (by decide +kernel) (consbad n110 (consbad n167 (consbad n169 (nilbad 4))))

def w507 : List Mask := [15,4593,8738,34952,61440,65348]
theorem n507 : impossible 5 w507.toFinset :=
  closeState (known := [w116.toFinset, w171.toFinset]) w507 (by decide) (by decide +kernel) (consbad n116 (consbad n171 (nilbad 4)))

def w508 : List Mask := [15,4593,8738,34952,62532,65280]
theorem n508 : impossible 5 w508.toFinset :=
  closeState (known := [w108.toFinset, w173.toFinset]) w508 (by decide) (by decide +kernel) (consbad n108 (consbad n173 (nilbad 4)))

def w509 : List Mask := [15,4593,8738,34952,62532,65348]
theorem n509 : impossible 5 w509.toFinset :=
  closeState (known := []) w509 (by decide) (by decide +kernel) (nilbad 4)

def w510 : List Mask := [15,4593,8738,34952,65280,65348]
theorem n510 : impossible 5 w510.toFinset :=
  closeState (known := [w117.toFinset, w175.toFinset]) w510 (by decide) (by decide +kernel) (consbad n117 (consbad n175 (nilbad 4)))

def w511 : List Mask := [15,4593,8738,34952,65348]
theorem n511 : impossible 5 w511.toFinset :=
  closeState (known := [w40.toFinset, w99.toFinset, w109.toFinset, w110.toFinset, w114.toFinset, w115.toFinset]) w511 (by decide) (by decide +kernel) (consbad n40 (consbad n99 (consbad n109 (consbad n110 (consbad n114 (consbad n115 (nilbad 4)))))))

def w512 : List Mask := [15,4593,8994,17476,34952,61440]
theorem n512 : impossible 5 w512.toFinset :=
  closeState (known := [w121.toFinset, w142.toFinset, w242.toFinset]) w512 (by decide) (by decide +kernel) (consbad n121 (consbad n142 (consbad n242 (nilbad 4))))

def w513 : List Mask := [15,4593,12066,17476,34952,61455]
theorem n513 : impossible 5 w513.toFinset :=
  closeState (known := [w126.toFinset, w243.toFinset]) w513 (by decide) (by decide +kernel) (consbad n126 (consbad n243 (nilbad 4)))

def w514 : List Mask := [15,4593,12066,17476,34952,61986]
theorem n514 : impossible 5 w514.toFinset :=
  closeState (known := [w127.toFinset, w143.toFinset, w167.toFinset, w244.toFinset]) w514 (by decide) (by decide +kernel) (consbad n127 (consbad n143 (consbad n167 (consbad n244 (nilbad 4)))))

def w515 : List Mask := [15,4593,12066,17476,34952,62532]
theorem n515 : impossible 5 w515.toFinset :=
  closeState (known := []) w515 (by decide) (by decide +kernel) (nilbad 4)

def w516 : List Mask := [15,4593,12066,17476,34952,65280]
theorem n516 : impossible 5 w516.toFinset :=
  closeState (known := [w128.toFinset, w143.toFinset]) w516 (by decide) (by decide +kernel) (consbad n128 (consbad n143 (nilbad 4)))

def w517 : List Mask := [15,4593,12066,17476,34952,65314]
theorem n517 : impossible 5 w517.toFinset :=
  closeState (known := [w129.toFinset, w149.toFinset, w168.toFinset]) w517 (by decide) (by decide +kernel) (consbad n129 (consbad n149 (consbad n168 (nilbad 4))))

def w518 : List Mask := [15,4593,12066,17476,35064,61440]
theorem n518 : impossible 5 w518.toFinset :=
  closeState (known := [w130.toFinset, w144.toFinset]) w518 (by decide) (by decide +kernel) (consbad n130 (consbad n144 (nilbad 4)))

def w519 : List Mask := [15,4593,12066,17476,36744,61440]
theorem n519 : impossible 5 w519.toFinset :=
  closeState (known := [w131.toFinset, w145.toFinset]) w519 (by decide) (by decide +kernel) (consbad n131 (consbad n145 (nilbad 4)))

def w520 : List Mask := [15,4593,12066,17476,39321,61440]
theorem n520 : impossible 5 w520.toFinset :=
  closeState (known := [w132.toFinset, w146.toFinset]) w520 (by decide) (by decide +kernel) (consbad n132 (consbad n146 (nilbad 4)))

def w521 : List Mask := [15,4593,12066,17476,39417,61440]
theorem n521 : impossible 5 w521.toFinset :=
  closeState (known := [w133.toFinset, w147.toFinset]) w521 (by decide) (by decide +kernel) (consbad n133 (consbad n147 (nilbad 4)))

def w522 : List Mask := [15,4593,12066,17476,43690,61440]
theorem n522 : impossible 5 w522.toFinset :=
  closeState (known := [w134.toFinset, w148.toFinset, w169.toFinset, w245.toFinset]) w522 (by decide) (by decide +kernel) (consbad n134 (consbad n148 (consbad n169 (consbad n245 (nilbad 4)))))

def w523 : List Mask := [15,4593,12066,17476,44970,61440]
theorem n523 : impossible 5 w523.toFinset :=
  closeState (known := [w135.toFinset, w149.toFinset, w170.toFinset]) w523 (by decide) (by decide +kernel) (consbad n135 (consbad n149 (consbad n170 (nilbad 4))))

def w524 : List Mask := [15,4593,12066,17476,61440,63624]
theorem n524 : impossible 5 w524.toFinset :=
  closeState (known := [w136.toFinset, w150.toFinset]) w524 (by decide) (by decide +kernel) (consbad n136 (consbad n150 (nilbad 4)))

def w525 : List Mask := [15,4593,12066,17487,34952,61440]
theorem n525 : impossible 5 w525.toFinset :=
  closeState (known := [w126.toFinset, w154.toFinset, w243.toFinset]) w525 (by decide) (by decide +kernel) (consbad n126 (consbad n154 (consbad n243 (nilbad 4))))

def w526 : List Mask := [15,4593,12066,20292,34952,61440]
theorem n526 : impossible 5 w526.toFinset :=
  closeState (known := [w128.toFinset, w156.toFinset]) w526 (by decide) (by decide +kernel) (consbad n128 (consbad n156 (nilbad 4)))

def w527 : List Mask := [15,4593,12066,26214,34952,61440]
theorem n527 : impossible 5 w527.toFinset :=
  closeState (known := [w127.toFinset, w165.toFinset]) w527 (by decide) (by decide +kernel) (consbad n127 (consbad n165 (nilbad 4)))

def w528 : List Mask := [15,4593,12066,28518,34952,61440]
theorem n528 : impossible 5 w528.toFinset :=
  closeState (known := [w129.toFinset, w168.toFinset, w170.toFinset]) w528 (by decide) (by decide +kernel) (consbad n129 (consbad n168 (consbad n170 (nilbad 4))))

def w529 : List Mask := [15,4593,12066,34952,61440,62532]
theorem n529 : impossible 5 w529.toFinset :=
  closeState (known := [w136.toFinset, w173.toFinset]) w529 (by decide) (by decide +kernel) (consbad n136 (consbad n173 (nilbad 4)))

def w530 : List Mask := [15,4593,12066,34952,62532]
theorem n530 : impossible 5 w530.toFinset :=
  closeState (known := [w41.toFinset, w92.toFinset, w126.toFinset, w129.toFinset, w133.toFinset, w135.toFinset]) w530 (by decide) (by decide +kernel) (consbad n41 (consbad n92 (consbad n126 (consbad n129 (consbad n133 (consbad n135 (nilbad 4)))))))

def w531 : List Mask := [15,4593,17476,20292,34952,61986]
theorem n531 : impossible 5 w531.toFinset :=
  closeState (known := []) w531 (by decide) (by decide +kernel) (nilbad 4)

def w532 : List Mask := [15,4593,17476,34952,61440,65314]
theorem n532 : impossible 5 w532.toFinset :=
  closeState (known := [w150.toFinset, w173.toFinset]) w532 (by decide) (by decide +kernel) (consbad n150 (consbad n173 (nilbad 4)))

def w533 : List Mask := [15,4593,17476,34952,61986,65280]
theorem n533 : impossible 5 w533.toFinset :=
  closeState (known := [w143.toFinset, w171.toFinset]) w533 (by decide) (by decide +kernel) (consbad n143 (consbad n171 (nilbad 4)))

def w534 : List Mask := [15,4593,17476,34952,61986,65314]
theorem n534 : impossible 5 w534.toFinset :=
  closeState (known := [w151.toFinset, w172.toFinset, w174.toFinset]) w534 (by decide) (by decide +kernel) (consbad n151 (consbad n172 (consbad n174 (nilbad 4))))

def w535 : List Mask := [15,4593,17476,34952,65280,65314]
theorem n535 : impossible 5 w535.toFinset :=
  closeState (known := [w152.toFinset, w175.toFinset]) w535 (by decide) (by decide +kernel) (consbad n152 (consbad n175 (nilbad 4)))

def w536 : List Mask := [15,4593,17476,34952,65314]
theorem n536 : impossible 5 w536.toFinset :=
  closeState (known := [w42.toFinset, w45.toFinset, w147.toFinset, w153.toFinset, w154.toFinset, w176.toFinset]) w536 (by decide) (by decide +kernel) (consbad n42 (consbad n45 (consbad n147 (consbad n153 (consbad n154 (consbad n176 (nilbad 4)))))))

def w537 : List Mask := [15,4593,20292,34952,61440,61986]
theorem n537 : impossible 5 w537.toFinset :=
  closeState (known := [w162.toFinset, w171.toFinset]) w537 (by decide) (by decide +kernel) (consbad n162 (consbad n171 (nilbad 4)))

def w538 : List Mask := [15,4593,20292,34952,61986]
theorem n538 : impossible 5 w538.toFinset :=
  closeState (known := [w43.toFinset, w80.toFinset, w160.toFinset, w163.toFinset, w164.toFinset, w172.toFinset]) w538 (by decide) (by decide +kernel) (consbad n43 (consbad n80 (consbad n160 (consbad n163 (consbad n164 (consbad n172 (nilbad 4)))))))

def w539 : List Mask := [79,240,3840,4369,8738,63624]
theorem n539 : impossible 5 w539.toFinset :=
  closeState (known := [w180.toFinset, w181.toFinset]) w539 (by decide) (by decide +kernel) (consbad n180 (consbad n181 (nilbad 4)))

def w540 : List Mask := [79,240,3840,4369,34952,61986]
theorem n540 : impossible 5 w540.toFinset :=
  closeState (known := [w182.toFinset, w183.toFinset, w184.toFinset]) w540 (by decide) (by decide +kernel) (consbad n182 (consbad n183 (consbad n184 (nilbad 4))))

def w541 : List Mask := [79,240,4369,8738,34952,65280]
theorem n541 : impossible 5 w541.toFinset :=
  closeState (known := [w180.toFinset, w182.toFinset, w185.toFinset, w186.toFinset]) w541 (by decide) (by decide +kernel) (consbad n180 (consbad n182 (consbad n185 (consbad n186 (nilbad 4)))))

def w542 : List Mask := [79,240,4369,8738,36744,61440]
theorem n542 : impossible 5 w542.toFinset :=
  closeState (known := [w180.toFinset, w183.toFinset]) w542 (by decide) (by decide +kernel) (consbad n180 (consbad n183 (nilbad 4)))

def w543 : List Mask := [79,240,4369,12066,34952,61440]
theorem n543 : impossible 5 w543.toFinset :=
  closeState (known := [w181.toFinset, w182.toFinset, w187.toFinset]) w543 (by decide) (by decide +kernel) (consbad n181 (consbad n182 (consbad n187 (nilbad 4))))

def w544 : List Mask := [79,3840,4369,8738,35064,61440]
theorem n544 : impossible 5 w544.toFinset :=
  closeState (known := [w185.toFinset]) w544 (by decide) (by decide +kernel) (consbad n185 (nilbad 4))

def w545 : List Mask := [79,3840,4593,8738,34952,61440]
theorem n545 : impossible 5 w545.toFinset :=
  closeState (known := [w184.toFinset, w186.toFinset, w187.toFinset]) w545 (by decide) (by decide +kernel) (consbad n184 (consbad n186 (consbad n187 (nilbad 4))))

def w546 : List Mask := [240,271,4369,8738,17476,63624]
theorem n546 : impossible 5 w546.toFinset :=
  closeState (known := []) w546 (by decide) (by decide +kernel) (nilbad 4)

def w547 : List Mask := [240,271,4369,8738,34952,62532]
theorem n547 : impossible 5 w547.toFinset :=
  closeState (known := [w198.toFinset]) w547 (by decide) (by decide +kernel) (consbad n198 (nilbad 4))

def w548 : List Mask := [240,271,4369,17476,34952,61986]
theorem n548 : impossible 5 w548.toFinset :=
  closeState (known := [w199.toFinset]) w548 (by decide) (by decide +kernel) (consbad n199 (nilbad 4))

def w549 : List Mask := [240,3840,4369,8738,17487,39048]
theorem n549 : impossible 5 w549.toFinset :=
  closeState (known := []) w549 (by decide) (by decide +kernel) (nilbad 4)

def w550 : List Mask := [240,3840,4369,8738,21583,34952]
theorem n550 : impossible 5 w550.toFinset :=
  closeState (known := [w202.toFinset, w204.toFinset]) w550 (by decide) (by decide +kernel) (consbad n202 (consbad n204 (nilbad 4)))

def w551 : List Mask := [240,3840,4369,8746,17487,61440]
theorem n551 : impossible 5 w551.toFinset :=
  closeState (known := [w193.toFinset, w205.toFinset]) w551 (by decide) (by decide +kernel) (consbad n193 (consbad n205 (nilbad 4)))

def w552 : List Mask := [240,3840,4369,12834,17487,34952]
theorem n552 : impossible 5 w552.toFinset :=
  closeState (known := [w203.toFinset, w206.toFinset]) w552 (by decide) (by decide +kernel) (consbad n203 (consbad n206 (nilbad 4)))

def w553 : List Mask := [240,3840,4369,17487,43690,61986]
theorem n553 : impossible 5 w553.toFinset :=
  closeState (known := [w195.toFinset, w207.toFinset]) w553 (by decide) (by decide +kernel) (consbad n195 (consbad n207 (nilbad 4)))

def w554 : List Mask := [240,3840,4377,8738,17487,61440]
theorem n554 : impossible 5 w554.toFinset :=
  closeState (known := [w196.toFinset, w208.toFinset]) w554 (by decide) (by decide +kernel) (consbad n196 (consbad n208 (nilbad 4)))

def w555 : List Mask := [240,3855,4369,8738,17487,63624]
theorem n555 : impossible 5 w555.toFinset :=
  closeState (known := []) w555 (by decide) (by decide +kernel) (nilbad 4)

def w556 : List Mask := [240,3855,4369,8738,34952,62543]
theorem n556 : impossible 5 w556.toFinset :=
  closeState (known := [w209.toFinset]) w556 (by decide) (by decide +kernel) (consbad n209 (nilbad 4))

def w557 : List Mask := [240,3855,4369,17487,34952,61986]
theorem n557 : impossible 5 w557.toFinset :=
  closeState (known := [w210.toFinset]) w557 (by decide) (by decide +kernel) (consbad n210 (nilbad 4))

def w558 : List Mask := [240,4111,4369,8738,17476,36744]
theorem n558 : impossible 5 w558.toFinset :=
  closeState (known := []) w558 (by decide) (by decide +kernel) (nilbad 4)

def w559 : List Mask := [240,4111,4369,8738,20292,34952]
theorem n559 : impossible 5 w559.toFinset :=
  closeState (known := [w211.toFinset]) w559 (by decide) (by decide +kernel) (consbad n211 (nilbad 4))

def w560 : List Mask := [240,4111,4369,12066,17476,34952]
theorem n560 : impossible 5 w560.toFinset :=
  closeState (known := [w212.toFinset]) w560 (by decide) (by decide +kernel) (consbad n212 (nilbad 4))

def w561 : List Mask := [240,4352,4369,8738,17487,34952]
theorem n561 : impossible 5 w561.toFinset :=
  closeState (known := [w188.toFinset, w191.toFinset, w192.toFinset, w194.toFinset, w213.toFinset, w214.toFinset]) w561 (by decide) (by decide +kernel) (consbad n188 (consbad n191 (consbad n192 (consbad n194 (consbad n213 (consbad n214 (nilbad 4)))))))

def w562 : List Mask := [240,4367,4369,8738,17476,34952]
theorem n562 : impossible 5 w562.toFinset :=
  closeState (known := [w190.toFinset, w192.toFinset, w215.toFinset, w216.toFinset]) w562 (by decide) (by decide +kernel) (consbad n190 (consbad n192 (consbad n215 (consbad n216 (nilbad 4)))))

def w563 : List Mask := [240,4369,7936,8738,17487,34952]
theorem n563 : impossible 5 w563.toFinset :=
  closeState (known := [w217.toFinset, w229.toFinset]) w563 (by decide) (by decide +kernel) (consbad n217 (consbad n229 (nilbad 4)))

def w564 : List Mask := [240,4369,8738,17487,34952,61696]
theorem n564 : impossible 5 w564.toFinset :=
  closeState (known := [w218.toFinset, w230.toFinset]) w564 (by decide) (by decide +kernel) (consbad n218 (consbad n230 (nilbad 4)))

def w565 : List Mask := [240,4369,8738,17487,34952,65295]
theorem n565 : impossible 5 w565.toFinset :=
  closeState (known := [w189.toFinset, w219.toFinset, w231.toFinset]) w565 (by decide) (by decide +kernel) (consbad n189 (consbad n219 (consbad n231 (nilbad 4))))

def w566 : List Mask := [240,4369,8738,17487,34952,65314]
theorem n566 : impossible 5 w566.toFinset :=
  closeState (known := [w195.toFinset, w220.toFinset, w232.toFinset]) w566 (by decide) (by decide +kernel) (consbad n195 (consbad n220 (consbad n232 (nilbad 4))))

def w567 : List Mask := [240,4369,8738,17487,34952,65348]
theorem n567 : impossible 5 w567.toFinset :=
  closeState (known := [w221.toFinset, w233.toFinset]) w567 (by decide) (by decide +kernel) (consbad n221 (consbad n233 (nilbad 4)))

def w568 : List Mask := [240,4369,8738,17487,34952,65359]
theorem n568 : impossible 5 w568.toFinset :=
  closeState (known := [w189.toFinset, w222.toFinset, w234.toFinset]) w568 (by decide) (by decide +kernel) (consbad n189 (consbad n222 (consbad n234 (nilbad 4))))

def w569 : List Mask := [240,4369,8738,17487,34952,65416]
theorem n569 : impossible 5 w569.toFinset :=
  closeState (known := [w223.toFinset]) w569 (by decide) (by decide +kernel) (consbad n223 (nilbad 4))

def w570 : List Mask := [240,4369,8738,17487,35064,65280]
theorem n570 : impossible 5 w570.toFinset :=
  closeState (known := [w235.toFinset]) w570 (by decide) (by decide +kernel) (consbad n235 (nilbad 4))

def w571 : List Mask := [240,4369,8738,17487,35208,61440]
theorem n571 : impossible 5 w571.toFinset :=
  closeState (known := []) w571 (by decide) (by decide +kernel) (nilbad 4)

def w572 : List Mask := [240,4369,8738,17487,36744,61455]
theorem n572 : impossible 5 w572.toFinset :=
  closeState (known := []) w572 (by decide) (by decide +kernel) (nilbad 4)

def w573 : List Mask := [240,4369,8738,17487,36744,63624]
theorem n573 : impossible 5 w573.toFinset :=
  closeState (known := []) w573 (by decide) (by decide +kernel) (nilbad 4)

def w574 : List Mask := [240,4369,8738,17487,39321,65280]
theorem n574 : impossible 5 w574.toFinset :=
  closeState (known := [w188.toFinset, w224.toFinset, w236.toFinset]) w574 (by decide) (by decide +kernel) (consbad n188 (consbad n224 (consbad n236 (nilbad 4))))

def w575 : List Mask := [240,4369,8738,17487,43690,65280]
theorem n575 : impossible 5 w575.toFinset :=
  closeState (known := [w195.toFinset, w238.toFinset]) w575 (by decide) (by decide +kernel) (consbad n195 (consbad n238 (nilbad 4)))

def w576 : List Mask := [240,4369,8738,17743,34952,61440]
theorem n576 : impossible 5 w576.toFinset :=
  closeState (known := [w225.toFinset, w239.toFinset]) w576 (by decide) (by decide +kernel) (consbad n225 (consbad n239 (nilbad 4)))

def w577 : List Mask := [240,4369,8738,20303,34952,61455]
theorem n577 : impossible 5 w577.toFinset :=
  closeState (known := [w240.toFinset]) w577 (by decide) (by decide +kernel) (consbad n240 (nilbad 4))

def w578 : List Mask := [240,4369,8738,20303,34952,62543]
theorem n578 : impossible 5 w578.toFinset :=
  closeState (known := [w226.toFinset, w241.toFinset]) w578 (by decide) (by decide +kernel) (consbad n226 (consbad n241 (nilbad 4)))

def w579 : List Mask := [240,4369,8994,17487,34952,61440]
theorem n579 : impossible 5 w579.toFinset :=
  closeState (known := [w227.toFinset, w242.toFinset]) w579 (by decide) (by decide +kernel) (consbad n227 (consbad n242 (nilbad 4)))

def w580 : List Mask := [240,4369,12066,17487,34952,61455]
theorem n580 : impossible 5 w580.toFinset :=
  closeState (known := [w243.toFinset]) w580 (by decide) (by decide +kernel) (consbad n243 (nilbad 4))

def w581 : List Mask := [240,4369,12066,17487,34952,61986]
theorem n581 : impossible 5 w581.toFinset :=
  closeState (known := [w228.toFinset, w244.toFinset]) w581 (by decide) (by decide +kernel) (consbad n228 (consbad n244 (nilbad 4)))

def w582 : List Mask := [240,4369,12066,17487,43690,61440]
theorem n582 : impossible 5 w582.toFinset :=
  closeState (known := [w195.toFinset, w245.toFinset]) w582 (by decide) (by decide +kernel) (consbad n195 (consbad n245 (nilbad 4)))

def w583 : List Mask := [240,4593,8738,17487,34952,65280]
theorem n583 : impossible 5 w583.toFinset :=
  closeState (known := [w235.toFinset]) w583 (by decide) (by decide +kernel) (consbad n235 (nilbad 4))

def w584 : List Mask := [248,3840,4369,8738,17487,61440]
theorem n584 : impossible 5 w584.toFinset :=
  closeState (known := [w197.toFinset, w208.toFinset]) w584 (by decide) (by decide +kernel) (consbad n197 (consbad n208 (nilbad 4)))

def w585 : List Mask := [256,4369,8738,17487,35064,61440]
theorem n585 : impossible 5 w585.toFinset :=
  closeState (known := [w218.toFinset, w225.toFinset, w227.toFinset]) w585 (by decide) (by decide +kernel) (consbad n218 (consbad n225 (consbad n227 (nilbad 4))))

def w586 : List Mask := [256,4593,8738,17487,34952,61440]
theorem n586 : impossible 5 w586.toFinset :=
  closeState (known := [w230.toFinset, w239.toFinset, w242.toFinset]) w586 (by decide) (by decide +kernel) (consbad n230 (consbad n239 (consbad n242 (nilbad 4))))

def w587 : List Mask := [271,4369,8738,17476,35064,61440]
theorem n587 : impossible 5 w587.toFinset :=
  closeState (known := [w225.toFinset]) w587 (by decide) (by decide +kernel) (consbad n225 (nilbad 4))

def w588 : List Mask := [271,4593,8738,17476,34952,61440]
theorem n588 : impossible 5 w588.toFinset :=
  closeState (known := [w198.toFinset, w199.toFinset, w239.toFinset]) w588 (by decide) (by decide +kernel) (consbad n198 (consbad n199 (consbad n239 (nilbad 4))))

def w589 : List Mask := [3840,4096,4369,8738,17487,35064]
theorem n589 : impossible 5 w589.toFinset :=
  closeState (known := [w202.toFinset, w203.toFinset, w217.toFinset]) w589 (by decide) (by decide +kernel) (consbad n202 (consbad n203 (consbad n217 (nilbad 4))))

def w590 : List Mask := [3840,4096,4593,8738,17487,34952]
theorem n590 : impossible 5 w590.toFinset :=
  closeState (known := [w204.toFinset, w206.toFinset, w229.toFinset]) w590 (by decide) (by decide +kernel) (consbad n204 (consbad n206 (consbad n229 (nilbad 4))))

def w591 : List Mask := [3840,4111,4369,8738,17476,35064]
theorem n591 : impossible 5 w591.toFinset :=
  closeState (known := [w202.toFinset]) w591 (by decide) (by decide +kernel) (consbad n202 (nilbad 4))

def w592 : List Mask := [3840,4111,4593,8738,17476,34952]
theorem n592 : impossible 5 w592.toFinset :=
  closeState (known := [w204.toFinset, w211.toFinset, w212.toFinset]) w592 (by decide) (by decide +kernel) (consbad n204 (consbad n211 (consbad n212 (nilbad 4))))

def w593 : List Mask := [3840,4369,8738,17487,35064,61455]
theorem n593 : impossible 5 w593.toFinset :=
  closeState (known := [w219.toFinset]) w593 (by decide) (by decide +kernel) (consbad n219 (nilbad 4))

def w594 : List Mask := [3840,4369,8738,17487,35064,61986]
theorem n594 : impossible 5 w594.toFinset :=
  closeState (known := [w220.toFinset, w228.toFinset]) w594 (by decide) (by decide +kernel) (consbad n220 (consbad n228 (nilbad 4)))

def w595 : List Mask := [3840,4369,8738,17487,35064,62532]
theorem n595 : impossible 5 w595.toFinset :=
  closeState (known := [w221.toFinset]) w595 (by decide) (by decide +kernel) (consbad n221 (nilbad 4))

def w596 : List Mask := [3840,4369,8738,17487,35064,62543]
theorem n596 : impossible 5 w596.toFinset :=
  closeState (known := [w222.toFinset, w226.toFinset]) w596 (by decide) (by decide +kernel) (consbad n222 (consbad n226 (nilbad 4)))

def w597 : List Mask := [3840,4369,8738,17487,35064,63624]
theorem n597 : impossible 5 w597.toFinset :=
  closeState (known := [w223.toFinset]) w597 (by decide) (by decide +kernel) (consbad n223 (nilbad 4))

def w598 : List Mask := [3840,4369,8738,17487,35064,65280]
theorem n598 : impossible 5 w598.toFinset :=
  closeState (known := []) w598 (by decide) (by decide +kernel) (nilbad 4)

def w599 : List Mask := [3840,4369,8738,17487,39417,61440]
theorem n599 : impossible 5 w599.toFinset :=
  closeState (known := [w224.toFinset]) w599 (by decide) (by decide +kernel) (consbad n224 (nilbad 4))

def w600 : List Mask := [3840,4593,8738,17487,34952,61455]
theorem n600 : impossible 5 w600.toFinset :=
  closeState (known := [w231.toFinset, w240.toFinset, w243.toFinset]) w600 (by decide) (by decide +kernel) (consbad n231 (consbad n240 (consbad n243 (nilbad 4))))

def w601 : List Mask := [3840,4593,8738,17487,34952,61986]
theorem n601 : impossible 5 w601.toFinset :=
  closeState (known := [w207.toFinset, w232.toFinset, w244.toFinset]) w601 (by decide) (by decide +kernel) (consbad n207 (consbad n232 (consbad n244 (nilbad 4))))

def w602 : List Mask := [3840,4593,8738,17487,34952,62532]
theorem n602 : impossible 5 w602.toFinset :=
  closeState (known := [w233.toFinset]) w602 (by decide) (by decide +kernel) (consbad n233 (nilbad 4))

def w603 : List Mask := [3840,4593,8738,17487,34952,62543]
theorem n603 : impossible 5 w603.toFinset :=
  closeState (known := [w234.toFinset, w241.toFinset]) w603 (by decide) (by decide +kernel) (consbad n234 (consbad n241 (nilbad 4)))

def w604 : List Mask := [3840,4593,8738,17487,34952,65280]
theorem n604 : impossible 5 w604.toFinset :=
  closeState (known := []) w604 (by decide) (by decide +kernel) (nilbad 4)

def w605 : List Mask := [3840,4593,8738,17487,35064,61440]
theorem n605 : impossible 5 w605.toFinset :=
  closeState (known := [w235.toFinset]) w605 (by decide) (by decide +kernel) (consbad n235 (nilbad 4))

def w606 : List Mask := [3840,4593,8738,17487,39321,61440]
theorem n606 : impossible 5 w606.toFinset :=
  closeState (known := [w236.toFinset]) w606 (by decide) (by decide +kernel) (consbad n236 (nilbad 4))

def w607 : List Mask := [3840,4593,8738,17487,39417,61440]
theorem n607 : impossible 5 w607.toFinset :=
  closeState (known := [w237.toFinset]) w607 (by decide) (by decide +kernel) (consbad n237 (nilbad 4))

def w608 : List Mask := [3840,4593,8738,17487,43690,61440]
theorem n608 : impossible 5 w608.toFinset :=
  closeState (known := [w207.toFinset, w238.toFinset, w245.toFinset]) w608 (by decide) (by decide +kernel) (consbad n207 (consbad n238 (consbad n245 (nilbad 4))))

def w609 : List Mask := [3855,4369,8738,17476,35064,61455]
theorem n609 : impossible 5 w609.toFinset :=
  closeState (known := []) w609 (by decide) (by decide +kernel) (nilbad 4)

def w610 : List Mask := [3855,4369,8738,17487,35064,61440]
theorem n610 : impossible 5 w610.toFinset :=
  closeState (known := [w219.toFinset]) w610 (by decide) (by decide +kernel) (consbad n219 (nilbad 4))

def w611 : List Mask := [3855,4593,8738,17476,34952,61455]
theorem n611 : impossible 5 w611.toFinset :=
  closeState (known := [w209.toFinset, w240.toFinset]) w611 (by decide) (by decide +kernel) (consbad n209 (consbad n240 (nilbad 4)))

def w612 : List Mask := [3855,4593,8738,17487,34952,61440]
theorem n612 : impossible 5 w612.toFinset :=
  closeState (known := [w209.toFinset, w210.toFinset, w231.toFinset]) w612 (by decide) (by decide +kernel) (consbad n209 (consbad n210 (consbad n231 (nilbad 4))))

def w613 : List Mask := [4369,4593,8738,17487,34952,65280]
theorem n613 : impossible 5 w613.toFinset :=
  closeState (known := [w214.toFinset, w224.toFinset, w236.toFinset]) w613 (by decide) (by decide +kernel) (consbad n214 (consbad n224 (consbad n236 (nilbad 4))))

def w614 : List Mask := [4369,8738,12066,17487,35064,61440]
theorem n614 : impossible 5 w614.toFinset :=
  closeState (known := [w220.toFinset, w228.toFinset]) w614 (by decide) (by decide +kernel) (consbad n220 (consbad n228 (nilbad 4)))

def w615 : List Mask := [4369,8738,17476,17487,35064,65280]
theorem n615 : impossible 5 w615.toFinset :=
  closeState (known := [w221.toFinset]) w615 (by decide) (by decide +kernel) (consbad n221 (nilbad 4))

def w616 : List Mask := [4369,8738,17487,20292,35064,61440]
theorem n616 : impossible 5 w616.toFinset :=
  closeState (known := [w221.toFinset]) w616 (by decide) (by decide +kernel) (consbad n221 (nilbad 4))

def w617 : List Mask := [4369,8738,17487,20303,35064,61440]
theorem n617 : impossible 5 w617.toFinset :=
  closeState (known := [w222.toFinset, w226.toFinset]) w617 (by decide) (by decide +kernel) (consbad n222 (consbad n226 (nilbad 4)))

def w618 : List Mask := [4369,8738,17487,34952,35064,65280]
theorem n618 : impossible 5 w618.toFinset :=
  closeState (known := [w223.toFinset]) w618 (by decide) (by decide +kernel) (consbad n223 (nilbad 4))

def w619 : List Mask := [4369,8738,17487,35064,36744,61440]
theorem n619 : impossible 5 w619.toFinset :=
  closeState (known := [w223.toFinset]) w619 (by decide) (by decide +kernel) (consbad n223 (nilbad 4))

def w620 : List Mask := [4369,8738,17487,35064,61440,65280]
theorem n620 : impossible 5 w620.toFinset :=
  closeState (known := []) w620 (by decide) (by decide +kernel) (nilbad 4)

def w621 : List Mask := [4369,8738,17487,35064,65280]
theorem n621 : impossible 5 w621.toFinset :=
  closeState (known := [w213.toFinset, w220.toFinset, w222.toFinset, w224.toFinset]) w621 (by decide) (by decide +kernel) (consbad n213 (consbad n220 (consbad n222 (consbad n224 (nilbad 4)))))

def w622 : List Mask := [4593,8738,12066,17487,34952,61440]
theorem n622 : impossible 5 w622.toFinset :=
  closeState (known := [w232.toFinset, w244.toFinset, w245.toFinset]) w622 (by decide) (by decide +kernel) (consbad n232 (consbad n244 (consbad n245 (nilbad 4))))

def w623 : List Mask := [4593,8738,17476,17487,34952,65280]
theorem n623 : impossible 5 w623.toFinset :=
  closeState (known := [w233.toFinset]) w623 (by decide) (by decide +kernel) (consbad n233 (nilbad 4))

def w624 : List Mask := [4593,8738,17487,20292,34952,61440]
theorem n624 : impossible 5 w624.toFinset :=
  closeState (known := [w233.toFinset]) w624 (by decide) (by decide +kernel) (consbad n233 (nilbad 4))

def w625 : List Mask := [4593,8738,17487,20303,34952,61440]
theorem n625 : impossible 5 w625.toFinset :=
  closeState (known := [w234.toFinset, w241.toFinset]) w625 (by decide) (by decide +kernel) (consbad n234 (consbad n241 (nilbad 4)))

def w626 : List Mask := [4593,8738,17487,34952,61440,65280]
theorem n626 : impossible 5 w626.toFinset :=
  closeState (known := []) w626 (by decide) (by decide +kernel) (nilbad 4)

def w627 : List Mask := [4593,8738,17487,34952,65280]
theorem n627 : impossible 5 w627.toFinset :=
  closeState (known := [w44.toFinset, w214.toFinset, w232.toFinset, w234.toFinset, w237.toFinset, w238.toFinset]) w627 (by decide) (by decide +kernel) (consbad n44 (consbad n214 (consbad n232 (consbad n234 (consbad n237 (consbad n238 (nilbad 4)))))))

def w628 : List Mask := [8,15,240,3840,4369,8738,62532]
theorem n628 : impossible 6 w628.toFinset :=
  closeState (known := [w246.toFinset, w247.toFinset, w250.toFinset, w271.toFinset, w278.toFinset, w280.toFinset, w403.toFinset]) w628 (by decide) (by decide +kernel) (consbad n246 (consbad n247 (consbad n250 (consbad n271 (consbad n278 (consbad n280 (consbad n403 (nilbad 5))))))))

def w629 : List Mask := [8,15,240,3840,4369,17476,61986]
theorem n629 : impossible 6 w629.toFinset :=
  closeState (known := [w248.toFinset, w249.toFinset, w251.toFinset, w273.toFinset, w279.toFinset, w281.toFinset, w404.toFinset]) w629 (by decide) (by decide +kernel) (consbad n248 (consbad n249 (consbad n251 (consbad n273 (consbad n279 (consbad n281 (consbad n404 (nilbad 5))))))))

def w630 : List Mask := [8,15,240,4369,8738,17476,65280]
theorem n630 : impossible 6 w630.toFinset :=
  closeState (known := [w246.toFinset, w248.toFinset, w252.toFinset, w255.toFinset, w289.toFinset, w321.toFinset, w396.toFinset, w405.toFinset]) w630 (by decide) (by decide +kernel) (consbad n246 (consbad n248 (consbad n252 (consbad n255 (consbad n289 (consbad n321 (consbad n396 (consbad n405 (nilbad 5)))))))))

def w631 : List Mask := [8,15,240,4369,8738,20292,61440]
theorem n631 : impossible 6 w631.toFinset :=
  closeState (known := [w246.toFinset, w249.toFinset, w253.toFinset, w295.toFinset, w322.toFinset, w397.toFinset, w406.toFinset]) w631 (by decide) (by decide +kernel) (consbad n246 (consbad n249 (consbad n253 (consbad n295 (consbad n322 (consbad n397 (consbad n406 (nilbad 5))))))))

def w632 : List Mask := [8,15,240,4369,12066,17476,61440]
theorem n632 : impossible 6 w632.toFinset :=
  closeState (known := [w247.toFinset, w248.toFinset, w254.toFinset, w328.toFinset, w348.toFinset, w398.toFinset, w407.toFinset]) w632 (by decide) (by decide +kernel) (consbad n247 (consbad n248 (consbad n254 (consbad n328 (consbad n348 (consbad n398 (consbad n407 (nilbad 5))))))))

def w633 : List Mask := [8,15,3840,4593,8738,17476,61440]
theorem n633 : impossible 6 w633.toFinset :=
  closeState (known := [w250.toFinset, w251.toFinset, w252.toFinset, w253.toFinset, w254.toFinset, w256.toFinset, w416.toFinset, w428.toFinset, w446.toFinset, w447.toFinset]) w633 (by decide) (by decide +kernel) (consbad n250 (consbad n251 (consbad n252 (consbad n253 (consbad n254 (consbad n256 (consbad n416 (consbad n428 (consbad n446 (consbad n447 (nilbad 5)))))))))))

def w634 : List Mask := [8,240,3840,4369,8738,17487,61440]
theorem n634 : impossible 6 w634.toFinset :=
  closeState (known := [w255.toFinset, w256.toFinset, w551.toFinset, w554.toFinset, w584.toFinset]) w634 (by decide) (by decide +kernel) (consbad n255 (consbad n256 (consbad n551 (consbad n554 (consbad n584 (nilbad 5))))))

def w635 : List Mask := [15,64,240,3840,4369,8738,63624]
theorem n635 : impossible 6 w635.toFinset :=
  closeState (known := [w257.toFinset, w258.toFinset, w272.toFinset, w282.toFinset, w539.toFinset]) w635 (by decide) (by decide +kernel) (consbad n257 (consbad n258 (consbad n272 (consbad n282 (consbad n539 (nilbad 5))))))

def w636 : List Mask := [15,64,240,3840,4369,34952,61986]
theorem n636 : impossible 6 w636.toFinset :=
  closeState (known := [w259.toFinset, w260.toFinset, w261.toFinset, w275.toFinset, w283.toFinset, w540.toFinset]) w636 (by decide) (by decide +kernel) (consbad n259 (consbad n260 (consbad n261 (consbad n275 (consbad n283 (consbad n540 (nilbad 5)))))))

def w637 : List Mask := [15,64,240,4369,8738,34952,65280]
theorem n637 : impossible 6 w637.toFinset :=
  closeState (known := [w257.toFinset, w259.toFinset, w262.toFinset, w263.toFinset, w305.toFinset, w323.toFinset, w541.toFinset]) w637 (by decide) (by decide +kernel) (consbad n257 (consbad n259 (consbad n262 (consbad n263 (consbad n305 (consbad n323 (consbad n541 (nilbad 5))))))))

def w638 : List Mask := [15,64,240,4369,8738,36744,61440]
theorem n638 : impossible 6 w638.toFinset :=
  closeState (known := [w257.toFinset, w260.toFinset, w311.toFinset, w324.toFinset, w542.toFinset]) w638 (by decide) (by decide +kernel) (consbad n257 (consbad n260 (consbad n311 (consbad n324 (consbad n542 (nilbad 5))))))

def w639 : List Mask := [15,64,240,4369,12066,34952,61440]
theorem n639 : impossible 6 w639.toFinset :=
  closeState (known := [w258.toFinset, w259.toFinset, w264.toFinset, w337.toFinset, w349.toFinset, w543.toFinset]) w639 (by decide) (by decide +kernel) (consbad n258 (consbad n259 (consbad n264 (consbad n337 (consbad n349 (consbad n543 (nilbad 5)))))))

def w640 : List Mask := [15,64,3840,4369,8738,35064,61440]
theorem n640 : impossible 6 w640.toFinset :=
  closeState (known := [w262.toFinset, w413.toFinset, w544.toFinset]) w640 (by decide) (by decide +kernel) (consbad n262 (consbad n413 (consbad n544 (nilbad 5))))

def w641 : List Mask := [15,64,3840,4593,8738,34952,61440]
theorem n641 : impossible 6 w641.toFinset :=
  closeState (known := [w261.toFinset, w263.toFinset, w264.toFinset, w418.toFinset, w429.toFinset, w450.toFinset, w545.toFinset]) w641 (by decide) (by decide +kernel) (consbad n261 (consbad n263 (consbad n264 (consbad n418 (consbad n429 (consbad n450 (consbad n545 (nilbad 5))))))))

def w642 : List Mask := [15,96,3840,4369,8738,34952,61440]
theorem n642 : impossible 6 w642.toFinset :=
  closeState (known := [w265.toFinset, w266.toFinset, w267.toFinset, w268.toFinset, w269.toFinset, w270.toFinset]) w642 (by decide) (by decide +kernel) (consbad n265 (consbad n266 (consbad n267 (consbad n268 (consbad n269 (consbad n270 (nilbad 5)))))))

def w643 : List Mask := [15,240,256,4369,8738,17476,63624]
theorem n643 : impossible 6 w643.toFinset :=
  closeState (known := [w288.toFinset, w293.toFinset, w325.toFinset, w546.toFinset]) w643 (by decide) (by decide +kernel) (consbad n288 (consbad n293 (consbad n325 (consbad n546 (nilbad 5)))))

def w644 : List Mask := [15,240,256,4369,8738,34952,62532]
theorem n644 : impossible 6 w644.toFinset :=
  closeState (known := [w304.toFinset, w310.toFinset, w326.toFinset, w408.toFinset, w547.toFinset]) w644 (by decide) (by decide +kernel) (consbad n304 (consbad n310 (consbad n326 (consbad n408 (consbad n547 (nilbad 5))))))

def w645 : List Mask := [15,240,256,4369,17476,34952,61986]
theorem n645 : impossible 6 w645.toFinset :=
  closeState (known := [w354.toFinset, w357.toFinset, w371.toFinset, w409.toFinset, w548.toFinset]) w645 (by decide) (by decide +kernel) (consbad n354 (consbad n357 (consbad n371 (consbad n409 (consbad n548 (nilbad 5))))))

def w646 : List Mask := [15,240,3840,4369,8738,17476,39048]
theorem n646 : impossible 6 w646.toFinset :=
  closeState (known := [w287.toFinset, w294.toFinset, w327.toFinset, w549.toFinset]) w646 (by decide) (by decide +kernel) (consbad n287 (consbad n294 (consbad n327 (consbad n549 (nilbad 5)))))

def w647 : List Mask := [15,240,3840,4369,8738,17476,61448]
theorem n647 : impossible 6 w647.toFinset :=
  closeState (known := [w273.toFinset, w289.toFinset, w295.toFinset, w328.toFinset, w416.toFinset]) w647 (by decide) (by decide +kernel) (consbad n273 (consbad n289 (consbad n295 (consbad n328 (consbad n416 (nilbad 5))))))

def w648 : List Mask := [15,240,3840,4369,8738,17476,64170]
theorem n648 : impossible 6 w648.toFinset :=
  closeState (known := [w274.toFinset, w291.toFinset, w296.toFinset, w329.toFinset]) w648 (by decide) (by decide +kernel) (consbad n274 (consbad n291 (consbad n296 (consbad n329 (nilbad 5)))))

def w649 : List Mask := [15,240,3840,4369,8738,17476,65416]
theorem n649 : impossible 6 w649.toFinset :=
  closeState (known := [w297.toFinset, w330.toFinset]) w649 (by decide) (by decide +kernel) (consbad n297 (consbad n330 (nilbad 5)))

def w650 : List Mask := [15,240,3840,4369,8738,17487,63624]
theorem n650 : impossible 6 w650.toFinset :=
  closeState (known := [w292.toFinset, w298.toFinset, w332.toFinset, w555.toFinset]) w650 (by decide) (by decide +kernel) (consbad n292 (consbad n298 (consbad n332 (consbad n555 (nilbad 5)))))

def w651 : List Mask := [15,240,3840,4369,8738,20292,63624]
theorem n651 : impossible 6 w651.toFinset :=
  closeState (known := [w297.toFinset, w333.toFinset]) w651 (by decide) (by decide +kernel) (consbad n297 (consbad n333 (nilbad 5)))

def w652 : List Mask := [15,240,3840,4369,8738,21572,34952]
theorem n652 : impossible 6 w652.toFinset :=
  closeState (known := [w299.toFinset, w301.toFinset, w334.toFinset, w412.toFinset, w417.toFinset, w550.toFinset]) w652 (by decide) (by decide +kernel) (consbad n299 (consbad n301 (consbad n334 (consbad n412 (consbad n417 (consbad n550 (nilbad 5)))))))

def w653 : List Mask := [15,240,3840,4369,8738,26214,63624]
theorem n653 : impossible 6 w653.toFinset :=
  closeState (known := [w265.toFinset, w274.toFinset, w302.toFinset, w303.toFinset, w335.toFinset]) w653 (by decide) (by decide +kernel) (consbad n265 (consbad n274 (consbad n302 (consbad n303 (consbad n335 (nilbad 5))))))

def w654 : List Mask := [15,240,3840,4369,8738,34952,61504]
theorem n654 : impossible 6 w654.toFinset :=
  closeState (known := [w275.toFinset, w305.toFinset, w311.toFinset, w337.toFinset, w418.toFinset]) w654 (by decide) (by decide +kernel) (consbad n275 (consbad n305 (consbad n311 (consbad n337 (consbad n418 (nilbad 5))))))

def w655 : List Mask := [15,240,3840,4369,8738,34952,62543]
theorem n655 : impossible 6 w655.toFinset :=
  closeState (known := [w307.toFinset, w312.toFinset, w338.toFinset, w419.toFinset, w556.toFinset]) w655 (by decide) (by decide +kernel) (consbad n307 (consbad n312 (consbad n338 (consbad n419 (consbad n556 (nilbad 5))))))

def w656 : List Mask := [15,240,3840,4369,8738,34952,63078]
theorem n656 : impossible 6 w656.toFinset :=
  closeState (known := [w276.toFinset, w308.toFinset, w313.toFinset, w339.toFinset, w420.toFinset]) w656 (by decide) (by decide +kernel) (consbad n276 (consbad n308 (consbad n313 (consbad n339 (consbad n420 (nilbad 5))))))

def w657 : List Mask := [15,240,3840,4369,8738,34952,65348]
theorem n657 : impossible 6 w657.toFinset :=
  closeState (known := [w314.toFinset, w340.toFinset, w421.toFinset]) w657 (by decide) (by decide +kernel) (consbad n314 (consbad n340 (consbad n421 (nilbad 5))))

def w658 : List Mask := [15,240,3840,4369,8738,35064,62532]
theorem n658 : impossible 6 w658.toFinset :=
  closeState (known := [w309.toFinset, w342.toFinset, w422.toFinset]) w658 (by decide) (by decide +kernel) (consbad n309 (consbad n342 (consbad n422 (nilbad 5))))

def w659 : List Mask := [15,240,3840,4369,8738,36744,62532]
theorem n659 : impossible 6 w659.toFinset :=
  closeState (known := [w314.toFinset, w343.toFinset, w423.toFinset]) w659 (by decide) (by decide +kernel) (consbad n314 (consbad n343 (consbad n423 (nilbad 5))))

def w660 : List Mask := [15,240,3840,4369,8738,39321,62532]
theorem n660 : impossible 6 w660.toFinset :=
  closeState (known := [w315.toFinset, w344.toFinset, w424.toFinset]) w660 (by decide) (by decide +kernel) (consbad n315 (consbad n344 (consbad n424 (nilbad 5))))

def w661 : List Mask := [15,240,3840,4369,8738,43690,62532]
theorem n661 : impossible 6 w661.toFinset :=
  closeState (known := [w276.toFinset, w316.toFinset, w317.toFinset, w345.toFinset, w426.toFinset]) w661 (by decide) (by decide +kernel) (consbad n276 (consbad n316 (consbad n317 (consbad n345 (consbad n426 (nilbad 5))))))

def w662 : List Mask := [15,240,3840,4369,8738,62532,63624]
theorem n662 : impossible 6 w662.toFinset :=
  closeState (known := [w318.toFinset, w319.toFinset, w347.toFinset, w427.toFinset]) w662 (by decide) (by decide +kernel) (consbad n318 (consbad n319 (consbad n347 (consbad n427 (nilbad 5)))))

def w663 : List Mask := [15,240,3840,4369,8746,17476,61440]
theorem n663 : impossible 6 w663.toFinset :=
  closeState (known := [w271.toFinset, w273.toFinset, w321.toFinset, w322.toFinset, w348.toFinset, w428.toFinset, w551.toFinset]) w663 (by decide) (by decide +kernel) (consbad n271 (consbad n273 (consbad n321 (consbad n322 (consbad n348 (consbad n428 (consbad n551 (nilbad 5))))))))

def w664 : List Mask := [15,240,3840,4369,8802,34952,61440]
theorem n664 : impossible 6 w664.toFinset :=
  closeState (known := [w272.toFinset, w275.toFinset, w323.toFinset, w324.toFinset, w349.toFinset, w413.toFinset, w429.toFinset]) w664 (by decide) (by decide +kernel) (consbad n272 (consbad n275 (consbad n323 (consbad n324 (consbad n349 (consbad n413 (consbad n429 (nilbad 5))))))))

def w665 : List Mask := [15,240,3840,4369,12066,17476,63624]
theorem n665 : impossible 6 w665.toFinset :=
  closeState (known := [w330.toFinset, w333.toFinset]) w665 (by decide) (by decide +kernel) (consbad n330 (consbad n333 (nilbad 5)))

def w666 : List Mask := [15,240,3840,4369,12066,34952,62532]
theorem n666 : impossible 6 w666.toFinset :=
  closeState (known := [w340.toFinset, w343.toFinset, w430.toFinset]) w666 (by decide) (by decide +kernel) (consbad n340 (consbad n343 (consbad n430 (nilbad 5))))

def w667 : List Mask := [15,240,3840,4369,12834,17476,34952]
theorem n667 : impossible 6 w667.toFinset :=
  closeState (known := [w350.toFinset, w351.toFinset, w353.toFinset, w414.toFinset, w431.toFinset, w552.toFinset]) w667 (by decide) (by decide +kernel) (consbad n350 (consbad n351 (consbad n353 (consbad n414 (consbad n431 (consbad n552 (nilbad 5)))))))

def w668 : List Mask := [15,240,3840,4369,17476,34952,65314]
theorem n668 : impossible 6 w668.toFinset :=
  closeState (known := [w358.toFinset, w372.toFinset, w432.toFinset]) w668 (by decide) (by decide +kernel) (consbad n358 (consbad n372 (consbad n432 (nilbad 5))))

def w669 : List Mask := [15,240,3840,4369,17476,35064,61986]
theorem n669 : impossible 6 w669.toFinset :=
  closeState (known := [w356.toFinset, w373.toFinset, w433.toFinset]) w669 (by decide) (by decide +kernel) (consbad n356 (consbad n373 (consbad n433 (nilbad 5))))

def w670 : List Mask := [15,240,3840,4369,17476,36744,61986]
theorem n670 : impossible 6 w670.toFinset :=
  closeState (known := [w358.toFinset, w374.toFinset, w434.toFinset]) w670 (by decide) (by decide +kernel) (consbad n358 (consbad n374 (consbad n434 (nilbad 5))))

def w671 : List Mask := [15,240,3840,4369,17476,39321,61986]
theorem n671 : impossible 6 w671.toFinset :=
  closeState (known := [w359.toFinset, w375.toFinset, w435.toFinset]) w671 (by decide) (by decide +kernel) (consbad n359 (consbad n375 (consbad n435 (nilbad 5))))

def w672 : List Mask := [15,240,3840,4369,17476,43690,61986]
theorem n672 : impossible 6 w672.toFinset :=
  closeState (known := [w276.toFinset, w360.toFinset, w361.toFinset, w376.toFinset, w437.toFinset, w553.toFinset]) w672 (by decide) (by decide +kernel) (consbad n276 (consbad n360 (consbad n361 (consbad n376 (consbad n437 (consbad n553 (nilbad 5)))))))

def w673 : List Mask := [15,240,3840,4369,17476,61986,63624]
theorem n673 : impossible 6 w673.toFinset :=
  closeState (known := [w363.toFinset, w365.toFinset, w377.toFinset, w438.toFinset]) w673 (by decide) (by decide +kernel) (consbad n363 (consbad n365 (consbad n377 (consbad n438 (nilbad 5)))))

def w674 : List Mask := [15,240,3840,4369,17476,61986,64170]
theorem n674 : impossible 6 w674.toFinset :=
  closeState (known := [w277.toFinset, w364.toFinset, w366.toFinset, w378.toFinset, w439.toFinset]) w674 (by decide) (by decide +kernel) (consbad n277 (consbad n364 (consbad n366 (consbad n378 (consbad n439 (nilbad 5))))))

def w675 : List Mask := [15,240,3840,4369,17487,34952,61986]
theorem n675 : impossible 6 w675.toFinset :=
  closeState (known := [w369.toFinset, w370.toFinset, w379.toFinset, w440.toFinset, w557.toFinset]) w675 (by decide) (by decide +kernel) (consbad n369 (consbad n370 (consbad n379 (consbad n440 (consbad n557 (nilbad 5))))))

def w676 : List Mask := [15,240,3840,4369,20292,34952,61986]
theorem n676 : impossible 6 w676.toFinset :=
  closeState (known := [w372.toFinset, w374.toFinset, w441.toFinset]) w676 (by decide) (by decide +kernel) (consbad n372 (consbad n374 (consbad n441 (nilbad 5))))

def w677 : List Mask := [15,240,3840,4369,26214,34952,61986]
theorem n677 : impossible 6 w677.toFinset :=
  closeState (known := [w266.toFinset, w274.toFinset, w380.toFinset, w381.toFinset, w384.toFinset, w415.toFinset, w442.toFinset]) w677 (by decide) (by decide +kernel) (consbad n266 (consbad n274 (consbad n380 (consbad n381 (consbad n384 (consbad n415 (consbad n442 (nilbad 5))))))))

def w678 : List Mask := [15,240,3840,4369,26214,43690,61440]
theorem n678 : impossible 6 w678.toFinset :=
  closeState (known := [w267.toFinset, w274.toFinset, w276.toFinset, w382.toFinset, w383.toFinset, w386.toFinset, w443.toFinset]) w678 (by decide) (by decide +kernel) (consbad n267 (consbad n274 (consbad n276 (consbad n382 (consbad n383 (consbad n386 (consbad n443 (nilbad 5))))))))

def w679 : List Mask := [15,240,3840,4369,34952,61986,62532]
theorem n679 : impossible 6 w679.toFinset :=
  closeState (known := [w388.toFinset, w390.toFinset, w394.toFinset, w444.toFinset]) w679 (by decide) (by decide +kernel) (consbad n388 (consbad n390 (consbad n394 (consbad n444 (nilbad 5)))))

def w680 : List Mask := [15,240,3840,4369,34952,61986,63078]
theorem n680 : impossible 6 w680.toFinset :=
  closeState (known := [w266.toFinset, w277.toFinset, w389.toFinset, w391.toFinset, w395.toFinset, w445.toFinset]) w680 (by decide) (by decide +kernel) (consbad n266 (consbad n277 (consbad n389 (consbad n391 (consbad n395 (consbad n445 (nilbad 5)))))))

def w681 : List Mask := [15,240,3840,4377,8738,17476,61440]
theorem n681 : impossible 6 w681.toFinset :=
  closeState (known := [w278.toFinset, w279.toFinset, w396.toFinset, w397.toFinset, w398.toFinset, w446.toFinset, w554.toFinset]) w681 (by decide) (by decide +kernel) (consbad n278 (consbad n279 (consbad n396 (consbad n397 (consbad n398 (consbad n446 (consbad n554 (nilbad 5))))))))

def w682 : List Mask := [15,240,3840,4593,8738,34952,62532]
theorem n682 : impossible 6 w682.toFinset :=
  closeState (known := [w399.toFinset, w400.toFinset, w422.toFinset]) w682 (by decide) (by decide +kernel) (consbad n399 (consbad n400 (consbad n422 (nilbad 5))))

def w683 : List Mask := [15,240,3840,4593,17476,34952,61986]
theorem n683 : impossible 6 w683.toFinset :=
  closeState (known := [w261.toFinset, w401.toFinset, w402.toFinset, w433.toFinset]) w683 (by decide) (by decide +kernel) (consbad n261 (consbad n401 (consbad n402 (consbad n433 (nilbad 5)))))

def w684 : List Mask := [15,240,3848,4369,8738,17476,61440]
theorem n684 : impossible 6 w684.toFinset :=
  closeState (known := [w280.toFinset, w281.toFinset, w289.toFinset, w348.toFinset, w447.toFinset]) w684 (by decide) (by decide +kernel) (consbad n280 (consbad n281 (consbad n289 (consbad n348 (consbad n447 (nilbad 5))))))

def w685 : List Mask := [15,240,3855,4369,8738,17476,63624]
theorem n685 : impossible 6 w685.toFinset :=
  closeState (known := [w298.toFinset, w555.toFinset]) w685 (by decide) (by decide +kernel) (consbad n298 (consbad n555 (nilbad 5)))

def w686 : List Mask := [15,240,3855,4369,8738,34952,62532]
theorem n686 : impossible 6 w686.toFinset :=
  closeState (known := [w307.toFinset, w448.toFinset, w556.toFinset]) w686 (by decide) (by decide +kernel) (consbad n307 (consbad n448 (consbad n556 (nilbad 5))))

def w687 : List Mask := [15,240,3855,4369,17476,34952,61986]
theorem n687 : impossible 6 w687.toFinset :=
  closeState (known := [w379.toFinset, w449.toFinset, w557.toFinset]) w687 (by decide) (by decide +kernel) (consbad n379 (consbad n449 (consbad n557 (nilbad 5))))

def w688 : List Mask := [15,240,3904,4369,8738,34952,61440]
theorem n688 : impossible 6 w688.toFinset :=
  closeState (known := [w282.toFinset, w283.toFinset, w305.toFinset, w349.toFinset, w450.toFinset]) w688 (by decide) (by decide +kernel) (consbad n282 (consbad n283 (consbad n305 (consbad n349 (consbad n450 (nilbad 5))))))

def w689 : List Mask := [15,240,4096,4369,8738,17476,36744]
theorem n689 : impossible 6 w689.toFinset :=
  closeState (known := [w287.toFinset, w299.toFinset, w350.toFinset, w558.toFinset]) w689 (by decide) (by decide +kernel) (consbad n287 (consbad n299 (consbad n350 (consbad n558 (nilbad 5)))))

def w690 : List Mask := [15,240,4096,4369,8738,20292,34952]
theorem n690 : impossible 6 w690.toFinset :=
  closeState (known := [w294.toFinset, w301.toFinset, w351.toFinset, w451.toFinset, w559.toFinset]) w690 (by decide) (by decide +kernel) (consbad n294 (consbad n301 (consbad n351 (consbad n451 (consbad n559 (nilbad 5))))))

def w691 : List Mask := [15,240,4096,4369,12066,17476,34952]
theorem n691 : impossible 6 w691.toFinset :=
  closeState (known := [w327.toFinset, w334.toFinset, w353.toFinset, w452.toFinset, w560.toFinset]) w691 (by decide) (by decide +kernel) (consbad n327 (consbad n334 (consbad n353 (consbad n452 (consbad n560 (nilbad 5))))))

def w692 : List Mask := [15,240,4352,4369,8738,17476,34952]
theorem n692 : impossible 6 w692.toFinset :=
  closeState (known := [w284.toFinset, w286.toFinset, w300.toFinset, w352.toFinset, w453.toFinset, w454.toFinset, w561.toFinset, w562.toFinset]) w692 (by decide) (by decide +kernel) (consbad n284 (consbad n286 (consbad n300 (consbad n352 (consbad n453 (consbad n454 (consbad n561 (consbad n562 (nilbad 5)))))))))

def w693 : List Mask := [15,240,4369,7936,8738,17476,34952]
theorem n693 : impossible 6 w693.toFinset :=
  closeState (known := [w287.toFinset, w301.toFinset, w353.toFinset, w464.toFinset, w478.toFinset, w563.toFinset]) w693 (by decide) (by decide +kernel) (consbad n287 (consbad n301 (consbad n353 (consbad n464 (consbad n478 (consbad n563 (nilbad 5)))))))

def w694 : List Mask := [15,240,4369,8738,12066,17476,63624]
theorem n694 : impossible 6 w694.toFinset :=
  closeState (known := [w291.toFinset, w303.toFinset, w329.toFinset, w335.toFinset]) w694 (by decide) (by decide +kernel) (consbad n291 (consbad n303 (consbad n329 (consbad n335 (nilbad 5)))))

def w695 : List Mask := [15,240,4369,8738,12066,34952,62532]
theorem n695 : impossible 6 w695.toFinset :=
  closeState (known := [w308.toFinset, w317.toFinset, w339.toFinset, w345.toFinset, w479.toFinset]) w695 (by decide) (by decide +kernel) (consbad n308 (consbad n317 (consbad n339 (consbad n345 (consbad n479 (nilbad 5))))))

def w696 : List Mask := [15,240,4369,8738,17476,20292,63624]
theorem n696 : impossible 6 w696.toFinset :=
  closeState (known := []) w696 (by decide) (by decide +kernel) (nilbad 5)

def w697 : List Mask := [15,240,4369,8738,17476,34952,61696]
theorem n697 : impossible 6 w697.toFinset :=
  closeState (known := [w288.toFinset, w304.toFinset, w354.toFinset, w465.toFinset, w480.toFinset, w564.toFinset]) w697 (by decide) (by decide +kernel) (consbad n288 (consbad n304 (consbad n354 (consbad n465 (consbad n480 (consbad n564 (nilbad 5)))))))

def w698 : List Mask := [15,240,4369,8738,17476,34952,65295]
theorem n698 : impossible 6 w698.toFinset :=
  closeState (known := [w285.toFinset, w307.toFinset, w466.toFinset, w481.toFinset, w565.toFinset]) w698 (by decide) (by decide +kernel) (consbad n285 (consbad n307 (consbad n466 (consbad n481 (consbad n565 (nilbad 5))))))

def w699 : List Mask := [15,240,4369,8738,17476,34952,65314]
theorem n699 : impossible 6 w699.toFinset :=
  closeState (known := [w291.toFinset, w308.toFinset, w360.toFinset, w380.toFinset, w467.toFinset, w482.toFinset, w566.toFinset]) w699 (by decide) (by decide +kernel) (consbad n291 (consbad n308 (consbad n360 (consbad n380 (consbad n467 (consbad n482 (consbad n566 (nilbad 5))))))))

def w700 : List Mask := [15,240,4369,8738,17476,34952,65348]
theorem n700 : impossible 6 w700.toFinset :=
  closeState (known := [w468.toFinset, w483.toFinset, w567.toFinset]) w700 (by decide) (by decide +kernel) (consbad n468 (consbad n483 (consbad n567 (nilbad 5))))

def w701 : List Mask := [15,240,4369,8738,17476,34952,65416]
theorem n701 : impossible 6 w701.toFinset :=
  closeState (known := [w469.toFinset, w569.toFinset]) w701 (by decide) (by decide +kernel) (consbad n469 (consbad n569 (nilbad 5)))

def w702 : List Mask := [15,240,4369,8738,17476,35064,65280]
theorem n702 : impossible 6 w702.toFinset :=
  closeState (known := [w262.toFinset, w309.toFinset, w356.toFinset, w484.toFinset, w570.toFinset]) w702 (by decide) (by decide +kernel) (consbad n262 (consbad n309 (consbad n356 (consbad n484 (consbad n570 (nilbad 5))))))

def w703 : List Mask := [15,240,4369,8738,17476,35208,61440]
theorem n703 : impossible 6 w703.toFinset :=
  closeState (known := [w288.toFinset, w310.toFinset, w357.toFinset, w571.toFinset]) w703 (by decide) (by decide +kernel) (consbad n288 (consbad n310 (consbad n357 (consbad n571 (nilbad 5)))))

def w704 : List Mask := [15,240,4369,8738,17476,36744,61455]
theorem n704 : impossible 6 w704.toFinset :=
  closeState (known := [w312.toFinset, w572.toFinset]) w704 (by decide) (by decide +kernel) (consbad n312 (consbad n572 (nilbad 5)))

def w705 : List Mask := [15,240,4369,8738,17476,36744,61986]
theorem n705 : impossible 6 w705.toFinset :=
  closeState (known := [w291.toFinset, w313.toFinset, w361.toFinset, w381.toFinset]) w705 (by decide) (by decide +kernel) (consbad n291 (consbad n313 (consbad n361 (consbad n381 (nilbad 5)))))

def w706 : List Mask := [15,240,4369,8738,17476,36744,62532]
theorem n706 : impossible 6 w706.toFinset :=
  closeState (known := []) w706 (by decide) (by decide +kernel) (nilbad 5)

def w707 : List Mask := [15,240,4369,8738,17476,36744,63624]
theorem n707 : impossible 6 w707.toFinset :=
  closeState (known := [w290.toFinset, w573.toFinset]) w707 (by decide) (by decide +kernel) (consbad n290 (consbad n573 (nilbad 5)))

def w708 : List Mask := [15,240,4369,8738,17476,36744,65280]
theorem n708 : impossible 6 w708.toFinset :=
  closeState (known := [w290.toFinset, w314.toFinset, w358.toFinset, w485.toFinset]) w708 (by decide) (by decide +kernel) (consbad n290 (consbad n314 (consbad n358 (consbad n485 (nilbad 5)))))

def w709 : List Mask := [15,240,4369,8738,17476,36744,65416]
theorem n709 : impossible 6 w709.toFinset :=
  closeState (known := []) w709 (by decide) (by decide +kernel) (nilbad 5)

def w710 : List Mask := [15,240,4369,8738,17476,39321,65280]
theorem n710 : impossible 6 w710.toFinset :=
  closeState (known := [w284.toFinset, w315.toFinset, w359.toFinset, w470.toFinset, w486.toFinset, w574.toFinset]) w710 (by decide) (by decide +kernel) (consbad n284 (consbad n315 (consbad n359 (consbad n470 (consbad n486 (consbad n574 (nilbad 5)))))))

def w711 : List Mask := [15,240,4369,8738,17476,43690,65280]
theorem n711 : impossible 6 w711.toFinset :=
  closeState (known := [w291.toFinset, w316.toFinset, w360.toFinset, w382.toFinset, w488.toFinset, w575.toFinset]) w711 (by decide) (by decide +kernel) (consbad n291 (consbad n316 (consbad n360 (consbad n382 (consbad n488 (consbad n575 (nilbad 5)))))))

def w712 : List Mask := [15,240,4369,8738,17476,44970,61440]
theorem n712 : impossible 6 w712.toFinset :=
  closeState (known := [w291.toFinset, w317.toFinset, w361.toFinset, w383.toFinset]) w712 (by decide) (by decide +kernel) (consbad n291 (consbad n317 (consbad n361 (consbad n383 (nilbad 5)))))

def w713 : List Mask := [15,240,4369,8738,17476,61440,65416]
theorem n713 : impossible 6 w713.toFinset :=
  closeState (known := [w318.toFinset, w363.toFinset]) w713 (by decide) (by decide +kernel) (consbad n318 (consbad n363 (nilbad 5)))

def w714 : List Mask := [15,240,4369,8738,17476,63624,65280]
theorem n714 : impossible 6 w714.toFinset :=
  closeState (known := [w290.toFinset, w319.toFinset, w365.toFinset, w489.toFinset]) w714 (by decide) (by decide +kernel) (consbad n290 (consbad n319 (consbad n365 (consbad n489 (nilbad 5)))))

def w715 : List Mask := [15,240,4369,8738,17476,63624,65416]
theorem n715 : impossible 6 w715.toFinset :=
  closeState (known := []) w715 (by decide) (by decide +kernel) (nilbad 5)

def w716 : List Mask := [15,240,4369,8738,17476,65280,65416]
theorem n716 : impossible 6 w716.toFinset :=
  closeState (known := [w320.toFinset, w367.toFinset, w490.toFinset]) w716 (by decide) (by decide +kernel) (consbad n320 (consbad n367 (consbad n490 (nilbad 5))))

def w717 : List Mask := [15,240,4369,8738,17476,65416]
theorem n717 : impossible 6 w717.toFinset :=
  closeState (known := [w257.toFinset, w291.toFinset, w292.toFinset, w302.toFinset, w455.toFinset]) w717 (by decide) (by decide +kernel) (consbad n257 (consbad n291 (consbad n292 (consbad n302 (consbad n455 (nilbad 5))))))

def w718 : List Mask := [15,240,4369,8738,17487,34952,65280]
theorem n718 : impossible 6 w718.toFinset :=
  closeState (known := [w255.toFinset, w292.toFinset, w307.toFinset, w369.toFinset, w471.toFinset, w491.toFinset, w565.toFinset]) w718 (by decide) (by decide +kernel) (consbad n255 (consbad n292 (consbad n307 (consbad n369 (consbad n471 (consbad n491 (consbad n565 (nilbad 5))))))))

def w719 : List Mask := [15,240,4369,8738,17487,36744,61440]
theorem n719 : impossible 6 w719.toFinset :=
  closeState (known := [w292.toFinset, w312.toFinset, w370.toFinset, w572.toFinset]) w719 (by decide) (by decide +kernel) (consbad n292 (consbad n312 (consbad n370 (consbad n572 (nilbad 5)))))

def w720 : List Mask := [15,240,4369,8738,17732,34952,61440]
theorem n720 : impossible 6 w720.toFinset :=
  closeState (known := [w293.toFinset, w304.toFinset, w371.toFinset, w472.toFinset, w492.toFinset, w576.toFinset]) w720 (by decide) (by decide +kernel) (consbad n293 (consbad n304 (consbad n371 (consbad n472 (consbad n492 (consbad n576 (nilbad 5)))))))

def w721 : List Mask := [15,240,4369,8738,20292,34952,61455]
theorem n721 : impossible 6 w721.toFinset :=
  closeState (known := [w307.toFinset, w493.toFinset, w577.toFinset]) w721 (by decide) (by decide +kernel) (consbad n307 (consbad n493 (consbad n577 (nilbad 5))))

def w722 : List Mask := [15,240,4369,8738,20292,34952,61986]
theorem n722 : impossible 6 w722.toFinset :=
  closeState (known := [w296.toFinset, w308.toFinset, w376.toFinset, w384.toFinset, w494.toFinset]) w722 (by decide) (by decide +kernel) (consbad n296 (consbad n308 (consbad n376 (consbad n384 (consbad n494 (nilbad 5))))))

def w723 : List Mask := [15,240,4369,8738,20292,34952,62532]
theorem n723 : impossible 6 w723.toFinset :=
  closeState (known := [w306.toFinset, w473.toFinset, w495.toFinset]) w723 (by decide) (by decide +kernel) (consbad n306 (consbad n473 (consbad n495 (nilbad 5))))

def w724 : List Mask := [15,240,4369,8738,20292,34952,63624]
theorem n724 : impossible 6 w724.toFinset :=
  closeState (known := []) w724 (by decide) (by decide +kernel) (nilbad 5)

def w725 : List Mask := [15,240,4369,8738,20292,34952,65280]
theorem n725 : impossible 6 w725.toFinset :=
  closeState (known := [w297.toFinset, w306.toFinset, w372.toFinset, w496.toFinset]) w725 (by decide) (by decide +kernel) (consbad n297 (consbad n306 (consbad n372 (consbad n496 (nilbad 5)))))

def w726 : List Mask := [15,240,4369,8738,20292,34952,65348]
theorem n726 : impossible 6 w726.toFinset :=
  closeState (known := [w497.toFinset]) w726 (by decide) (by decide +kernel) (consbad n497 (nilbad 5))

def w727 : List Mask := [15,240,4369,8738,20292,35064,61440]
theorem n727 : impossible 6 w727.toFinset :=
  closeState (known := [w309.toFinset, w373.toFinset, w498.toFinset]) w727 (by decide) (by decide +kernel) (consbad n309 (consbad n373 (consbad n498 (nilbad 5))))

def w728 : List Mask := [15,240,4369,8738,20292,36744,61440]
theorem n728 : impossible 6 w728.toFinset :=
  closeState (known := [w297.toFinset, w314.toFinset, w374.toFinset, w499.toFinset]) w728 (by decide) (by decide +kernel) (consbad n297 (consbad n314 (consbad n374 (consbad n499 (nilbad 5)))))

def w729 : List Mask := [15,240,4369,8738,20292,39321,61440]
theorem n729 : impossible 6 w729.toFinset :=
  closeState (known := [w315.toFinset, w375.toFinset, w500.toFinset]) w729 (by decide) (by decide +kernel) (consbad n315 (consbad n375 (consbad n500 (nilbad 5))))

def w730 : List Mask := [15,240,4369,8738,20292,43690,61440]
theorem n730 : impossible 6 w730.toFinset :=
  closeState (known := [w296.toFinset, w316.toFinset, w376.toFinset, w386.toFinset, w502.toFinset]) w730 (by decide) (by decide +kernel) (consbad n296 (consbad n316 (consbad n376 (consbad n386 (consbad n502 (nilbad 5))))))

def w731 : List Mask := [15,240,4369,8738,20292,61440,63624]
theorem n731 : impossible 6 w731.toFinset :=
  closeState (known := [w319.toFinset, w377.toFinset, w503.toFinset]) w731 (by decide) (by decide +kernel) (consbad n319 (consbad n377 (consbad n503 (nilbad 5))))

def w732 : List Mask := [15,240,4369,8738,20292,63624]
theorem n732 : impossible 6 w732.toFinset :=
  closeState (known := [w296.toFinset, w298.toFinset, w303.toFinset, w456.toFinset]) w732 (by decide) (by decide +kernel) (consbad n296 (consbad n298 (consbad n303 (consbad n456 (nilbad 5)))))

def w733 : List Mask := [15,240,4369,8738,20303,34952,61440]
theorem n733 : impossible 6 w733.toFinset :=
  closeState (known := [w298.toFinset, w307.toFinset, w379.toFinset, w504.toFinset, w577.toFinset]) w733 (by decide) (by decide +kernel) (consbad n298 (consbad n307 (consbad n379 (consbad n504 (consbad n577 (nilbad 5))))))

def w734 : List Mask := [15,240,4369,8738,26214,34952,65280]
theorem n734 : impossible 6 w734.toFinset :=
  closeState (known := [w268.toFinset, w302.toFinset, w308.toFinset, w380.toFinset, w382.toFinset, w474.toFinset, w505.toFinset]) w734 (by decide) (by decide +kernel) (consbad n268 (consbad n302 (consbad n308 (consbad n380 (consbad n382 (consbad n474 (consbad n505 (nilbad 5))))))))

def w735 : List Mask := [15,240,4369,8738,26214,36744,61440]
theorem n735 : impossible 6 w735.toFinset :=
  closeState (known := [w269.toFinset, w302.toFinset, w313.toFinset, w381.toFinset, w383.toFinset]) w735 (by decide) (by decide +kernel) (consbad n269 (consbad n302 (consbad n313 (consbad n381 (consbad n383 (nilbad 5))))))

def w736 : List Mask := [15,240,4369,8738,28518,34952,61440]
theorem n736 : impossible 6 w736.toFinset :=
  closeState (known := [w303.toFinset, w308.toFinset, w384.toFinset, w386.toFinset, w506.toFinset]) w736 (by decide) (by decide +kernel) (consbad n303 (consbad n308 (consbad n384 (consbad n386 (consbad n506 (nilbad 5))))))

def w737 : List Mask := [15,240,4369,8738,34952,36744,62532]
theorem n737 : impossible 6 w737.toFinset :=
  closeState (known := []) w737 (by decide) (by decide +kernel) (nilbad 5)

def w738 : List Mask := [15,240,4369,8738,34952,61440,65348]
theorem n738 : impossible 6 w738.toFinset :=
  closeState (known := [w319.toFinset, w388.toFinset, w507.toFinset]) w738 (by decide) (by decide +kernel) (consbad n319 (consbad n388 (consbad n507 (nilbad 5))))

def w739 : List Mask := [15,240,4369,8738,34952,62532,65280]
theorem n739 : impossible 6 w739.toFinset :=
  closeState (known := [w306.toFinset, w318.toFinset, w390.toFinset, w508.toFinset]) w739 (by decide) (by decide +kernel) (consbad n306 (consbad n318 (consbad n390 (consbad n508 (nilbad 5)))))

def w740 : List Mask := [15,240,4369,8738,34952,62532,65348]
theorem n740 : impossible 6 w740.toFinset :=
  closeState (known := [w509.toFinset]) w740 (by decide) (by decide +kernel) (consbad n509 (nilbad 5))

def w741 : List Mask := [15,240,4369,8738,34952,65280,65348]
theorem n741 : impossible 6 w741.toFinset :=
  closeState (known := [w320.toFinset, w392.toFinset, w510.toFinset]) w741 (by decide) (by decide +kernel) (consbad n320 (consbad n392 (consbad n510 (nilbad 5))))

def w742 : List Mask := [15,240,4369,8738,34952,65348]
theorem n742 : impossible 6 w742.toFinset :=
  closeState (known := [w246.toFinset, w307.toFinset, w308.toFinset, w309.toFinset, w315.toFinset, w316.toFinset, w399.toFinset, w457.toFinset, w511.toFinset]) w742 (by decide) (by decide +kernel) (consbad n246 (consbad n307 (consbad n308 (consbad n309 (consbad n315 (consbad n316 (consbad n399 (consbad n457 (consbad n511 (nilbad 5))))))))))

def w743 : List Mask := [15,240,4369,8738,36744,61440,62532]
theorem n743 : impossible 6 w743.toFinset :=
  closeState (known := [w318.toFinset, w394.toFinset]) w743 (by decide) (by decide +kernel) (consbad n318 (consbad n394 (nilbad 5)))

def w744 : List Mask := [15,240,4369,8738,36744,62532]
theorem n744 : impossible 6 w744.toFinset :=
  closeState (known := [w312.toFinset, w313.toFinset, w317.toFinset, w458.toFinset]) w744 (by decide) (by decide +kernel) (consbad n312 (consbad n313 (consbad n317 (consbad n458 (nilbad 5)))))

def w745 : List Mask := [15,240,4369,8994,17476,34952,61440]
theorem n745 : impossible 6 w745.toFinset :=
  closeState (known := [w325.toFinset, w326.toFinset, w354.toFinset, w475.toFinset, w512.toFinset, w579.toFinset]) w745 (by decide) (by decide +kernel) (consbad n325 (consbad n326 (consbad n354 (consbad n475 (consbad n512 (consbad n579 (nilbad 5)))))))

def w746 : List Mask := [15,240,4369,12066,17476,34952,61455]
theorem n746 : impossible 6 w746.toFinset :=
  closeState (known := [w338.toFinset, w513.toFinset, w580.toFinset]) w746 (by decide) (by decide +kernel) (consbad n338 (consbad n513 (consbad n580 (nilbad 5))))

def w747 : List Mask := [15,240,4369,12066,17476,34952,61986]
theorem n747 : impossible 6 w747.toFinset :=
  closeState (known := [w329.toFinset, w339.toFinset, w355.toFinset, w361.toFinset, w384.toFinset, w476.toFinset, w514.toFinset, w581.toFinset]) w747 (by decide) (by decide +kernel) (consbad n329 (consbad n339 (consbad n355 (consbad n361 (consbad n384 (consbad n476 (consbad n514 (consbad n581 (nilbad 5)))))))))

def w748 : List Mask := [15,240,4369,12066,17476,34952,62532]
theorem n748 : impossible 6 w748.toFinset :=
  closeState (known := [w515.toFinset]) w748 (by decide) (by decide +kernel) (consbad n515 (nilbad 5))

def w749 : List Mask := [15,240,4369,12066,17476,34952,63624]
theorem n749 : impossible 6 w749.toFinset :=
  closeState (known := []) w749 (by decide) (by decide +kernel) (nilbad 5)

def w750 : List Mask := [15,240,4369,12066,17476,34952,65280]
theorem n750 : impossible 6 w750.toFinset :=
  closeState (known := [w330.toFinset, w340.toFinset, w355.toFinset, w516.toFinset]) w750 (by decide) (by decide +kernel) (consbad n330 (consbad n340 (consbad n355 (consbad n516 (nilbad 5)))))

def w751 : List Mask := [15,240,4369,12066,17476,34952,65314]
theorem n751 : impossible 6 w751.toFinset :=
  closeState (known := [w331.toFinset, w341.toFinset, w362.toFinset, w385.toFinset, w517.toFinset]) w751 (by decide) (by decide +kernel) (consbad n331 (consbad n341 (consbad n362 (consbad n385 (consbad n517 (nilbad 5))))))

def w752 : List Mask := [15,240,4369,12066,17476,35064,61440]
theorem n752 : impossible 6 w752.toFinset :=
  closeState (known := [w342.toFinset, w356.toFinset, w518.toFinset]) w752 (by decide) (by decide +kernel) (consbad n342 (consbad n356 (consbad n518 (nilbad 5))))

def w753 : List Mask := [15,240,4369,12066,17476,36744,61440]
theorem n753 : impossible 6 w753.toFinset :=
  closeState (known := [w330.toFinset, w343.toFinset, w358.toFinset, w519.toFinset]) w753 (by decide) (by decide +kernel) (consbad n330 (consbad n343 (consbad n358 (consbad n519 (nilbad 5)))))

def w754 : List Mask := [15,240,4369,12066,17476,39321,61440]
theorem n754 : impossible 6 w754.toFinset :=
  closeState (known := [w344.toFinset, w359.toFinset, w520.toFinset]) w754 (by decide) (by decide +kernel) (consbad n344 (consbad n359 (consbad n520 (nilbad 5))))

def w755 : List Mask := [15,240,4369,12066,17476,43690,61440]
theorem n755 : impossible 6 w755.toFinset :=
  closeState (known := [w329.toFinset, w345.toFinset, w360.toFinset, w386.toFinset, w522.toFinset, w582.toFinset]) w755 (by decide) (by decide +kernel) (consbad n329 (consbad n345 (consbad n360 (consbad n386 (consbad n522 (consbad n582 (nilbad 5)))))))

def w756 : List Mask := [15,240,4369,12066,17476,44970,61440]
theorem n756 : impossible 6 w756.toFinset :=
  closeState (known := [w331.toFinset, w346.toFinset, w362.toFinset, w387.toFinset, w523.toFinset]) w756 (by decide) (by decide +kernel) (consbad n331 (consbad n346 (consbad n362 (consbad n387 (consbad n523 (nilbad 5))))))

def w757 : List Mask := [15,240,4369,12066,17476,61440,63624]
theorem n757 : impossible 6 w757.toFinset :=
  closeState (known := [w347.toFinset, w365.toFinset, w524.toFinset]) w757 (by decide) (by decide +kernel) (consbad n347 (consbad n365 (consbad n524 (nilbad 5))))

def w758 : List Mask := [15,240,4369,12066,17476,63624]
theorem n758 : impossible 6 w758.toFinset :=
  closeState (known := [w258.toFinset, w331.toFinset, w332.toFinset, w336.toFinset, w459.toFinset]) w758 (by decide) (by decide +kernel) (consbad n258 (consbad n331 (consbad n332 (consbad n336 (consbad n459 (nilbad 5))))))

def w759 : List Mask := [15,240,4369,12066,17487,34952,61440]
theorem n759 : impossible 6 w759.toFinset :=
  closeState (known := [w332.toFinset, w338.toFinset, w369.toFinset, w525.toFinset, w580.toFinset]) w759 (by decide) (by decide +kernel) (consbad n332 (consbad n338 (consbad n369 (consbad n525 (consbad n580 (nilbad 5))))))

def w760 : List Mask := [15,240,4369,12066,20292,34952,61440]
theorem n760 : impossible 6 w760.toFinset :=
  closeState (known := [w333.toFinset, w340.toFinset, w372.toFinset, w526.toFinset]) w760 (by decide) (by decide +kernel) (consbad n333 (consbad n340 (consbad n372 (consbad n526 (nilbad 5)))))

def w761 : List Mask := [15,240,4369,12066,26214,34952,61440]
theorem n761 : impossible 6 w761.toFinset :=
  closeState (known := [w270.toFinset, w335.toFinset, w339.toFinset, w380.toFinset, w383.toFinset, w477.toFinset, w527.toFinset]) w761 (by decide) (by decide +kernel) (consbad n270 (consbad n335 (consbad n339 (consbad n380 (consbad n383 (consbad n477 (consbad n527 (nilbad 5))))))))

def w762 : List Mask := [15,240,4369,12066,28518,34952,61440]
theorem n762 : impossible 6 w762.toFinset :=
  closeState (known := [w270.toFinset, w336.toFinset, w341.toFinset, w385.toFinset, w387.toFinset, w528.toFinset]) w762 (by decide) (by decide +kernel) (consbad n270 (consbad n336 (consbad n341 (consbad n385 (consbad n387 (consbad n528 (nilbad 5)))))))

def w763 : List Mask := [15,240,4369,12066,34952,61440,62532]
theorem n763 : impossible 6 w763.toFinset :=
  closeState (known := [w347.toFinset, w390.toFinset, w529.toFinset]) w763 (by decide) (by decide +kernel) (consbad n347 (consbad n390 (consbad n529 (nilbad 5))))

def w764 : List Mask := [15,240,4369,12066,34952,62532]
theorem n764 : impossible 6 w764.toFinset :=
  closeState (known := [w247.toFinset, w338.toFinset, w341.toFinset, w342.toFinset, w344.toFinset, w346.toFinset, w400.toFinset, w460.toFinset, w530.toFinset]) w764 (by decide) (by decide +kernel) (consbad n247 (consbad n338 (consbad n341 (consbad n342 (consbad n344 (consbad n346 (consbad n400 (consbad n460 (consbad n530 (nilbad 5))))))))))

def w765 : List Mask := [15,240,4369,17476,20292,34952,61986]
theorem n765 : impossible 6 w765.toFinset :=
  closeState (known := [w531.toFinset]) w765 (by decide) (by decide +kernel) (consbad n531 (nilbad 5))

def w766 : List Mask := [15,240,4369,17476,34952,36744,61986]
theorem n766 : impossible 6 w766.toFinset :=
  closeState (known := []) w766 (by decide) (by decide +kernel) (nilbad 5)

def w767 : List Mask := [15,240,4369,17476,34952,61440,65314]
theorem n767 : impossible 6 w767.toFinset :=
  closeState (known := [w365.toFinset, w390.toFinset, w532.toFinset]) w767 (by decide) (by decide +kernel) (consbad n365 (consbad n390 (consbad n532 (nilbad 5))))

def w768 : List Mask := [15,240,4369,17476,34952,61986,65280]
theorem n768 : impossible 6 w768.toFinset :=
  closeState (known := [w355.toFinset, w363.toFinset, w388.toFinset, w533.toFinset]) w768 (by decide) (by decide +kernel) (consbad n355 (consbad n363 (consbad n388 (consbad n533 (nilbad 5)))))

def w769 : List Mask := [15,240,4369,17476,34952,61986,65314]
theorem n769 : impossible 6 w769.toFinset :=
  closeState (known := [w364.toFinset, w366.toFinset, w389.toFinset, w391.toFinset, w534.toFinset]) w769 (by decide) (by decide +kernel) (consbad n364 (consbad n366 (consbad n389 (consbad n391 (consbad n534 (nilbad 5))))))

def w770 : List Mask := [15,240,4369,17476,34952,65280,65314]
theorem n770 : impossible 6 w770.toFinset :=
  closeState (known := [w367.toFinset, w392.toFinset, w535.toFinset]) w770 (by decide) (by decide +kernel) (consbad n367 (consbad n392 (consbad n535 (nilbad 5))))

def w771 : List Mask := [15,240,4369,17476,34952,65314]
theorem n771 : impossible 6 w771.toFinset :=
  closeState (known := [w248.toFinset, w259.toFinset, w356.toFinset, w359.toFinset, w368.toFinset, w369.toFinset, w393.toFinset, w401.toFinset, w461.toFinset, w536.toFinset]) w771 (by decide) (by decide +kernel) (consbad n248 (consbad n259 (consbad n356 (consbad n359 (consbad n368 (consbad n369 (consbad n393 (consbad n401 (consbad n461 (consbad n536 (nilbad 5)))))))))))

def w772 : List Mask := [15,240,4369,17476,36744,61440,61986]
theorem n772 : impossible 6 w772.toFinset :=
  closeState (known := [w363.toFinset, w394.toFinset]) w772 (by decide) (by decide +kernel) (consbad n363 (consbad n394 (nilbad 5)))

def w773 : List Mask := [15,240,4369,17476,36744,61986]
theorem n773 : impossible 6 w773.toFinset :=
  closeState (known := [w260.toFinset, w364.toFinset, w370.toFinset, w395.toFinset, w462.toFinset]) w773 (by decide) (by decide +kernel) (consbad n260 (consbad n364 (consbad n370 (consbad n395 (consbad n462 (nilbad 5))))))

def w774 : List Mask := [15,240,4369,20292,34952,61440,61986]
theorem n774 : impossible 6 w774.toFinset :=
  closeState (known := [w377.toFinset, w388.toFinset, w537.toFinset]) w774 (by decide) (by decide +kernel) (consbad n377 (consbad n388 (consbad n537 (nilbad 5))))

def w775 : List Mask := [15,240,4369,20292,34952,61986]
theorem n775 : impossible 6 w775.toFinset :=
  closeState (known := [w249.toFinset, w373.toFinset, w375.toFinset, w378.toFinset, w379.toFinset, w389.toFinset, w402.toFinset, w463.toFinset, w538.toFinset]) w775 (by decide) (by decide +kernel) (consbad n249 (consbad n373 (consbad n375 (consbad n378 (consbad n379 (consbad n389 (consbad n402 (consbad n463 (consbad n538 (nilbad 5))))))))))

def w776 : List Mask := [15,240,4593,8738,17476,34952,65280]
theorem n776 : impossible 6 w776.toFinset :=
  closeState (known := [w263.toFinset, w399.toFinset, w401.toFinset, w484.toFinset, w583.toFinset]) w776 (by decide) (by decide +kernel) (consbad n263 (consbad n399 (consbad n401 (consbad n484 (consbad n583 (nilbad 5))))))

def w777 : List Mask := [15,240,4593,8738,20292,34952,61440]
theorem n777 : impossible 6 w777.toFinset :=
  closeState (known := [w399.toFinset, w402.toFinset, w498.toFinset]) w777 (by decide) (by decide +kernel) (consbad n399 (consbad n402 (consbad n498 (nilbad 5))))

def w778 : List Mask := [15,240,4593,12066,17476,34952,61440]
theorem n778 : impossible 6 w778.toFinset :=
  closeState (known := [w264.toFinset, w400.toFinset, w401.toFinset, w518.toFinset]) w778 (by decide) (by decide +kernel) (consbad n264 (consbad n400 (consbad n401 (consbad n518 (nilbad 5)))))

def w779 : List Mask := [15,248,3840,4369,8738,17476,61440]
theorem n779 : impossible 6 w779.toFinset :=
  closeState (known := [w403.toFinset, w404.toFinset, w405.toFinset, w406.toFinset, w407.toFinset, w446.toFinset, w584.toFinset]) w779 (by decide) (by decide +kernel) (consbad n403 (consbad n404 (consbad n405 (consbad n406 (consbad n407 (consbad n446 (consbad n584 (nilbad 5))))))))

def w780 : List Mask := [15,256,4369,8738,17476,35064,61440]
theorem n780 : impossible 6 w780.toFinset :=
  closeState (known := [w465.toFinset, w472.toFinset, w475.toFinset, w585.toFinset, w587.toFinset]) w780 (by decide) (by decide +kernel) (consbad n465 (consbad n472 (consbad n475 (consbad n585 (consbad n587 (nilbad 5))))))

def w781 : List Mask := [15,256,4593,8738,17476,34952,61440]
theorem n781 : impossible 6 w781.toFinset :=
  closeState (known := [w408.toFinset, w409.toFinset, w480.toFinset, w492.toFinset, w512.toFinset, w586.toFinset, w588.toFinset]) w781 (by decide) (by decide +kernel) (consbad n408 (consbad n409 (consbad n480 (consbad n492 (consbad n512 (consbad n586 (consbad n588 (nilbad 5))))))))

def w782 : List Mask := [15,3840,4096,4369,8738,17476,35064]
theorem n782 : impossible 6 w782.toFinset :=
  closeState (known := [w412.toFinset, w414.toFinset, w464.toFinset, w589.toFinset, w591.toFinset]) w782 (by decide) (by decide +kernel) (consbad n412 (consbad n414 (consbad n464 (consbad n589 (consbad n591 (nilbad 5))))))

def w783 : List Mask := [15,3840,4096,4593,8738,17476,34952]
theorem n783 : impossible 6 w783.toFinset :=
  closeState (known := [w417.toFinset, w431.toFinset, w451.toFinset, w452.toFinset, w478.toFinset, w590.toFinset, w592.toFinset]) w783 (by decide) (by decide +kernel) (consbad n417 (consbad n431 (consbad n451 (consbad n452 (consbad n478 (consbad n590 (consbad n592 (nilbad 5))))))))

def w784 : List Mask := [15,3840,4369,4593,8738,17476,63624]
theorem n784 : impossible 6 w784.toFinset :=
  closeState (known := [w455.toFinset, w456.toFinset, w459.toFinset]) w784 (by decide) (by decide +kernel) (consbad n455 (consbad n456 (consbad n459 (nilbad 5))))

def w785 : List Mask := [15,3840,4369,4593,8738,34952,62532]
theorem n785 : impossible 6 w785.toFinset :=
  closeState (known := [w408.toFinset, w424.toFinset, w457.toFinset, w458.toFinset, w460.toFinset]) w785 (by decide) (by decide +kernel) (consbad n408 (consbad n424 (consbad n457 (consbad n458 (consbad n460 (nilbad 5))))))

def w786 : List Mask := [15,3840,4369,4593,17476,34952,61986]
theorem n786 : impossible 6 w786.toFinset :=
  closeState (known := [w409.toFinset, w435.toFinset, w461.toFinset, w462.toFinset, w463.toFinset]) w786 (by decide) (by decide +kernel) (consbad n409 (consbad n435 (consbad n461 (consbad n462 (consbad n463 (nilbad 5))))))

def w787 : List Mask := [15,3840,4369,8738,17476,35064,61455]
theorem n787 : impossible 6 w787.toFinset :=
  closeState (known := [w466.toFinset, w593.toFinset, w609.toFinset]) w787 (by decide) (by decide +kernel) (consbad n466 (consbad n593 (consbad n609 (nilbad 5))))

def w788 : List Mask := [15,3840,4369,8738,17476,35064,61986]
theorem n788 : impossible 6 w788.toFinset :=
  closeState (known := [w415.toFinset, w467.toFinset, w476.toFinset, w594.toFinset]) w788 (by decide) (by decide +kernel) (consbad n415 (consbad n467 (consbad n476 (consbad n594 (nilbad 5)))))

def w789 : List Mask := [15,3840,4369,8738,17476,35064,62532]
theorem n789 : impossible 6 w789.toFinset :=
  closeState (known := [w468.toFinset, w473.toFinset, w595.toFinset]) w789 (by decide) (by decide +kernel) (consbad n468 (consbad n473 (consbad n595 (nilbad 5))))

def w790 : List Mask := [15,3840,4369,8738,17476,35064,63624]
theorem n790 : impossible 6 w790.toFinset :=
  closeState (known := [w469.toFinset, w597.toFinset]) w790 (by decide) (by decide +kernel) (consbad n469 (consbad n597 (nilbad 5)))

def w791 : List Mask := [15,3840,4369,8738,17476,35064,65280]
theorem n791 : impossible 6 w791.toFinset :=
  closeState (known := [w598.toFinset]) w791 (by decide) (by decide +kernel) (consbad n598 (nilbad 5))

def w792 : List Mask := [15,3840,4369,8738,17476,39417,61440]
theorem n792 : impossible 6 w792.toFinset :=
  closeState (known := [w470.toFinset, w599.toFinset]) w792 (by decide) (by decide +kernel) (consbad n470 (consbad n599 (nilbad 5)))

def w793 : List Mask := [15,3840,4369,8738,17487,35064,61440]
theorem n793 : impossible 6 w793.toFinset :=
  closeState (known := [w471.toFinset, w593.toFinset, w610.toFinset]) w793 (by decide) (by decide +kernel) (consbad n471 (consbad n593 (consbad n610 (nilbad 5))))

def w794 : List Mask := [15,3840,4369,8738,26214,35064,61440]
theorem n794 : impossible 6 w794.toFinset :=
  closeState (known := [w415.toFinset, w474.toFinset, w477.toFinset]) w794 (by decide) (by decide +kernel) (consbad n415 (consbad n474 (consbad n477 (nilbad 5))))

def w795 : List Mask := [15,3840,4593,8738,17476,34952,61455]
theorem n795 : impossible 6 w795.toFinset :=
  closeState (known := [w419.toFinset, w481.toFinset, w493.toFinset, w513.toFinset, w600.toFinset, w611.toFinset]) w795 (by decide) (by decide +kernel) (consbad n419 (consbad n481 (consbad n493 (consbad n513 (consbad n600 (consbad n611 (nilbad 5)))))))

def w796 : List Mask := [15,3840,4593,8738,17476,34952,61986]
theorem n796 : impossible 6 w796.toFinset :=
  closeState (known := [w420.toFinset, w437.toFinset, w442.toFinset, w482.toFinset, w494.toFinset, w514.toFinset, w601.toFinset]) w796 (by decide) (by decide +kernel) (consbad n420 (consbad n437 (consbad n442 (consbad n482 (consbad n494 (consbad n514 (consbad n601 (nilbad 5))))))))

def w797 : List Mask := [15,3840,4593,8738,17476,34952,62532]
theorem n797 : impossible 6 w797.toFinset :=
  closeState (known := [w483.toFinset, w495.toFinset, w515.toFinset, w602.toFinset]) w797 (by decide) (by decide +kernel) (consbad n483 (consbad n495 (consbad n515 (consbad n602 (nilbad 5)))))

def w798 : List Mask := [15,3840,4593,8738,17476,34952,65280]
theorem n798 : impossible 6 w798.toFinset :=
  closeState (known := [w421.toFinset, w432.toFinset, w485.toFinset, w496.toFinset, w516.toFinset, w604.toFinset]) w798 (by decide) (by decide +kernel) (consbad n421 (consbad n432 (consbad n485 (consbad n496 (consbad n516 (consbad n604 (nilbad 5)))))))

def w799 : List Mask := [15,3840,4593,8738,17476,35064,61440]
theorem n799 : impossible 6 w799.toFinset :=
  closeState (known := [w422.toFinset, w433.toFinset, w484.toFinset, w498.toFinset, w518.toFinset, w605.toFinset]) w799 (by decide) (by decide +kernel) (consbad n422 (consbad n433 (consbad n484 (consbad n498 (consbad n518 (consbad n605 (nilbad 5)))))))

def w800 : List Mask := [15,3840,4593,8738,17476,36744,61440]
theorem n800 : impossible 6 w800.toFinset :=
  closeState (known := [w423.toFinset, w434.toFinset, w485.toFinset, w499.toFinset, w519.toFinset]) w800 (by decide) (by decide +kernel) (consbad n423 (consbad n434 (consbad n485 (consbad n499 (consbad n519 (nilbad 5))))))

def w801 : List Mask := [15,3840,4593,8738,17476,39321,61440]
theorem n801 : impossible 6 w801.toFinset :=
  closeState (known := [w424.toFinset, w435.toFinset, w486.toFinset, w500.toFinset, w520.toFinset, w606.toFinset]) w801 (by decide) (by decide +kernel) (consbad n424 (consbad n435 (consbad n486 (consbad n500 (consbad n520 (consbad n606 (nilbad 5)))))))

def w802 : List Mask := [15,3840,4593,8738,17476,39417,61440]
theorem n802 : impossible 6 w802.toFinset :=
  closeState (known := [w425.toFinset, w436.toFinset, w487.toFinset, w501.toFinset, w521.toFinset, w607.toFinset]) w802 (by decide) (by decide +kernel) (consbad n425 (consbad n436 (consbad n487 (consbad n501 (consbad n521 (consbad n607 (nilbad 5)))))))

def w803 : List Mask := [15,3840,4593,8738,17476,43690,61440]
theorem n803 : impossible 6 w803.toFinset :=
  closeState (known := [w426.toFinset, w437.toFinset, w443.toFinset, w488.toFinset, w502.toFinset, w522.toFinset, w608.toFinset]) w803 (by decide) (by decide +kernel) (consbad n426 (consbad n437 (consbad n443 (consbad n488 (consbad n502 (consbad n522 (consbad n608 (nilbad 5))))))))

def w804 : List Mask := [15,3840,4593,8738,17476,61440,63624]
theorem n804 : impossible 6 w804.toFinset :=
  closeState (known := [w427.toFinset, w438.toFinset, w489.toFinset, w503.toFinset, w524.toFinset]) w804 (by decide) (by decide +kernel) (consbad n427 (consbad n438 (consbad n489 (consbad n503 (consbad n524 (nilbad 5))))))

def w805 : List Mask := [15,3840,4593,8738,17487,34952,61440]
theorem n805 : impossible 6 w805.toFinset :=
  closeState (known := [w256.toFinset, w419.toFinset, w440.toFinset, w491.toFinset, w504.toFinset, w525.toFinset, w600.toFinset, w612.toFinset]) w805 (by decide) (by decide +kernel) (consbad n256 (consbad n419 (consbad n440 (consbad n491 (consbad n504 (consbad n525 (consbad n600 (consbad n612 (nilbad 5)))))))))

def w806 : List Mask := [15,3840,4593,8738,20292,34952,61440]
theorem n806 : impossible 6 w806.toFinset :=
  closeState (known := [w421.toFinset, w441.toFinset, w496.toFinset, w499.toFinset, w526.toFinset]) w806 (by decide) (by decide +kernel) (consbad n421 (consbad n441 (consbad n496 (consbad n499 (consbad n526 (nilbad 5))))))

def w807 : List Mask := [15,3840,4593,8738,26214,34952,61440]
theorem n807 : impossible 6 w807.toFinset :=
  closeState (known := [w420.toFinset, w442.toFinset, w443.toFinset, w505.toFinset, w506.toFinset, w527.toFinset]) w807 (by decide) (by decide +kernel) (consbad n420 (consbad n442 (consbad n443 (consbad n505 (consbad n506 (consbad n527 (nilbad 5)))))))

def w808 : List Mask := [15,3840,4593,8738,34952,61440,62532]
theorem n808 : impossible 6 w808.toFinset :=
  closeState (known := [w427.toFinset, w444.toFinset, w507.toFinset, w508.toFinset, w529.toFinset]) w808 (by decide) (by decide +kernel) (consbad n427 (consbad n444 (consbad n507 (consbad n508 (consbad n529 (nilbad 5))))))

def w809 : List Mask := [15,3840,4593,8738,34952,62532]
theorem n809 : impossible 6 w809.toFinset :=
  closeState (known := [w250.toFinset, w408.toFinset, w411.toFinset, w419.toFinset, w420.toFinset, w421.toFinset, w423.toFinset, w425.toFinset, w426.toFinset, w430.toFinset, w448.toFinset, w479.toFinset, w509.toFinset, w511.toFinset, w530.toFinset]) w809 (by decide) (by decide +kernel) (consbad n250 (consbad n408 (consbad n411 (consbad n419 (consbad n420 (consbad n421 (consbad n423 (consbad n425 (consbad n426 (consbad n430 (consbad n448 (consbad n479 (consbad n509 (consbad n511 (consbad n530 (nilbad 5))))))))))))))))

def w810 : List Mask := [15,3840,4593,12066,17476,34952,61440]
theorem n810 : impossible 6 w810.toFinset :=
  closeState (known := [w430.toFinset, w432.toFinset, w516.toFinset, w519.toFinset, w526.toFinset]) w810 (by decide) (by decide +kernel) (consbad n430 (consbad n432 (consbad n516 (consbad n519 (consbad n526 (nilbad 5))))))

def w811 : List Mask := [15,3840,4593,17476,34952,61440,61986]
theorem n811 : impossible 6 w811.toFinset :=
  closeState (known := [w438.toFinset, w444.toFinset, w532.toFinset, w533.toFinset, w537.toFinset]) w811 (by decide) (by decide +kernel) (consbad n438 (consbad n444 (consbad n532 (consbad n533 (consbad n537 (nilbad 5))))))

def w812 : List Mask := [15,3840,4593,17476,34952,61986]
theorem n812 : impossible 6 w812.toFinset :=
  closeState (known := [w251.toFinset, w261.toFinset, w409.toFinset, w432.toFinset, w434.toFinset, w436.toFinset, w439.toFinset, w440.toFinset, w441.toFinset, w445.toFinset, w449.toFinset, w531.toFinset, w534.toFinset, w536.toFinset, w538.toFinset]) w812 (by decide) (by decide +kernel) (consbad n251 (consbad n261 (consbad n409 (consbad n432 (consbad n434 (consbad n436 (consbad n439 (consbad n440 (consbad n441 (consbad n445 (consbad n449 (consbad n531 (consbad n534 (consbad n536 (consbad n538 (nilbad 5))))))))))))))))

def w813 : List Mask := [15,3855,4369,8738,17476,35064,61440]
theorem n813 : impossible 6 w813.toFinset :=
  closeState (known := [w466.toFinset, w609.toFinset, w610.toFinset]) w813 (by decide) (by decide +kernel) (consbad n466 (consbad n609 (consbad n610 (nilbad 5))))

def w814 : List Mask := [15,3855,4593,8738,17476,34952,61440]
theorem n814 : impossible 6 w814.toFinset :=
  closeState (known := [w448.toFinset, w449.toFinset, w481.toFinset, w504.toFinset, w611.toFinset, w612.toFinset]) w814 (by decide) (by decide +kernel) (consbad n448 (consbad n449 (consbad n481 (consbad n504 (consbad n611 (consbad n612 (nilbad 5)))))))

def w815 : List Mask := [15,4369,4593,8738,17476,34952,65280]
theorem n815 : impossible 6 w815.toFinset :=
  closeState (known := [w454.toFinset, w455.toFinset, w457.toFinset, w461.toFinset, w470.toFinset, w486.toFinset, w613.toFinset]) w815 (by decide) (by decide +kernel) (consbad n454 (consbad n455 (consbad n457 (consbad n461 (consbad n470 (consbad n486 (consbad n613 (nilbad 5))))))))

def w816 : List Mask := [15,4369,4593,8738,17476,36744,61440]
theorem n816 : impossible 6 w816.toFinset :=
  closeState (known := [w455.toFinset, w458.toFinset, w462.toFinset]) w816 (by decide) (by decide +kernel) (consbad n455 (consbad n458 (consbad n462 (nilbad 5))))

def w817 : List Mask := [15,4369,4593,8738,20292,34952,61440]
theorem n817 : impossible 6 w817.toFinset :=
  closeState (known := [w451.toFinset, w456.toFinset, w457.toFinset, w463.toFinset, w500.toFinset]) w817 (by decide) (by decide +kernel) (consbad n451 (consbad n456 (consbad n457 (consbad n463 (consbad n500 (nilbad 5))))))

def w818 : List Mask := [15,4369,4593,12066,17476,34952,61440]
theorem n818 : impossible 6 w818.toFinset :=
  closeState (known := [w452.toFinset, w459.toFinset, w460.toFinset, w461.toFinset, w520.toFinset]) w818 (by decide) (by decide +kernel) (consbad n452 (consbad n459 (consbad n460 (consbad n461 (consbad n520 (nilbad 5))))))

def w819 : List Mask := [15,4369,8738,12066,17476,35064,61440]
theorem n819 : impossible 6 w819.toFinset :=
  closeState (known := [w467.toFinset, w476.toFinset, w477.toFinset, w614.toFinset]) w819 (by decide) (by decide +kernel) (consbad n467 (consbad n476 (consbad n477 (consbad n614 (nilbad 5)))))

def w820 : List Mask := [15,4369,8738,17476,20292,35064,61440]
theorem n820 : impossible 6 w820.toFinset :=
  closeState (known := [w468.toFinset, w473.toFinset, w616.toFinset]) w820 (by decide) (by decide +kernel) (consbad n468 (consbad n473 (consbad n616 (nilbad 5))))

def w821 : List Mask := [15,4369,8738,17476,34952,35064,65280]
theorem n821 : impossible 6 w821.toFinset :=
  closeState (known := [w469.toFinset, w618.toFinset]) w821 (by decide) (by decide +kernel) (consbad n469 (consbad n618 (nilbad 5)))

def w822 : List Mask := [15,4369,8738,17476,35064,36744,61440]
theorem n822 : impossible 6 w822.toFinset :=
  closeState (known := [w469.toFinset, w619.toFinset]) w822 (by decide) (by decide +kernel) (consbad n469 (consbad n619 (nilbad 5)))

def w823 : List Mask := [15,4369,8738,17476,35064,61440,65280]
theorem n823 : impossible 6 w823.toFinset :=
  closeState (known := [w620.toFinset]) w823 (by decide) (by decide +kernel) (consbad n620 (nilbad 5))

def w824 : List Mask := [15,4369,8738,17476,35064,65280]
theorem n824 : impossible 6 w824.toFinset :=
  closeState (known := [w262.toFinset, w453.toFinset, w466.toFinset, w467.toFinset, w468.toFinset, w470.toFinset, w471.toFinset, w474.toFinset, w615.toFinset, w621.toFinset]) w824 (by decide) (by decide +kernel) (consbad n262 (consbad n453 (consbad n466 (consbad n467 (consbad n468 (consbad n470 (consbad n471 (consbad n474 (consbad n615 (consbad n621 (nilbad 5)))))))))))

def w825 : List Mask := [15,4593,8738,12066,17476,34952,61440]
theorem n825 : impossible 6 w825.toFinset :=
  closeState (known := [w479.toFinset, w482.toFinset, w506.toFinset, w514.toFinset, w522.toFinset, w527.toFinset, w622.toFinset]) w825 (by decide) (by decide +kernel) (consbad n479 (consbad n482 (consbad n506 (consbad n514 (consbad n522 (consbad n527 (consbad n622 (nilbad 5))))))))

def w826 : List Mask := [15,4593,8738,17476,20292,34952,61440]
theorem n826 : impossible 6 w826.toFinset :=
  closeState (known := [w483.toFinset, w495.toFinset, w531.toFinset, w624.toFinset]) w826 (by decide) (by decide +kernel) (consbad n483 (consbad n495 (consbad n531 (consbad n624 (nilbad 5)))))

def w827 : List Mask := [15,4593,8738,17476,34952,61440,65280]
theorem n827 : impossible 6 w827.toFinset :=
  closeState (known := [w489.toFinset, w507.toFinset, w508.toFinset, w532.toFinset, w533.toFinset, w626.toFinset]) w827 (by decide) (by decide +kernel) (consbad n489 (consbad n507 (consbad n508 (consbad n532 (consbad n533 (consbad n626 (nilbad 5)))))))

def w828 : List Mask := [15,4593,8738,17476,34952,65280]
theorem n828 : impossible 6 w828.toFinset :=
  closeState (known := [w252.toFinset, w263.toFinset, w454.toFinset, w481.toFinset, w482.toFinset, w483.toFinset, w487.toFinset, w488.toFinset, w490.toFinset, w491.toFinset, w505.toFinset, w510.toFinset, w511.toFinset, w535.toFinset, w536.toFinset, w623.toFinset, w627.toFinset]) w828 (by decide) (by decide +kernel) (consbad n252 (consbad n263 (consbad n454 (consbad n481 (consbad n482 (consbad n483 (consbad n487 (consbad n488 (consbad n490 (consbad n491 (consbad n505 (consbad n510 (consbad n511 (consbad n535 (consbad n536 (consbad n623 (consbad n627 (nilbad 5))))))))))))))))))

def w829 : List Mask := [15,4593,8738,20292,34952,61440]
theorem n829 : impossible 6 w829.toFinset :=
  closeState (known := [w253.toFinset, w410.toFinset, w451.toFinset, w493.toFinset, w494.toFinset, w497.toFinset, w501.toFinset, w502.toFinset, w503.toFinset, w504.toFinset, w506.toFinset, w507.toFinset, w511.toFinset, w537.toFinset, w538.toFinset]) w829 (by decide) (by decide +kernel) (consbad n253 (consbad n410 (consbad n451 (consbad n493 (consbad n494 (consbad n497 (consbad n501 (consbad n502 (consbad n503 (consbad n504 (consbad n506 (consbad n507 (consbad n511 (consbad n537 (consbad n538 (nilbad 5))))))))))))))))

def w830 : List Mask := [15,4593,12066,17476,34952,61440]
theorem n830 : impossible 6 w830.toFinset :=
  closeState (known := [w254.toFinset, w264.toFinset, w452.toFinset, w513.toFinset, w515.toFinset, w517.toFinset, w521.toFinset, w523.toFinset, w524.toFinset, w525.toFinset, w528.toFinset, w529.toFinset, w530.toFinset, w532.toFinset, w536.toFinset]) w830 (by decide) (by decide +kernel) (consbad n254 (consbad n264 (consbad n452 (consbad n513 (consbad n515 (consbad n517 (consbad n521 (consbad n523 (consbad n524 (consbad n525 (consbad n528 (consbad n529 (consbad n530 (consbad n532 (consbad n536 (nilbad 5))))))))))))))))

def w831 : List Mask := [79,240,3840,4369,8738,34952,61440]
theorem n831 : impossible 6 w831.toFinset :=
  closeState (known := [w539.toFinset, w540.toFinset, w541.toFinset, w542.toFinset, w543.toFinset, w544.toFinset, w545.toFinset]) w831 (by decide) (by decide +kernel) (consbad n539 (consbad n540 (consbad n541 (consbad n542 (consbad n543 (consbad n544 (consbad n545 (nilbad 5))))))))

def w832 : List Mask := [240,256,4369,8738,17487,34952,61440]
theorem n832 : impossible 6 w832.toFinset :=
  closeState (known := [w564.toFinset, w571.toFinset, w576.toFinset, w579.toFinset, w585.toFinset, w586.toFinset]) w832 (by decide) (by decide +kernel) (consbad n564 (consbad n571 (consbad n576 (consbad n579 (consbad n585 (consbad n586 (nilbad 5)))))))

def w833 : List Mask := [240,271,4369,8738,17476,34952,61440]
theorem n833 : impossible 6 w833.toFinset :=
  closeState (known := [w546.toFinset, w547.toFinset, w548.toFinset, w576.toFinset, w587.toFinset, w588.toFinset]) w833 (by decide) (by decide +kernel) (consbad n546 (consbad n547 (consbad n548 (consbad n576 (consbad n587 (consbad n588 (nilbad 5)))))))

def w834 : List Mask := [240,3840,4096,4369,8738,17487,34952]
theorem n834 : impossible 6 w834.toFinset :=
  closeState (known := [w549.toFinset, w550.toFinset, w552.toFinset, w563.toFinset, w589.toFinset, w590.toFinset]) w834 (by decide) (by decide +kernel) (consbad n549 (consbad n550 (consbad n552 (consbad n563 (consbad n589 (consbad n590 (nilbad 5)))))))

def w835 : List Mask := [240,3840,4111,4369,8738,17476,34952]
theorem n835 : impossible 6 w835.toFinset :=
  closeState (known := [w550.toFinset, w558.toFinset, w559.toFinset, w560.toFinset, w591.toFinset, w592.toFinset]) w835 (by decide) (by decide +kernel) (consbad n550 (consbad n558 (consbad n559 (consbad n560 (consbad n591 (consbad n592 (nilbad 5)))))))

def w836 : List Mask := [240,3840,4369,8738,17487,34952,61455]
theorem n836 : impossible 6 w836.toFinset :=
  closeState (known := [w565.toFinset, w572.toFinset, w577.toFinset, w580.toFinset, w593.toFinset, w600.toFinset]) w836 (by decide) (by decide +kernel) (consbad n565 (consbad n572 (consbad n577 (consbad n580 (consbad n593 (consbad n600 (nilbad 5)))))))

def w837 : List Mask := [240,3840,4369,8738,17487,34952,61986]
theorem n837 : impossible 6 w837.toFinset :=
  closeState (known := [w553.toFinset, w566.toFinset, w581.toFinset, w594.toFinset, w601.toFinset]) w837 (by decide) (by decide +kernel) (consbad n553 (consbad n566 (consbad n581 (consbad n594 (consbad n601 (nilbad 5))))))

def w838 : List Mask := [240,3840,4369,8738,17487,34952,62532]
theorem n838 : impossible 6 w838.toFinset :=
  closeState (known := [w567.toFinset, w595.toFinset, w602.toFinset]) w838 (by decide) (by decide +kernel) (consbad n567 (consbad n595 (consbad n602 (nilbad 5))))

def w839 : List Mask := [240,3840,4369,8738,17487,34952,62543]
theorem n839 : impossible 6 w839.toFinset :=
  closeState (known := [w568.toFinset, w578.toFinset, w596.toFinset, w603.toFinset]) w839 (by decide) (by decide +kernel) (consbad n568 (consbad n578 (consbad n596 (consbad n603 (nilbad 5)))))

def w840 : List Mask := [240,3840,4369,8738,17487,34952,63624]
theorem n840 : impossible 6 w840.toFinset :=
  closeState (known := [w569.toFinset, w573.toFinset, w597.toFinset]) w840 (by decide) (by decide +kernel) (consbad n569 (consbad n573 (consbad n597 (nilbad 5))))

def w841 : List Mask := [240,3840,4369,8738,17487,34952,65280]
theorem n841 : impossible 6 w841.toFinset :=
  closeState (known := [w598.toFinset, w604.toFinset]) w841 (by decide) (by decide +kernel) (consbad n598 (consbad n604 (nilbad 5)))

def w842 : List Mask := [240,3840,4369,8738,17487,35064,61440]
theorem n842 : impossible 6 w842.toFinset :=
  closeState (known := [w570.toFinset, w605.toFinset]) w842 (by decide) (by decide +kernel) (consbad n570 (consbad n605 (nilbad 5)))

def w843 : List Mask := [240,3840,4369,8738,17487,39321,61440]
theorem n843 : impossible 6 w843.toFinset :=
  closeState (known := [w574.toFinset, w599.toFinset, w606.toFinset]) w843 (by decide) (by decide +kernel) (consbad n574 (consbad n599 (consbad n606 (nilbad 5))))

def w844 : List Mask := [240,3840,4369,8738,17487,43690,61440]
theorem n844 : impossible 6 w844.toFinset :=
  closeState (known := [w553.toFinset, w575.toFinset, w582.toFinset, w608.toFinset]) w844 (by decide) (by decide +kernel) (consbad n553 (consbad n575 (consbad n582 (consbad n608 (nilbad 5)))))

def w845 : List Mask := [240,3840,4593,8738,17487,34952,61440]
theorem n845 : impossible 6 w845.toFinset :=
  closeState (known := [w583.toFinset, w605.toFinset]) w845 (by decide) (by decide +kernel) (consbad n583 (consbad n605 (nilbad 5)))

def w846 : List Mask := [240,3855,4369,8738,17476,34952,61455]
theorem n846 : impossible 6 w846.toFinset :=
  closeState (known := [w556.toFinset, w577.toFinset, w609.toFinset, w611.toFinset]) w846 (by decide) (by decide +kernel) (consbad n556 (consbad n577 (consbad n609 (consbad n611 (nilbad 5)))))

def w847 : List Mask := [240,3855,4369,8738,17487,34952,61440]
theorem n847 : impossible 6 w847.toFinset :=
  closeState (known := [w555.toFinset, w556.toFinset, w557.toFinset, w565.toFinset, w610.toFinset, w612.toFinset]) w847 (by decide) (by decide +kernel) (consbad n555 (consbad n556 (consbad n557 (consbad n565 (consbad n610 (consbad n612 (nilbad 5)))))))

def w848 : List Mask := [240,4369,8738,12066,17487,34952,61440]
theorem n848 : impossible 6 w848.toFinset :=
  closeState (known := [w566.toFinset, w581.toFinset, w582.toFinset, w614.toFinset, w622.toFinset]) w848 (by decide) (by decide +kernel) (consbad n566 (consbad n581 (consbad n582 (consbad n614 (consbad n622 (nilbad 5))))))

def w849 : List Mask := [240,4369,8738,17476,17487,34952,65280]
theorem n849 : impossible 6 w849.toFinset :=
  closeState (known := [w567.toFinset, w615.toFinset, w623.toFinset]) w849 (by decide) (by decide +kernel) (consbad n567 (consbad n615 (consbad n623 (nilbad 5))))

def w850 : List Mask := [240,4369,8738,17487,20292,34952,61440]
theorem n850 : impossible 6 w850.toFinset :=
  closeState (known := [w567.toFinset, w616.toFinset, w624.toFinset]) w850 (by decide) (by decide +kernel) (consbad n567 (consbad n616 (consbad n624 (nilbad 5))))

def w851 : List Mask := [240,4369,8738,17487,20303,34952,61440]
theorem n851 : impossible 6 w851.toFinset :=
  closeState (known := [w568.toFinset, w578.toFinset, w617.toFinset, w625.toFinset]) w851 (by decide) (by decide +kernel) (consbad n568 (consbad n578 (consbad n617 (consbad n625 (nilbad 5)))))

def w852 : List Mask := [240,4369,8738,17487,34952,36744,61440]
theorem n852 : impossible 6 w852.toFinset :=
  closeState (known := [w569.toFinset, w573.toFinset, w619.toFinset]) w852 (by decide) (by decide +kernel) (consbad n569 (consbad n573 (consbad n619 (nilbad 5))))

def w853 : List Mask := [240,4369,8738,17487,34952,61440,65280]
theorem n853 : impossible 6 w853.toFinset :=
  closeState (known := [w620.toFinset, w626.toFinset]) w853 (by decide) (by decide +kernel) (consbad n620 (consbad n626 (nilbad 5)))

def w854 : List Mask := [240,4369,8738,17487,34952,65280]
theorem n854 : impossible 6 w854.toFinset :=
  closeState (known := [w255.toFinset, w561.toFinset, w566.toFinset, w568.toFinset, w569.toFinset, w570.toFinset, w574.toFinset, w575.toFinset, w583.toFinset, w613.toFinset, w618.toFinset, w621.toFinset, w627.toFinset]) w854 (by decide) (by decide +kernel) (consbad n255 (consbad n561 (consbad n566 (consbad n568 (consbad n569 (consbad n570 (consbad n574 (consbad n575 (consbad n583 (consbad n613 (consbad n618 (consbad n621 (consbad n627 (nilbad 5))))))))))))))

def w855 : List Mask := [3840,4369,4593,8738,17487,34952,61440]
theorem n855 : impossible 6 w855.toFinset :=
  closeState (known := [w586.toFinset, w590.toFinset, w599.toFinset, w606.toFinset, w613.toFinset]) w855 (by decide) (by decide +kernel) (consbad n586 (consbad n590 (consbad n599 (consbad n606 (consbad n613 (nilbad 5))))))

def w856 : List Mask := [3840,4369,8738,17476,17487,35064,61440]
theorem n856 : impossible 6 w856.toFinset :=
  closeState (known := [w595.toFinset, w615.toFinset, w616.toFinset]) w856 (by decide) (by decide +kernel) (consbad n595 (consbad n615 (consbad n616 (nilbad 5))))

def w857 : List Mask := [3840,4369,8738,17487,34952,35064,61440]
theorem n857 : impossible 6 w857.toFinset :=
  closeState (known := [w597.toFinset, w618.toFinset, w619.toFinset]) w857 (by decide) (by decide +kernel) (consbad n597 (consbad n618 (consbad n619 (nilbad 5))))

def w858 : List Mask := [3840,4369,8738,17487,35064,61440]
theorem n858 : impossible 6 w858.toFinset :=
  closeState (known := [w585.toFinset, w589.toFinset, w594.toFinset, w596.toFinset, w598.toFinset, w599.toFinset, w614.toFinset, w617.toFinset, w620.toFinset, w621.toFinset]) w858 (by decide) (by decide +kernel) (consbad n585 (consbad n589 (consbad n594 (consbad n596 (consbad n598 (consbad n599 (consbad n614 (consbad n617 (consbad n620 (consbad n621 (nilbad 5)))))))))))

def w859 : List Mask := [3840,4593,8738,17476,17487,34952,61440]
theorem n859 : impossible 6 w859.toFinset :=
  closeState (known := [w602.toFinset, w623.toFinset, w624.toFinset]) w859 (by decide) (by decide +kernel) (consbad n602 (consbad n623 (consbad n624 (nilbad 5))))

def w860 : List Mask := [3840,4593,8738,17487,34952,61440]
theorem n860 : impossible 6 w860.toFinset :=
  closeState (known := [w256.toFinset, w586.toFinset, w590.toFinset, w601.toFinset, w603.toFinset, w604.toFinset, w607.toFinset, w608.toFinset, w622.toFinset, w625.toFinset, w626.toFinset, w627.toFinset]) w860 (by decide) (by decide +kernel) (consbad n256 (consbad n586 (consbad n590 (consbad n601 (consbad n603 (consbad n604 (consbad n607 (consbad n608 (consbad n622 (consbad n625 (consbad n626 (consbad n627 (nilbad 5)))))))))))))

def w861 : List Mask := [8,15,240,3840,4369,8738,17476,61440]
theorem n861 : impossible 7 w861.toFinset :=
  closeState (known := [w628.toFinset, w629.toFinset, w630.toFinset, w631.toFinset, w632.toFinset, w633.toFinset, w634.toFinset, w647.toFinset, w663.toFinset, w681.toFinset, w684.toFinset, w779.toFinset]) w861 (by decide) (by decide +kernel) (consbad n628 (consbad n629 (consbad n630 (consbad n631 (consbad n632 (consbad n633 (consbad n634 (consbad n647 (consbad n663 (consbad n681 (consbad n684 (consbad n779 (nilbad 6)))))))))))))

def w862 : List Mask := [15,64,240,3840,4369,8738,34952,61440]
theorem n862 : impossible 7 w862.toFinset :=
  closeState (known := [w635.toFinset, w636.toFinset, w637.toFinset, w638.toFinset, w639.toFinset, w640.toFinset, w641.toFinset, w654.toFinset, w664.toFinset, w688.toFinset, w831.toFinset]) w862 (by decide) (by decide +kernel) (consbad n635 (consbad n636 (consbad n637 (consbad n638 (consbad n639 (consbad n640 (consbad n641 (consbad n654 (consbad n664 (consbad n688 (consbad n831 (nilbad 6))))))))))))

def w863 : List Mask := [15,240,256,4369,8738,17476,34952,61440]
theorem n863 : impossible 7 w863.toFinset :=
  closeState (known := [w643.toFinset, w644.toFinset, w645.toFinset, w697.toFinset, w703.toFinset, w720.toFinset, w745.toFinset, w780.toFinset, w781.toFinset, w832.toFinset, w833.toFinset]) w863 (by decide) (by decide +kernel) (consbad n643 (consbad n644 (consbad n645 (consbad n697 (consbad n703 (consbad n720 (consbad n745 (consbad n780 (consbad n781 (consbad n832 (consbad n833 (nilbad 6))))))))))))

def w864 : List Mask := [15,240,3840,4096,4369,8738,17476,34952]
theorem n864 : impossible 7 w864.toFinset :=
  closeState (known := [w646.toFinset, w652.toFinset, w667.toFinset, w689.toFinset, w690.toFinset, w691.toFinset, w693.toFinset, w782.toFinset, w783.toFinset, w834.toFinset, w835.toFinset]) w864 (by decide) (by decide +kernel) (consbad n646 (consbad n652 (consbad n667 (consbad n689 (consbad n690 (consbad n691 (consbad n693 (consbad n782 (consbad n783 (consbad n834 (consbad n835 (nilbad 6))))))))))))

def w865 : List Mask := [15,240,3840,4369,8738,17476,34952,61455]
theorem n865 : impossible 7 w865.toFinset :=
  closeState (known := [w655.toFinset, w698.toFinset, w704.toFinset, w721.toFinset, w746.toFinset, w787.toFinset, w795.toFinset, w836.toFinset, w846.toFinset]) w865 (by decide) (by decide +kernel) (consbad n655 (consbad n698 (consbad n704 (consbad n721 (consbad n746 (consbad n787 (consbad n795 (consbad n836 (consbad n846 (nilbad 6))))))))))

def w866 : List Mask := [15,240,3840,4369,8738,17476,34952,61986]
theorem n866 : impossible 7 w866.toFinset :=
  closeState (known := [w648.toFinset, w656.toFinset, w672.toFinset, w677.toFinset, w699.toFinset, w705.toFinset, w722.toFinset, w747.toFinset, w788.toFinset, w796.toFinset, w837.toFinset]) w866 (by decide) (by decide +kernel) (consbad n648 (consbad n656 (consbad n672 (consbad n677 (consbad n699 (consbad n705 (consbad n722 (consbad n747 (consbad n788 (consbad n796 (consbad n837 (nilbad 6))))))))))))

def w867 : List Mask := [15,240,3840,4369,8738,17476,34952,62532]
theorem n867 : impossible 7 w867.toFinset :=
  closeState (known := [w700.toFinset, w706.toFinset, w723.toFinset, w748.toFinset, w789.toFinset, w797.toFinset, w838.toFinset]) w867 (by decide) (by decide +kernel) (consbad n700 (consbad n706 (consbad n723 (consbad n748 (consbad n789 (consbad n797 (consbad n838 (nilbad 6))))))))

def w868 : List Mask := [15,240,3840,4369,8738,17476,34952,63624]
theorem n868 : impossible 7 w868.toFinset :=
  closeState (known := [w701.toFinset, w707.toFinset, w724.toFinset, w749.toFinset, w790.toFinset, w840.toFinset]) w868 (by decide) (by decide +kernel) (consbad n701 (consbad n707 (consbad n724 (consbad n749 (consbad n790 (consbad n840 (nilbad 6)))))))

def w869 : List Mask := [15,240,3840,4369,8738,17476,34952,65280]
theorem n869 : impossible 7 w869.toFinset :=
  closeState (known := [w649.toFinset, w657.toFinset, w668.toFinset, w708.toFinset, w725.toFinset, w750.toFinset, w791.toFinset, w798.toFinset, w841.toFinset]) w869 (by decide) (by decide +kernel) (consbad n649 (consbad n657 (consbad n668 (consbad n708 (consbad n725 (consbad n750 (consbad n791 (consbad n798 (consbad n841 (nilbad 6))))))))))

def w870 : List Mask := [15,240,3840,4369,8738,17476,35064,61440]
theorem n870 : impossible 7 w870.toFinset :=
  closeState (known := [w640.toFinset, w658.toFinset, w669.toFinset, w702.toFinset, w727.toFinset, w752.toFinset, w799.toFinset, w842.toFinset]) w870 (by decide) (by decide +kernel) (consbad n640 (consbad n658 (consbad n669 (consbad n702 (consbad n727 (consbad n752 (consbad n799 (consbad n842 (nilbad 6)))))))))

def w871 : List Mask := [15,240,3840,4369,8738,17476,36744,61440]
theorem n871 : impossible 7 w871.toFinset :=
  closeState (known := [w649.toFinset, w659.toFinset, w670.toFinset, w708.toFinset, w728.toFinset, w753.toFinset, w800.toFinset]) w871 (by decide) (by decide +kernel) (consbad n649 (consbad n659 (consbad n670 (consbad n708 (consbad n728 (consbad n753 (consbad n800 (nilbad 6))))))))

def w872 : List Mask := [15,240,3840,4369,8738,17476,39321,61440]
theorem n872 : impossible 7 w872.toFinset :=
  closeState (known := [w660.toFinset, w671.toFinset, w710.toFinset, w729.toFinset, w754.toFinset, w792.toFinset, w801.toFinset, w843.toFinset]) w872 (by decide) (by decide +kernel) (consbad n660 (consbad n671 (consbad n710 (consbad n729 (consbad n754 (consbad n792 (consbad n801 (consbad n843 (nilbad 6)))))))))

def w873 : List Mask := [15,240,3840,4369,8738,17476,43690,61440]
theorem n873 : impossible 7 w873.toFinset :=
  closeState (known := [w648.toFinset, w661.toFinset, w672.toFinset, w678.toFinset, w711.toFinset, w712.toFinset, w730.toFinset, w755.toFinset, w803.toFinset, w844.toFinset]) w873 (by decide) (by decide +kernel) (consbad n648 (consbad n661 (consbad n672 (consbad n678 (consbad n711 (consbad n712 (consbad n730 (consbad n755 (consbad n803 (consbad n844 (nilbad 6)))))))))))

def w874 : List Mask := [15,240,3840,4369,8738,17476,61440,63624]
theorem n874 : impossible 7 w874.toFinset :=
  closeState (known := [w662.toFinset, w673.toFinset, w713.toFinset, w714.toFinset, w731.toFinset, w757.toFinset, w804.toFinset]) w874 (by decide) (by decide +kernel) (consbad n662 (consbad n673 (consbad n713 (consbad n714 (consbad n731 (consbad n757 (consbad n804 (nilbad 6))))))))

def w875 : List Mask := [15,240,3840,4369,8738,17476,63624]
theorem n875 : impossible 7 w875.toFinset :=
  closeState (known := [w635.toFinset, w643.toFinset, w648.toFinset, w649.toFinset, w650.toFinset, w651.toFinset, w653.toFinset, w665.toFinset, w685.toFinset, w694.toFinset, w696.toFinset, w715.toFinset, w717.toFinset, w732.toFinset, w758.toFinset, w784.toFinset]) w875 (by decide) (by decide +kernel) (consbad n635 (consbad n643 (consbad n648 (consbad n649 (consbad n650 (consbad n651 (consbad n653 (consbad n665 (consbad n685 (consbad n694 (consbad n696 (consbad n715 (consbad n717 (consbad n732 (consbad n758 (consbad n784 (nilbad 6)))))))))))))))))

def w876 : List Mask := [15,240,3840,4369,8738,17487,34952,61440]
theorem n876 : impossible 7 w876.toFinset :=
  closeState (known := [w634.toFinset, w650.toFinset, w655.toFinset, w675.toFinset, w718.toFinset, w719.toFinset, w733.toFinset, w759.toFinset, w793.toFinset, w805.toFinset, w836.toFinset, w847.toFinset]) w876 (by decide) (by decide +kernel) (consbad n634 (consbad n650 (consbad n655 (consbad n675 (consbad n718 (consbad n719 (consbad n733 (consbad n759 (consbad n793 (consbad n805 (consbad n836 (consbad n847 (nilbad 6)))))))))))))

def w877 : List Mask := [15,240,3840,4369,8738,20292,34952,61440]
theorem n877 : impossible 7 w877.toFinset :=
  closeState (known := [w651.toFinset, w657.toFinset, w676.toFinset, w725.toFinset, w728.toFinset, w760.toFinset, w806.toFinset]) w877 (by decide) (by decide +kernel) (consbad n651 (consbad n657 (consbad n676 (consbad n725 (consbad n728 (consbad n760 (consbad n806 (nilbad 6))))))))

def w878 : List Mask := [15,240,3840,4369,8738,26214,34952,61440]
theorem n878 : impossible 7 w878.toFinset :=
  closeState (known := [w642.toFinset, w653.toFinset, w656.toFinset, w677.toFinset, w678.toFinset, w734.toFinset, w735.toFinset, w736.toFinset, w761.toFinset, w794.toFinset, w807.toFinset]) w878 (by decide) (by decide +kernel) (consbad n642 (consbad n653 (consbad n656 (consbad n677 (consbad n678 (consbad n734 (consbad n735 (consbad n736 (consbad n761 (consbad n794 (consbad n807 (nilbad 6))))))))))))

def w879 : List Mask := [15,240,3840,4369,8738,34952,61440,62532]
theorem n879 : impossible 7 w879.toFinset :=
  closeState (known := [w662.toFinset, w679.toFinset, w738.toFinset, w739.toFinset, w743.toFinset, w763.toFinset, w808.toFinset]) w879 (by decide) (by decide +kernel) (consbad n662 (consbad n679 (consbad n738 (consbad n739 (consbad n743 (consbad n763 (consbad n808 (nilbad 6))))))))

def w880 : List Mask := [15,240,3840,4369,8738,34952,62532]
theorem n880 : impossible 7 w880.toFinset :=
  closeState (known := [w628.toFinset, w644.toFinset, w655.toFinset, w656.toFinset, w657.toFinset, w658.toFinset, w659.toFinset, w660.toFinset, w661.toFinset, w666.toFinset, w682.toFinset, w686.toFinset, w695.toFinset, w737.toFinset, w740.toFinset, w742.toFinset, w744.toFinset, w764.toFinset, w785.toFinset, w809.toFinset]) w880 (by decide) (by decide +kernel) (consbad n628 (consbad n644 (consbad n655 (consbad n656 (consbad n657 (consbad n658 (consbad n659 (consbad n660 (consbad n661 (consbad n666 (consbad n682 (consbad n686 (consbad n695 (consbad n737 (consbad n740 (consbad n742 (consbad n744 (consbad n764 (consbad n785 (consbad n809 (nilbad 6)))))))))))))))))))))

def w881 : List Mask := [15,240,3840,4369,12066,17476,34952,61440]
theorem n881 : impossible 7 w881.toFinset :=
  closeState (known := [w665.toFinset, w666.toFinset, w668.toFinset, w750.toFinset, w753.toFinset, w760.toFinset, w810.toFinset]) w881 (by decide) (by decide +kernel) (consbad n665 (consbad n666 (consbad n668 (consbad n750 (consbad n753 (consbad n760 (consbad n810 (nilbad 6))))))))

def w882 : List Mask := [15,240,3840,4369,17476,34952,61440,61986]
theorem n882 : impossible 7 w882.toFinset :=
  closeState (known := [w673.toFinset, w679.toFinset, w767.toFinset, w768.toFinset, w772.toFinset, w774.toFinset, w811.toFinset]) w882 (by decide) (by decide +kernel) (consbad n673 (consbad n679 (consbad n767 (consbad n768 (consbad n772 (consbad n774 (consbad n811 (nilbad 6))))))))

def w883 : List Mask := [15,240,3840,4369,17476,34952,61986]
theorem n883 : impossible 7 w883.toFinset :=
  closeState (known := [w629.toFinset, w636.toFinset, w645.toFinset, w668.toFinset, w669.toFinset, w670.toFinset, w671.toFinset, w674.toFinset, w675.toFinset, w676.toFinset, w680.toFinset, w683.toFinset, w687.toFinset, w765.toFinset, w766.toFinset, w769.toFinset, w771.toFinset, w773.toFinset, w775.toFinset, w786.toFinset, w812.toFinset]) w883 (by decide) (by decide +kernel) (consbad n629 (consbad n636 (consbad n645 (consbad n668 (consbad n669 (consbad n670 (consbad n671 (consbad n674 (consbad n675 (consbad n676 (consbad n680 (consbad n683 (consbad n687 (consbad n765 (consbad n766 (consbad n769 (consbad n771 (consbad n773 (consbad n775 (consbad n786 (consbad n812 (nilbad 6))))))))))))))))))))))

def w884 : List Mask := [15,240,3840,4593,8738,17476,34952,61440]
theorem n884 : impossible 7 w884.toFinset :=
  closeState (known := [w641.toFinset, w682.toFinset, w683.toFinset, w776.toFinset, w777.toFinset, w778.toFinset, w799.toFinset, w845.toFinset]) w884 (by decide) (by decide +kernel) (consbad n641 (consbad n682 (consbad n683 (consbad n776 (consbad n777 (consbad n778 (consbad n799 (consbad n845 (nilbad 6)))))))))

def w885 : List Mask := [15,240,3855,4369,8738,17476,34952,61440]
theorem n885 : impossible 7 w885.toFinset :=
  closeState (known := [w685.toFinset, w686.toFinset, w687.toFinset, w698.toFinset, w733.toFinset, w813.toFinset, w814.toFinset, w846.toFinset, w847.toFinset]) w885 (by decide) (by decide +kernel) (consbad n685 (consbad n686 (consbad n687 (consbad n698 (consbad n733 (consbad n813 (consbad n814 (consbad n846 (consbad n847 (nilbad 6))))))))))

def w886 : List Mask := [15,240,4369,8738,12066,17476,34952,61440]
theorem n886 : impossible 7 w886.toFinset :=
  closeState (known := [w694.toFinset, w695.toFinset, w699.toFinset, w712.toFinset, w736.toFinset, w747.toFinset, w755.toFinset, w761.toFinset, w819.toFinset, w825.toFinset, w848.toFinset]) w886 (by decide) (by decide +kernel) (consbad n694 (consbad n695 (consbad n699 (consbad n712 (consbad n736 (consbad n747 (consbad n755 (consbad n761 (consbad n819 (consbad n825 (consbad n848 (nilbad 6))))))))))))

def w887 : List Mask := [15,240,4369,8738,17476,20292,34952,61440]
theorem n887 : impossible 7 w887.toFinset :=
  closeState (known := [w696.toFinset, w700.toFinset, w723.toFinset, w765.toFinset, w820.toFinset, w826.toFinset, w850.toFinset]) w887 (by decide) (by decide +kernel) (consbad n696 (consbad n700 (consbad n723 (consbad n765 (consbad n820 (consbad n826 (consbad n850 (nilbad 6))))))))

def w888 : List Mask := [15,240,4369,8738,17476,34952,36744,61440]
theorem n888 : impossible 7 w888.toFinset :=
  closeState (known := [w701.toFinset, w707.toFinset, w737.toFinset, w766.toFinset, w822.toFinset, w852.toFinset]) w888 (by decide) (by decide +kernel) (consbad n701 (consbad n707 (consbad n737 (consbad n766 (consbad n822 (consbad n852 (nilbad 6)))))))

def w889 : List Mask := [15,240,4369,8738,17476,34952,61440,65280]
theorem n889 : impossible 7 w889.toFinset :=
  closeState (known := [w713.toFinset, w714.toFinset, w738.toFinset, w739.toFinset, w767.toFinset, w768.toFinset, w823.toFinset, w827.toFinset, w853.toFinset]) w889 (by decide) (by decide +kernel) (consbad n713 (consbad n714 (consbad n738 (consbad n739 (consbad n767 (consbad n768 (consbad n823 (consbad n827 (consbad n853 (nilbad 6))))))))))

def w890 : List Mask := [15,240,4369,8738,17476,34952,65280]
theorem n890 : impossible 7 w890.toFinset :=
  closeState (known := [w630.toFinset, w637.toFinset, w692.toFinset, w698.toFinset, w699.toFinset, w700.toFinset, w701.toFinset, w702.toFinset, w710.toFinset, w711.toFinset, w716.toFinset, w717.toFinset, w718.toFinset, w734.toFinset, w741.toFinset, w742.toFinset, w770.toFinset, w771.toFinset, w776.toFinset, w815.toFinset, w821.toFinset, w824.toFinset, w828.toFinset, w849.toFinset, w854.toFinset]) w890 (by decide) (by decide +kernel) (consbad n630 (consbad n637 (consbad n692 (consbad n698 (consbad n699 (consbad n700 (consbad n701 (consbad n702 (consbad n710 (consbad n711 (consbad n716 (consbad n717 (consbad n718 (consbad n734 (consbad n741 (consbad n742 (consbad n770 (consbad n771 (consbad n776 (consbad n815 (consbad n821 (consbad n824 (consbad n828 (consbad n849 (consbad n854 (nilbad 6))))))))))))))))))))))))))

def w891 : List Mask := [15,240,4369,8738,17476,36744,61440]
theorem n891 : impossible 7 w891.toFinset :=
  closeState (known := [w638.toFinset, w689.toFinset, w704.toFinset, w705.toFinset, w706.toFinset, w709.toFinset, w712.toFinset, w713.toFinset, w717.toFinset, w719.toFinset, w735.toFinset, w743.toFinset, w744.toFinset, w772.toFinset, w773.toFinset, w816.toFinset]) w891 (by decide) (by decide +kernel) (consbad n638 (consbad n689 (consbad n704 (consbad n705 (consbad n706 (consbad n709 (consbad n712 (consbad n713 (consbad n717 (consbad n719 (consbad n735 (consbad n743 (consbad n744 (consbad n772 (consbad n773 (consbad n816 (nilbad 6)))))))))))))))))

def w892 : List Mask := [15,240,4369,8738,20292,34952,61440]
theorem n892 : impossible 7 w892.toFinset :=
  closeState (known := [w631.toFinset, w690.toFinset, w721.toFinset, w722.toFinset, w724.toFinset, w726.toFinset, w727.toFinset, w729.toFinset, w730.toFinset, w731.toFinset, w732.toFinset, w733.toFinset, w736.toFinset, w738.toFinset, w742.toFinset, w774.toFinset, w775.toFinset, w777.toFinset, w817.toFinset, w829.toFinset]) w892 (by decide) (by decide +kernel) (consbad n631 (consbad n690 (consbad n721 (consbad n722 (consbad n724 (consbad n726 (consbad n727 (consbad n729 (consbad n730 (consbad n731 (consbad n732 (consbad n733 (consbad n736 (consbad n738 (consbad n742 (consbad n774 (consbad n775 (consbad n777 (consbad n817 (consbad n829 (nilbad 6)))))))))))))))))))))

def w893 : List Mask := [15,240,4369,12066,17476,34952,61440]
theorem n893 : impossible 7 w893.toFinset :=
  closeState (known := [w632.toFinset, w639.toFinset, w691.toFinset, w746.toFinset, w748.toFinset, w749.toFinset, w751.toFinset, w752.toFinset, w754.toFinset, w756.toFinset, w757.toFinset, w758.toFinset, w759.toFinset, w762.toFinset, w763.toFinset, w764.toFinset, w767.toFinset, w771.toFinset, w778.toFinset, w818.toFinset, w830.toFinset]) w893 (by decide) (by decide +kernel) (consbad n632 (consbad n639 (consbad n691 (consbad n746 (consbad n748 (consbad n749 (consbad n751 (consbad n752 (consbad n754 (consbad n756 (consbad n757 (consbad n758 (consbad n759 (consbad n762 (consbad n763 (consbad n764 (consbad n767 (consbad n771 (consbad n778 (consbad n818 (consbad n830 (nilbad 6))))))))))))))))))))))

def w894 : List Mask := [15,3840,4369,4593,8738,17476,34952,61440]
theorem n894 : impossible 7 w894.toFinset :=
  closeState (known := [w781.toFinset, w783.toFinset, w784.toFinset, w785.toFinset, w786.toFinset, w792.toFinset, w801.toFinset, w815.toFinset, w816.toFinset, w817.toFinset, w818.toFinset, w855.toFinset]) w894 (by decide) (by decide +kernel) (consbad n781 (consbad n783 (consbad n784 (consbad n785 (consbad n786 (consbad n792 (consbad n801 (consbad n815 (consbad n816 (consbad n817 (consbad n818 (consbad n855 (nilbad 6)))))))))))))

def w895 : List Mask := [15,3840,4369,8738,17476,34952,35064,61440]
theorem n895 : impossible 7 w895.toFinset :=
  closeState (known := [w790.toFinset, w821.toFinset, w822.toFinset, w857.toFinset]) w895 (by decide) (by decide +kernel) (consbad n790 (consbad n821 (consbad n822 (consbad n857 (nilbad 6)))))

def w896 : List Mask := [15,3840,4369,8738,17476,35064,61440]
theorem n896 : impossible 7 w896.toFinset :=
  closeState (known := [w640.toFinset, w780.toFinset, w782.toFinset, w787.toFinset, w788.toFinset, w789.toFinset, w791.toFinset, w792.toFinset, w793.toFinset, w794.toFinset, w813.toFinset, w819.toFinset, w820.toFinset, w823.toFinset, w824.toFinset, w856.toFinset, w858.toFinset]) w896 (by decide) (by decide +kernel) (consbad n640 (consbad n780 (consbad n782 (consbad n787 (consbad n788 (consbad n789 (consbad n791 (consbad n792 (consbad n793 (consbad n794 (consbad n813 (consbad n819 (consbad n820 (consbad n823 (consbad n824 (consbad n856 (consbad n858 (nilbad 6))))))))))))))))))

def w897 : List Mask := [15,3840,4593,8738,17476,34952,61440]
theorem n897 : impossible 7 w897.toFinset :=
  closeState (known := [w633.toFinset, w641.toFinset, w781.toFinset, w783.toFinset, w795.toFinset, w796.toFinset, w797.toFinset, w798.toFinset, w800.toFinset, w802.toFinset, w803.toFinset, w804.toFinset, w805.toFinset, w806.toFinset, w807.toFinset, w808.toFinset, w809.toFinset, w810.toFinset, w811.toFinset, w812.toFinset, w814.toFinset, w825.toFinset, w826.toFinset, w827.toFinset, w828.toFinset, w829.toFinset, w830.toFinset, w859.toFinset, w860.toFinset]) w897 (by decide) (by decide +kernel) (consbad n633 (consbad n641 (consbad n781 (consbad n783 (consbad n795 (consbad n796 (consbad n797 (consbad n798 (consbad n800 (consbad n802 (consbad n803 (consbad n804 (consbad n805 (consbad n806 (consbad n807 (consbad n808 (consbad n809 (consbad n810 (consbad n811 (consbad n812 (consbad n814 (consbad n825 (consbad n826 (consbad n827 (consbad n828 (consbad n829 (consbad n830 (consbad n859 (consbad n860 (nilbad 6))))))))))))))))))))))))))))))

def w898 : List Mask := [240,3840,4369,8738,17476,17487,34952,61440]
theorem n898 : impossible 7 w898.toFinset :=
  closeState (known := [w838.toFinset, w849.toFinset, w850.toFinset, w856.toFinset, w859.toFinset]) w898 (by decide) (by decide +kernel) (consbad n838 (consbad n849 (consbad n850 (consbad n856 (consbad n859 (nilbad 6))))))

def w899 : List Mask := [240,3840,4369,8738,17487,34952,61440]
theorem n899 : impossible 7 w899.toFinset :=
  closeState (known := [w634.toFinset, w832.toFinset, w834.toFinset, w837.toFinset, w839.toFinset, w840.toFinset, w841.toFinset, w842.toFinset, w843.toFinset, w844.toFinset, w845.toFinset, w848.toFinset, w851.toFinset, w852.toFinset, w853.toFinset, w854.toFinset, w855.toFinset, w857.toFinset, w858.toFinset, w860.toFinset]) w899 (by decide) (by decide +kernel) (consbad n634 (consbad n832 (consbad n834 (consbad n837 (consbad n839 (consbad n840 (consbad n841 (consbad n842 (consbad n843 (consbad n844 (consbad n845 (consbad n848 (consbad n851 (consbad n852 (consbad n853 (consbad n854 (consbad n855 (consbad n857 (consbad n858 (consbad n860 (nilbad 6)))))))))))))))))))))

def w900 : List Mask := [15,240,3840,4369,8738,17476,34952,61440]
theorem n900 : impossible 8 w900.toFinset :=
  closeState (known := [w861.toFinset, w862.toFinset, w863.toFinset, w864.toFinset, w865.toFinset, w866.toFinset, w867.toFinset, w868.toFinset, w869.toFinset, w870.toFinset, w871.toFinset, w872.toFinset, w873.toFinset, w874.toFinset, w875.toFinset, w876.toFinset, w877.toFinset, w878.toFinset, w879.toFinset, w880.toFinset, w881.toFinset, w882.toFinset, w883.toFinset, w884.toFinset, w885.toFinset, w886.toFinset, w887.toFinset, w888.toFinset, w889.toFinset, w890.toFinset, w891.toFinset, w892.toFinset, w893.toFinset, w894.toFinset, w895.toFinset, w896.toFinset, w897.toFinset, w898.toFinset, w899.toFinset]) w900 (by decide) (by decide +kernel) (consbad n861 (consbad n862 (consbad n863 (consbad n864 (consbad n865 (consbad n866 (consbad n867 (consbad n868 (consbad n869 (consbad n870 (consbad n871 (consbad n872 (consbad n873 (consbad n874 (consbad n875 (consbad n876 (consbad n877 (consbad n878 (consbad n879 (consbad n880 (consbad n881 (consbad n882 (consbad n883 (consbad n884 (consbad n885 (consbad n886 (consbad n887 (consbad n888 (consbad n889 (consbad n890 (consbad n891 (consbad n892 (consbad n893 (consbad n894 (consbad n895 (consbad n896 (consbad n897 (consbad n898 (consbad n899 (nilbad 7))))))))))))))))))))))))))))))))))))))))


-- Each listed pair forces use of the corresponding input wire. The first row is
-- an edge, the second a non-edge, and no other input is high only on the first.
def pinPairs : List (Mask × Nat × Nat) :=
  [(15,0,4), (240,5,9), (3840,8,4), (61440,12,4),
   (4369,0,2), (8738,1,2), (17476,6,4), (34952,3,2)]

theorem allPinsNeeded (a : Mask) (ha : a ∈ pins) :
    ∃ p n : Nat, target.getLsbD p = true ∧ target.getLsbD n = false ∧
      ∀ b ∈ pins, b.getLsbD p = true → b.getLsbD n = false → b = a := by
  have hmap : pins = pinPairs.map Prod.fst := by decide
  rw [hmap] at ha
  obtain ⟨⟨a,p,n⟩, hpair, rfl⟩ := List.mem_map.mp ha
  have checked : pinPairs.all (fun (w,i,j) => target.getLsbD i && !target.getLsbD j &&
    pins.all (fun v => !v.getLsbD i || v.getLsbD j || v == w)) = true := by decide +kernel
  have hc := List.all_eq_true.mp checked _ hpair
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  refine ⟨p,n,hc.1.1,hc.1.2,?_⟩
  intro b hb bp bn
  have h := List.all_eq_true.mp hc.2 b hb
  simpa [bp,bn] using h


theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4*u.val+v.val)) 8 := by
  rintro ⟨C,hm,hs,hr⟩
  obtain ⟨k,hk,s,hsub,ht⟩ := extract C.gates pins C.output (desiredMask hm hr)
  have he : s = pins.toFinset := by
    apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (hsub a ha))
    intro a ha
    obtain ⟨p,n,hp,hn,uniq⟩ := allPinsNeeded a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,bp,bn⟩ := traceDist ht p n hp hn
    exact uniq b (hsub b hb) bp bn ▸ hb
  have ew : pins.toFinset = w900.toFinset := by decide +kernel
  exact n900 k (hk.trans hs) ((he.trans ew) ▸ ht)

end PEqualNP.Outside.L_meta_5982

theorem PEqualNP.Outside.L_meta_5982 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
      ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_5982.upper, PEqualNP.Outside.L_meta_5982.lower⟩
