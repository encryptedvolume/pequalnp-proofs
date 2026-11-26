import PEqualNP.Defs.AndCountCircuit
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases

/-!
Twelve strict separations on seven vertices in the integer-indexed graph census.

For every graph below, witness proves the actual list of gates is well formed and
answers the project's partial-function tests. smallerThanEveryCover proves that
no cover by as many bicliques as the circuit has AND gates exists. Each complete
bipartite subgraph is dominated by a listed rectangle. The recursive test then
exhibits a missed edge for every sufficiently short list of those rectangles.

Graph identifiers are masks on unordered vertex pairs in lexicographic order.
An option mask inside the cover proof uses bit 7*i+j for the oriented pair (i,j).
Each exceptional graph contains an induced diamond. The final lemmas exhibit its four vertices.
-/

namespace SevenVertexAnd

open PEqualNP.AndCount

abbrev V := Fin 7

def graph (rows : List Nat) : SimpleGraph V :=
  SimpleGraph.fromRel (fun a b : V => (rows.getD a.val 0).testBit b.val = true)

def circuit (gates : List (Nat × Nat)) (output : Nat) : AndCountCircuit 7 where
  size := gates.length
  leftVars i := Finset.univ.filter (fun v : V => (gates.get i).1.testBit v.val)
  rightVars i := Finset.univ.filter (fun v : V => (gates.get i).2.testBit v.val)
  leftGates i := Finset.univ.filter (fun j : Fin gates.length => (gates.get i).1.testBit (7+j.val))
  rightGates i := Finset.univ.filter (fun j : Fin gates.length => (gates.get i).2.testBit (7+j.val))
  outVars := Finset.univ.filter (fun v : V => output.testBit v.val)
  outGates := Finset.univ.filter (fun j : Fin gates.length => output.testBit (7+j.val))

def Fits (G : SimpleGraph V) (C : AndCountCircuit 7) : Prop :=
  ∀ I : Finset V, (∀ a ∈ I, ∀ b ∈ I, ¬G.Adj a b) →
    (∀ v : V, v ∉ I → ∃ a ∈ I, G.Adj a v) →
      C.eval I = false ∧ ∀ v : V, v ∉ I → C.eval (insert v I) = true

instance (rows : List Nat) : DecidableRel (graph rows).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∨ _)))

instance (G : SimpleGraph V) [DecidableRel G.Adj] (C : AndCountCircuit 7) : Decidable (Fits G C) :=
  inferInstanceAs (Decidable (∀ I : Finset V, (∀ a ∈ I, ∀ b ∈ I, ¬G.Adj a b) →
    (∀ v : V, v ∉ I → ∃ a ∈ I, G.Adj a v) →
      C.eval I = false ∧ ∀ v : V, v ∉ I → C.eval (insert v I) = true))

def graph44343 := graph [110, 81, 41, 21, 10, 5, 3]
def circuit44343 := circuit [(17, 14), (3, 192), (133, 296)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness44343 : circuit44343.size = 3 ∧ circuit44343.WellFormed ∧ Fits graph44343 circuit44343 := by
  unfold graph44343 circuit44343 AndCountCircuit.WellFormed
  decide +kernel

def graph44351 := graph [126, 81, 41, 21, 11, 5, 3]
def circuit44351 := circuit [(9, 22), (80, 131), (261, 424)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness44351 : circuit44351.size = 3 ∧ circuit44351.WellFormed ∧ Fits graph44351 circuit44351 := by
  unfold graph44351 circuit44351 AndCountCircuit.WellFormed
  decide +kernel

def graph44471 := graph [110, 89, 41, 23, 10, 5, 3]
def circuit44471 := circuit [(17, 14), (3, 200), (389, 296)] 512

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness44471 : circuit44471.size = 3 ∧ circuit44471.WellFormed ∧ Fits graph44471 circuit44471 := by
  unfold graph44471 circuit44471 AndCountCircuit.WellFormed
  decide +kernel

def graph114034 := graph [100, 84, 59, 52, 14, 13, 3]
def circuit114034 := circuit [(35, 68), (14, 144), (164, 265)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness114034 : circuit114034.size = 3 ∧ circuit114034.WellFormed ∧ Fits graph114034 circuit114034 := by
  unfold graph114034 circuit114034 AndCountCircuit.WellFormed
  decide +kernel

def graph114037 := graph [106, 85, 58, 53, 14, 13, 3]
def circuit114037 := circuit [(21, 42), (3, 192), (432, 268)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness114037 : circuit114037.size = 3 ∧ circuit114037.WellFormed ∧ Fits graph114037 circuit114037 := by
  unfold graph114037 circuit114037 AndCountCircuit.WellFormed
  decide +kernel

def graph114039 := graph [110, 85, 59, 53, 14, 13, 3]
def circuit114039 := circuit [(68, 51), (164, 9), (145, 14)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness114039 : circuit114039.size = 3 ∧ circuit114039.WellFormed ∧ Fits graph114039 circuit114039 := by
  unfold graph114039 circuit114039 AndCountCircuit.WellFormed
  decide +kernel

def graph114166 := graph [108, 92, 59, 55, 14, 13, 3]
def circuit114166 := circuit [(51, 76), (168, 5), (404, 266)] 512

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness114166 : circuit114166.size = 3 ∧ circuit114166.WellFormed ∧ Fits graph114166 circuit114166 := by
  unfold graph114166 circuit114166 AndCountCircuit.WellFormed
  decide +kernel

def graph114167 := graph [110, 93, 59, 55, 14, 13, 3]
def circuit114167 := circuit [(25, 38), (12, 176), (192, 259)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness114167 : circuit114167.size = 3 ∧ circuit114167.WellFormed ∧ Fits graph114167 circuit114167 := by
  unfold graph114167 circuit114167 AndCountCircuit.WellFormed
  decide +kernel

def graph376303 := graph [94, 93, 59, 55, 47, 28, 3]
def circuit376303 := circuit [(35, 92), (21, 138), (14, 401)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness376303 : circuit376303.size = 3 ∧ circuit376303.WellFormed ∧ Fits graph376303 circuit376303 := by
  unfold graph376303 circuit376303 AndCountCircuit.WellFormed
  decide +kernel

def graph378106 := graph [116, 76, 67, 50, 41, 25, 7]
def circuit378106 := circuit [(48, 9), (133, 194), (416, 152), (68, 259)] 1536

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness378106 : circuit378106.size = 4 ∧ circuit378106.WellFormed ∧ Fits graph378106 circuit378106 := by
  unfold graph378106 circuit378106 AndCountCircuit.WellFormed
  decide +kernel

def graph452607 := graph [126, 125, 99, 83, 43, 23, 15]
def circuit452607 := circuit [(35, 84), (168, 19), (194, 269)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness452607 : circuit452607.size = 3 ∧ circuit452607.WellFormed ∧ Fits graph452607 circuit452607 := by
  unfold graph452607 circuit452607 AndCountCircuit.WellFormed
  decide +kernel

def graph454524 := graph [120, 116, 106, 85, 43, 23, 15]
def circuit454524 := circuit [(21, 104), (36, 130), (464, 267)] 768

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem witness454524 : circuit454524.size = 3 ∧ circuit454524.WellFormed ∧ Fits graph454524 circuit454524 := by
  unfold graph454524 circuit454524 AndCountCircuit.WellFormed
  decide +kernel


def hit (mask : Nat) (x y : V) : Bool := mask.testBit (7*x.val + y.val)

def miss (edges : List (V × V)) (mask : Nat) :=
  edges.any (fun e => !(hit mask e.1 e.2))

def outside (edges : List (V × V)) (options : List Nat) : Nat → Nat → Bool
  | 0, acc => miss edges acc
  | k+1, acc => miss edges acc && options.all (fun b => outside edges options k (acc ||| b))

theorem missed {edges : List (V × V)} {options : List Nat} (k : Nat) (acc : Nat)
    (h : outside edges options k acc = true) (xs : List Nat) (hlen : xs.length ≤ k)
    (hm : ∀ b ∈ xs, b ∈ options) :
    ∃ e ∈ edges, hit acc e.1 e.2 = false ∧ ∀ b ∈ xs, hit b e.1 e.2 = false := by
  induction k generalizing xs acc with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    obtain ⟨e, he, hf⟩ := List.any_eq_true.mp h
    exact ⟨e, he, by simpa using hf, by simp⟩
  | succ k ih =>
    simp only [outside, Bool.and_eq_true] at h
    obtain ⟨hme, hall⟩ := h
    cases xs with
    | nil =>
      obtain ⟨e, he, hf⟩ := List.any_eq_true.mp hme
      exact ⟨e, he, by simpa using hf, by simp⟩
    | cons b rest =>
      have hb : b ∈ options := hm b (by simp)
      obtain ⟨e, he, hf, hr⟩ := ih (acc ||| b) (List.all_eq_true.mp hall b hb) rest
        (by simpa using hlen) (fun m hmem => hm m (by simp [hmem]))
      have hboth : hit acc e.1 e.2 = false ∧ hit b e.1 e.2 = false := by
        simpa [hit, Nat.testBit_or] using hf
      refine ⟨e, he, hboth.1, ?_⟩
      intro m hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hboth.2
      · exact hr m hmem

def CompleteList (G : SimpleGraph V) (options : List Nat) : Prop :=
  ∀ X : Finset V, ∃ mask ∈ options, ∀ a ∈ X, ∀ b : V,
    (∀ u ∈ X, G.Adj u b) → hit mask a b = true ∧ hit mask b a = true

instance (G : SimpleGraph V) [DecidableRel G.Adj] (options : List Nat) :
    Decidable (CompleteList G options) := by unfold CompleteList; infer_instance

def HasCover (G : SimpleGraph V) (s : Nat) : Prop :=
  ∃ (k : Nat) (X Y : Fin k → Finset V), k ≤ s ∧
    (∀ i, ∀ v ∈ X i, ∀ w ∈ Y i, G.Adj v w) ∧
    (∀ v w, G.Adj v w → ∃ i, (v ∈ X i ∧ w ∈ Y i) ∨ (w ∈ X i ∧ v ∈ Y i))

theorem certifies {G : SimpleGraph V} {s : Nat} {options : List Nat} {edges : List (V × V)}
    (hp : CompleteList G options) (he : ∀ e ∈ edges, G.Adj e.1 e.2)
    (hc : outside edges options s 0 = true) : ¬HasCover G s := by
  rintro ⟨k, X, Y, hlen, hrect, hcover⟩
  have each := fun i : Fin k => hp (X i)
  choose masks hm htest using each
  obtain ⟨e, hem, _, hmiss⟩ := missed s 0 hc (List.ofFn masks) (by simpa using hlen)
    (by intro b hb; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb; exact hm i)
  obtain ⟨i, hcase⟩ := hcover e.1 e.2 (he e hem)
  have hm0 := hmiss (masks i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hv := (htest i _ hx _ (fun u hu => hrect i u hu _ hy)).1
    simp_all
  · have hv := (htest i _ hx _ (fun u hu => hrect i u hu _ hy)).2
    simp_all

def edges44343 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 4), (1, 6), (2, 3), (2, 5), (3, 4)]
def options44343 : List Nat := [4432408363246, 13194139541568, 8796629903490, 137448013828, 171809833000, 2720008330, 2191654920]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover44343 : ¬ HasCover graph44343 circuit44343.size := by
  apply certifies (options := options44343) (edges := edges44343)
  · unfold graph44343
    decide +kernel
  · unfold graph44343
    decide +kernel
  · decide +kernel

def edges44351 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 4), (1, 6), (2, 3), (2, 5), (3, 4)]
def options44351 : List Nat := [4432676798718, 8796629903490, 13194944850000, 137448013828, 171809833000, 2720008330, 2986346512, 2191654920, 2458009620]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover44351 : ¬ HasCover graph44351 circuit44351.size := by
  apply certifies (options := options44351) (edges := edges44351)
  · unfold graph44351
    decide +kernel
  · unfold graph44351
    decide +kernel
  · decide +kernel

def edges44471 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 3), (2, 5), (3, 4)]
def options44471 : List Nat := [4432408363246, 13194145834056, 8796634098818, 12731526, 137448013828, 171809833000, 2720008330, 2195850248]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover44471 : ¬ HasCover graph44471 circuit44471.size := by
  apply certifies (options := options44471) (edges := edges44471)
  · unfold graph44471
    decide +kernel
  · unfold graph44471
    decide +kernel
  · decide +kernel

def edges114034 : List (V × V) := [(0, 2), (0, 5), (0, 6), (1, 2), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
def options114034 : List Nat := [4432406265956, 13194139591236, 8796629936640, 138522051076, 2726464000, 3791915008, 309313290276, 446744231968, 277134573568, 415639535616]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover114034 : ¬ HasCover graph114034 circuit114034.size := by
  apply certifies (options := options114034) (edges := edges114034)
  · unfold graph114034
    decide +kernel
  · unfold graph114034
    decide +kernel
  · decide +kernel

def edges114037 : List (V × V) := [(0, 1), (0, 3), (0, 5), (0, 6), (1, 2), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
def options114037 : List Nat := [4432408346858, 13194139541568, 8796629936770, 171809866410, 138522034688, 2728561290, 3791915008, 446744231968, 277136670728, 415639535616]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover114037 : ¬ HasCover graph114037 circuit114037.size := by
  apply certifies (options := options114037) (edges := edges114037)
  · unfold graph114037
    decide +kernel
  · unfold graph114037
    decide +kernel
  · decide +kernel

def edges114039 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
def options114039 : List Nat := [4432408363246, 13194139591236, 8796629936770, 171809866410, 138522051076, 2728561290, 3794028686, 309313290276, 446744231968, 277136670728, 415641649164]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover114039 : ¬ HasCover graph114039 circuit114039.size := by
  apply certifies (options := options114039) (edges := edges114039)
  · unfold graph114039
    decide +kernel
  · unfold graph114039
    decide +kernel
  · decide +kernel

def edges114166 : List (V × V) := [(0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
def options114166 : List Nat := [4432408363116, 13194145883724, 8796634131968, 1623591936, 171809833000, 138522051076, 2726464000, 3791915008, 309313290276, 446744231968, 277140866056, 415645877772]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover114166 : ¬ HasCover graph114166 circuit114166.size := by
  apply certifies (options := options114166) (edges := edges114166)
  · unfold graph114166
    decide +kernel
  · unfold graph114166
    decide +kernel
  · decide +kernel

def edges114167 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
def options114167 : List Nat := [4432408363246, 13194145883724, 8796634132098, 1623608454, 171809866410, 138522051076, 2728561290, 3794028686, 309317485734, 446748460706, 277140866056, 415645877772]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover114167 : ¬ HasCover graph114167 circuit114167.size := by
  apply certifies (options := options114167) (edges := edges114167)
  · unfold graph114167
    decide +kernel
  · unfold graph114167
    decide +kernel
  · decide +kernel

def edges376303 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 6), (1, 2), (1, 3), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
def options376303 : List Nat := [4398317060318, 8796634132098, 13194951192156, 1353089690, 1623608454, 138522051076, 2462205078, 2728561290, 3527706258, 3794028686, 277140866056, 415645877772, 562406098960, 698780142100, 835184888856, 971541892636]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover376303 : ¬ HasCover graph376303 circuit376303.size := by
  apply certifies (options := options376303) (edges := edges376303)
  · unfold graph376303
    decide +kernel
  · unfold graph376303
    decide +kernel
  · decide +kernel

def edges378106 : List (V × V) := [(0, 2), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 6), (2, 6), (3, 4), (3, 5), (4, 5)]
def options378106 : List Nat := [4432674701428, 13194139591236, 8796097259008, 17592187142660, 30786326634560, 311754227760, 277130249216, 560795222032, 867650502688]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover378106 : ¬ HasCover graph378106 circuit378106.size := by
  apply certifies (options := options378106) (edges := edges378106)
  · unfold graph378106
    decide +kernel
  · unfold graph378106
    decide +kernel
  · decide +kernel

def edges452607 : List (V × V) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 5), (2, 6), (3, 4), (3, 6), (4, 5)]
def options452607 : List Nat := [4432676798718, 8865353612930, 13298030411388, 17729626620420, 22162032853730, 26594439098502, 31026845331552, 52776699741708, 57174744139458, 61572788543630, 65970832941120, 35186693637128, 39585006486738, 43983319345290, 48381632194640, 696590584340, 730681871010, 764773159062, 798864445472, 561332094992, 595425495210, 629518898322, 663612298280]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover452607 : ¬ HasCover graph452607 circuit452607.size := by
  apply certifies (options := options452607) (edges := edges452607)
  · unfold graph452607
    decide +kernel
  · unfold graph452607
    decide +kernel
  · decide +kernel

def edges454524 : List (V × V) := [(0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 4), (1, 5), (1, 6), (2, 3), (2, 5), (2, 6), (3, 4), (3, 6), (4, 5)]
def options454524 : List Nat := [4432676782200, 13298024069232, 8865349417472, 31026845331552, 22162043437160, 17729635123712, 65970832941120, 48381632194640, 35186697961480, 43983325800960, 798864445472, 561332094992, 732336619560, 698511690240]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem smallerThanEveryCover454524 : ¬ HasCover graph454524 circuit454524.size := by
  apply certifies (options := options454524) (edges := edges454524)
  · unfold graph454524
    decide +kernel
  · unfold graph454524
    decide +kernel
  · decide +kernel

def Diamond (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, [a,b,c,d].Nodup ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧
    G.Adj b c ∧ G.Adj b d ∧ ¬ G.Adj c d

theorem diamond44343 : Diamond graph44343 := by
  refine ⟨0, 2, 3, 5, ?_⟩
  unfold graph44343
  decide

theorem diamond44351 : Diamond graph44351 := by
  refine ⟨0, 1, 4, 6, ?_⟩
  unfold graph44351
  decide

theorem diamond44471 : Diamond graph44471 := by
  refine ⟨0, 1, 3, 6, ?_⟩
  unfold graph44471
  decide

theorem diamond114034 : Diamond graph114034 := by
  refine ⟨2, 3, 4, 5, ?_⟩
  unfold graph114034
  decide

theorem diamond114037 : Diamond graph114037 := by
  refine ⟨2, 3, 4, 5, ?_⟩
  unfold graph114037
  decide

theorem diamond114039 : Diamond graph114039 := by
  refine ⟨0, 1, 2, 6, ?_⟩
  unfold graph114039
  decide

theorem diamond114166 : Diamond graph114166 := by
  refine ⟨2, 3, 0, 1, ?_⟩
  unfold graph114166
  decide

theorem diamond114167 : Diamond graph114167 := by
  refine ⟨0, 1, 2, 6, ?_⟩
  unfold graph114167
  decide

theorem diamond376303 : Diamond graph376303 := by
  refine ⟨0, 1, 2, 6, ?_⟩
  unfold graph376303
  decide

theorem diamond378106 : Diamond graph378106 := by
  refine ⟨2, 6, 0, 1, ?_⟩
  unfold graph378106
  decide

theorem diamond452607 : Diamond graph452607 := by
  refine ⟨0, 1, 2, 3, ?_⟩
  unfold graph452607
  decide

theorem diamond454524 : Diamond graph454524 := by
  refine ⟨0, 3, 4, 6, ?_⟩
  unfold graph454524
  decide

end SevenVertexAnd
