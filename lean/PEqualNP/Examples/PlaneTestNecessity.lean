import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto
import PEqualNP.Defs.CircuitLowerBounds

/-!
A weight-nine input to the cyclic projective plane has four zero coordinates. For each
four-point set, the construction below gives a forty-gate monotone circuit with one wrong
output at the corresponding input and correct outputs at every other input of weight at
least nine. The ordinary circuit computes the thirteen line ORs in thirty-nine gates.

In each exceptional circuit one output computes the conjunction of its line OR and the
OR of the four zero coordinates. Distributing this conjunction shares intermediate wires
with another line. The fifty-five packed programs generate all 715 exceptions by cyclic
relabelling. The Python companion regenerates the programs and simulates their gates.

The kernel checks the gate lists, all thirteen output formulas, and coverage of the
four-point sets. The theorem `missesOmittedRow` uses the project's circuit evaluation.
-/

namespace PlaneTestNecessity

open PEqualNP.CircuitLowerBounds

abbrev Input := Fin 13 → Bool
abbrev CNF := List Nat

def clause (x : Input) (bits : Nat) : Prop :=
  ∃ i : Fin 13, bits.testBit i.val = true ∧ x i = true

def holds (x : Input) (f : CNF) : Prop := ∀ bits ∈ f, clause x bits

noncomputable def value (x : Input) (f : CNF) : Bool := by
  classical
  exact decide (holds x f)

def either (f g : CNF) : CNF :=
  f.flatMap fun c => g.map fun d => c ||| d

theorem clause_union (x : Input) (a b : Nat) :
    clause x (a ||| b) ↔ clause x a ∨ clause x b := by
  simp only [clause, Nat.testBit_or, Bool.or_eq_true]
  aesop

theorem holds_either (x : Input) (f g : CNF) :
    holds x (either f g) ↔ holds x f ∨ holds x g := by
  classical
  constructor
  · intro h
    by_cases hf : holds x f
    · exact Or.inl hf
    · right
      obtain ⟨c, hcf, hc⟩ : ∃ c ∈ f, ¬ clause x c := by simpa [holds] using hf
      intro d hd
      exact (clause_union x c d).mp (h _ (List.mem_flatMap.mpr
        ⟨c, hcf, List.mem_map.mpr ⟨d, hd, rfl⟩⟩)) |>.resolve_left hc
  · intro h z hz
    obtain ⟨c, hc, hc'⟩ := List.mem_flatMap.mp hz
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    exact (clause_union x _ _).mpr (h.imp (fun hf => hf _ hc) (fun hg => hg _ hd))

theorem value_false (x : Input) : value x [0] = false := by
  simp [value, holds, clause]

theorem value_and (x : Input) (f g : CNF) :
    value x (f ++ g) = (value x f && value x g) := by
  have hh : holds x (f ++ g) ↔ holds x f ∧ holds x g := by
    simp only [holds, List.mem_append]; aesop
  apply Bool.eq_iff_iff.mpr
  simpa only [value, decide_eq_true_eq, Bool.and_eq_true] using hh

theorem value_or (x : Input) (f g : CNF) :
    value x (either f g) = (value x f || value x g) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [value, decide_eq_true_eq, Bool.or_eq_true] using holds_either x f g

def inputCNFs : List CNF := List.ofFn fun i : Fin 13 => [2^i.val]

theorem map_inputs (x : Input) : inputCNFs.map (value x) = List.ofFn x := by
  rw [inputCNFs, List.map_ofFn]
  congr 1
  funext i
  have hc : holds x [2^i.val] ↔ x i = true := by
    simp only [holds, List.mem_singleton, forall_eq, clause, Nat.testBit_two_pow]
    constructor
    · rintro ⟨j, hj, hx⟩
      have : i = j := Fin.ext (by simpa [eq_comm] using hj)
      simpa [this] using hx
    · intro hi
      exact ⟨i, by simp, hi⟩
  simp [value, hc]

structure Step where
  meet : Bool
  left : Nat
  right : Nat
deriving DecidableEq

def Step.asGate (s : Step) : Gate :=
  ⟨if s.meet then .and else .or, [s.left,s.right]⟩

def symbolic (ws : List CNF) (s : Step) : List CNF :=
  let a := ws.getD s.left [0]
  let b := ws.getD s.right [0]
  ws ++ [if s.meet then a ++ b else either a b]

def advance (bs : List Bool) (g : Gate) :=
  bs ++ [g.op.eval (g.inputs.map fun i => bs.getD i false)]

theorem map_step (x : Input) (ws : List CNF) (s : Step) :
    (symbolic ws s).map (value x) = advance (ws.map (value x)) s.asGate := by
  have atWire (i : Nat) : (ws.map (value x)).getD i false = value x (ws.getD i [0]) := by
    exact (value_false x) ▸ (List.getD_map (l := ws) (n := i) (d := [0]) (value x))
  cases s with
  | mk op a b =>
    cases op <;> simp [symbolic, advance, Step.asGate, GateOp.eval, -List.getD_eq_getElem?_getD, atWire, value_or, value_and]

theorem map_run (x : Input) (ss : List Step) (ws : List CNF) :
    (ss.foldl symbolic ws).map (value x) = (ss.map Step.asGate).foldl advance (ws.map (value x)) := by
  induction ss generalizing ws with
  | nil => rfl
  | cons s ss ih => simp [ih, map_step]

theorem eval_wire (x : Input) (ss : List Step) (o : Nat) :
    (Circuit.mk (ss.map Step.asGate) o).eval (List.ofFn x) =
      value x ((ss.foldl symbolic inputCNFs).getD o [0]) := by
  have h := map_run x ss inputCNFs
  rw [map_inputs] at h
  change ((ss.map Step.asGate).foldl advance (List.ofFn x)).getD o false = _
  rw [← h, ← value_false x, List.getD_map]


-- Each base-8192 digit encodes a gate: the low six bits are the left operand,
-- the next six the right operand, and the high bit selects AND. Output indices use six bits.
structure Packed where
  zeros : Nat
  target : Nat
  gates : Nat
  outputs : Nat

def pattern0 : Packed := ⟨15, 0, 1388762614350087247286566269139483907135991559804693469778134163201183599670094545729084752924616651376842223464330775808560432577116758045838062574187421953, 230043140656071726932980⟩
def pattern1 : Packed := ⟨23, 1, 1388756119115233057287230821701929912386925865237223851582381403844301676788001130243386137443081602819874909779418701103005199182887174900058549100160327873, 230043140656071726935311⟩
def pattern2 : Packed := ⟨27, 0, 1388769161131303039570306295518877562334295993088785555907713129783919791937687355078194519464801303185156525237699030928702451011629849816624169231376818305, 230043140656071726932980⟩
def pattern3 : Packed := ⟨29, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520746815191877697193583252572312803605638980612386568402453410528370946, 230043140656071726932980⟩
def pattern4 : Packed := ⟨39, 0, 1388381726775123602167270951558564335556069524157669521977665878825439143308379815992961691620044342543726817013112875936493721515228693360408121247736029506, 230043140656071726920884⟩
def pattern5 : Packed := ⟨43, 0, 1388772434521910935712176308708574389933448209730831598972502613075287888071483759752749402734893629089313676124383158488773460228886393340545715014869819586, 230043140656071726920884⟩
def pattern6 : Packed := ⟨45, 2, 1388756170661594659571635400643769572836164603953846319516207611070155946173500524106797288501731206071221897867874881517591984223170681163593634738220933313, 230043140656071727072399⟩
def pattern7 : Packed := ⟨51, 4, 1388759239465336815234452891407143956871562965334806577927740043699600955178694607846567204816575442021015207419069786861261609447124949857670358946722455744, 230043140656072197493903⟩
def pattern8 : Packed := ⟨53, 4, 1388762512855944711376322904596840784470715181976852620992529526990969051312491012521122088086667767925172358305753914421332618664381493381591904730215457025, 230043140656072197493714⟩
def pattern9 : Packed := ⟨57, 4, 1388765786246552607518192917786537612069867398618898664057319010282337147446287417195676971356760093829329509192438041981403627881638041628456465603911852096, 230043140656072197493903⟩
def pattern10 : Packed := ⟨71, 0, 1388381726775123602167270951558564335556069524157669521977665878825439143308379815992961475914139667936200007047413676169225007582887036102432427564497166722, 230043140655044207137972⟩
def pattern11 : Packed := ⟨75, 0, 1388775707912518831854046321898271217532600426372877642037292096366655984205280164427304286004985954993470827011067286048843171213452335445934222808205861123, 230043140656071725372596⟩
def pattern12 : Packed := ⟨77, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520531109287203089666773286873113036336925048270726948955252182187827586, 230043140655044207137972⟩
def pattern13 : Packed := ⟨83, 0, 1388381726775123602167270951558564335556069524157669521977665878825439143308379815992961691620044342543726817013112875936492423282538089580403575712477372804, 230043140656071725372596⟩
def pattern14 : Packed := ⟨85, 1, 1388381727162368278661034384366310133716110761689564685867761879180655778509280759691471826980209436317537269397236848338197815623686603886023060760525619584, 230012066676471370964242⟩
def pattern15 : Packed := ⟨89, 3, 1388756222207956261856039979585609233285403342670468787450033818296010215558999917970208439560380809322568885956331061932177471030763586008595682386124579009, 230043140656071735071887⟩
def pattern16 : Packed := ⟨99, 5, 1388756017621090521376987457159286789721649487409383002796776767634087128430397597035423472605132718975838289736171831292423742772604681518998830572494233793, 230043140656098621609103⟩
def pattern17 : Packed := ⟨101, 2, 1388381727574487864623844046287296305505524232271906962545517211268296671507323975649099947673904221704778576652383375542020963591677874270304557765154652544, 230012066676471371089234⟩
def pattern18 : Packed := ⟨105, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520746815191877304826828371470510724799990211686254348503500122593698181, 230043140656058893161652⟩
def pattern19 : Packed := ⟨113, 4, 1388775606418376295943802957355628094867324048545036793251687460156441435847676631219341621167037071541800961851776713692176468134188842067191890043704811779, 230043140656072195147090⟩
def pattern20 : Packed := ⟨135, 0, 1388381726775123602167270951558564335556069524157669521977665878825439143308379815992961475914139667936200007047413676169225007582887036102432427564497158594, 230043140655044207137972⟩
def pattern21 : Packed := ⟨139, 0, 1388778981303126727995916335087968045131752643014923685102081579658024080339076569101859169275078280897627977901319619953463472392020586331189444158021017856, 230043140656071576736948⟩
def pattern22 : Packed := ⟨141, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520531109287203089666773286873113036336925048270726948955252182187819458, 230043140655044207137972⟩
def pattern23 : Packed := ⟨147, 4, 1388759137971047947360913464728654821836140032836383763604197986966689883838608635338347363465183419220764241070776602242089485870320364572649627068616253632, 230043140656072197493903⟩
def pattern24 : Packed := ⟨149, 4, 1388762411361655843502783477918351649435292249478429806668987470258057979972405040012902246735275745124921391957460729802160495087576908096571172852109254913, 230043140656072197493714⟩
def pattern25 : Packed := ⟨153, 4, 1388765684752263739644653491108048477034444466120475849733776953549426076106201444687457130005368071029078542844144857362231504304833456343435733725805649984, 230043140656072197493903⟩
def pattern26 : Packed := ⟨163, 4, 1388759086824368476304795433151181146361618797674879116027289791464494431664012212948726502251902606411372152650221535044762148329783472417810349489815920832, 230043140656072197493903⟩
def pattern27 : Packed := ⟨165, 4, 1388762360214976372446665446340877973960771014316925159092079274755862527797808617623281385521994932315529303536905662604833157547040015941731895273308922113, 230043140656072197493714⟩
def pattern28 : Packed := ⟨169, 4, 1388765633605584268588535459530574801559923230958971202156868758047230623931605022297836268792087258219686454423589790164904166764296564188596456147005317184, 230043140656072197493903⟩
def pattern29 : Packed := ⟨177, 5, 2452832704710280533395673944966472011649438641276384498787756036070873516617980440353213376142493275144270888807442642319257845432756790663948397977294970944, 244435114699126648951951⟩
def pattern30 : Packed := ⟨195, 0, 1388381726775123602167270951558564335556069524157669521977665878825439143308379815992961475914139667936200007047413676169225007582887036102432427564497125830, 230043140655044207137972⟩
def pattern31 : Packed := ⟨197, 6, 1388756069167452123661392036101126450170888226126005470730602974859941397815896990898834407957877648012025222740030614018547462649472662744457175815250616513, 230043140657586827777167⟩
def pattern32 : Packed := ⟨201, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520531109287203089666773286873113036336925048270726948955252182187786694, 230043140655044207137972⟩
def pattern33 : Packed := ⟨209, 4, 1388775504924087428070263530677138959831901116046613978928145403423530364507590658711121779815645048741549995503483529073004344557384256782171158165598609667, 230043140656072195147090⟩
def pattern34 : Packed := ⟨225, 4, 1388775453777407957014145499099665284357379880885109331351237207921334912332994236321500918602364235932157907082928461875677007016847364627331880586798276867, 230043140656072195147090⟩
def pattern35 : Packed := ⟨267, 0, 1388782254693734624137786348277664872730904859656969728166871062949392176472872973776414052545170606409418373903333739090180839111729901138297429257819889985, 230043140656058893161652⟩
def pattern36 : Packed := ⟨269, 12, 1388766043178847738085601115835826001847139265948180804924651171796453977010253290894566221638955921794424600492548627097854476210922481251616034763380990016, 249157481181972671845519⟩
def pattern37 : Packed := ⟨275, 0, 1388381726775123602167270951558564335556069524157669521977665878760246033907263572237534063443976256870538157344521478888541877668819344634951759769770729988, 230043134758500786328756⟩
def pattern38 : Packed := ⟨277, 12, 1388769316569455634227471129025522829446291482590226847989440655087822073144049695569121104909048247698581751379232754657925485428179024775537580546873991297, 249157481181972671845330⟩
def pattern39 : Packed := ⟨281, 0, 1388381726762734162608204357390268621550327895381729773098964274505273754723750378149093118639123792024004923583980915755653795134203035481474584387461390852, 230043134758500786328756⟩
def pattern40 : Packed := ⟨291, 5, 1388755916126801653503448030480797654686226554910960188473234710901176057090311624527203631253740696175587323387878646673251619195800096233978098694388031681, 230043140656098621609103⟩
def pattern41 : Packed := ⟨293, 12, 1388772589960063530369341142215219657045443699232272891054230138379190169277846100243675988179140573602738902265916882217995196412744966880926088340210032834, 249157481181972671821138⟩
def pattern42 : Packed := ⟨297, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520746815191877304826828371470510724799990211686254348503500122592649733, 230043140656058893161652⟩
def pattern43 : Packed := ⟨305, 4, 1388782153199592088227542983735021750065628481829128879381266426739177628115269440568451387707221724919390691808496315114017034331339811087970156650161086785, 230043140656059313390930⟩
def pattern44 : Packed := ⟨323, 5, 1388755864980122182447329998903323979211705319749455540896326515398980604915715202137582770040459883366195234967323579475924281655263204079138821115587698881, 230043140656098621609103⟩
def pattern45 : Packed := ⟨325, 12, 1388775863350671426511211155404916484644595915874318934119019621670558265411642504918230871449232899506896053151887298808627316463473281690351459203173949699, 249157481181972669498706⟩
def pattern46 : Packed := ⟨329, 0, 1388381726762734162608204357390268621550327895381729773098964274570466864124866621904520746815191877304826828371470510724799990211686254348503500122592125446, 230043140656058893161652⟩
def pattern47 : Packed := ⟨337, 3, 1388381727974121980678855034438878481465210972015453526267789039437932571549820254762673444688828264764010973278779450801500655676851590296938916517058200064, 74429921315795806291282⟩
def pattern48 : Packed := ⟨393, 7, 1388756120713813725945796615042966110620126964842627938664429182085795667201277799187060938517723540043617151800664537692451260214344961366899408666333126849, 230043140739844041430159⟩
def pattern49 : Packed := ⟨401, 4, 1388782051705303220354003557056532615030205549330706065057724370006266556775183468060231546355829702119139725460203130494844910754535225802949424772054884673, 230043140656059313390930⟩
def pattern50 : Packed := ⟨547, 0, 1388772130039044332091558028673106984827179412235563156001876442876554674051225842228089878680717560688560777079503604631257089498472637485483519380551213250, 230043140656071726920884⟩
def pattern51 : Packed := ⟨549, 0, 1388381724365523939892114447960893973809469281907970330608141271756027365097546005091455103589683069241593951774121463477157984467804787132957476026943299906, 230043140656071726920884⟩
def pattern52 : Packed := ⟨553, 0, 1388772027745685389979321965518159633878136941912553860848060051872163769702032997448848156254155935069776600238393470236602414417398853175804964222950547650, 230043140656071726920884⟩
def pattern53 : Packed := ⟨581, 6, 1388755967673163255787852609422637315135465293627582656407060918127030326475811018390614566606485625211774256391737429399375339072668077459436443937144414401, 230043140657586827777167⟩
def pattern54 : Packed := ⟨585, 0, 1388775301136293286121191978707856461477289158554599903912849535163531865835829402123403039524248260973933751125077597796672125401964795281193472016286589187, 230043140656071725372596⟩

def representatives : List Packed := [pattern0, pattern1, pattern2, pattern3, pattern4, pattern5, pattern6, pattern7, pattern8, pattern9, pattern10, pattern11, pattern12, pattern13, pattern14, pattern15, pattern16, pattern17, pattern18, pattern19, pattern20, pattern21, pattern22, pattern23, pattern24, pattern25, pattern26, pattern27, pattern28, pattern29, pattern30, pattern31, pattern32, pattern33, pattern34, pattern35, pattern36, pattern37, pattern38, pattern39, pattern40, pattern41, pattern42, pattern43, pattern44, pattern45, pattern46, pattern47, pattern48, pattern49, pattern50, pattern51, pattern52, pattern53, pattern54]


structure Witness where
  zeros : Nat
  target : Nat
  steps : List Step
  outputs : List Nat

def rotateBits (m t : Nat) := ((m <<< t) ||| (m >>> (13 - t))) % 8192

def lineBits (w : Nat) := rotateBits 523 w

def rotateWire (i t : Nat) := if i < 13 then (i+t)%13 else i

def expand (p : Packed) (t : Nat) : Witness :=
  let gates := (List.range 40).map fun j =>
    let digit := (p.gates >>> (13*j)) % 8192
    Step.mk (decide (4096 ≤ digit)) (rotateWire (digit%64) t) (rotateWire ((digit/64)%64) t)
  let outs := (List.range 13).map fun w =>
    let old := (w+13-t)%13
    (p.outputs >>> (6*old)) % 64
  ⟨rotateBits p.zeros t, (p.target+t)%13, gates, outs⟩

def witnesses : List Witness :=
  representatives.flatMap fun p => (List.range 13).map (expand p)

def points (bits : Nat) : Finset (Fin 13) :=
  Finset.univ.filter fun i => bits.testBit i.val = true

def signature (w : Witness) (forms : List CNF) (i : Nat) : Bool :=
  let f := forms.getD (w.outputs.getD i 0) [0]
  if i == w.target then
    f == [lineBits i,w.zeros] || f == [w.zeros,lineBits i]
  else f == [lineBits i]

def checked (w : Witness) : Bool :=
  let forms := w.steps.foldl symbolic inputCNFs
  w.steps.length == 40 &&
    (w.steps.filter (·.meet)).length == 1 &&
    w.steps.zipIdx.all (fun (s,j) => s.left < 13+j && s.right < 13+j && s.left != s.right) &&
    w.outputs.length == 13 && w.outputs.all (· < 53) && w.target < 13 &&
    (points w.zeros).card == 4 && 0 < ((points (lineBits w.target)) \ (points w.zeros)).card &&
    (List.range 13).all (signature w forms)



@[simp] theorem holds_cons (x : Input) (c : Nat) (f : CNF) :
    holds x (c :: f) ↔ clause x c ∧ holds x f := by
  simp only [holds, List.mem_cons]
  aesop

@[simp] theorem holds_nil (x : Input) : holds x [] := by simp [holds]

def zeroSet (x : Input) : Finset (Fin 13) :=
  (Finset.univ.filter fun v => x v = true)ᶜ

theorem hits_iff (x : Input) (h : Nat) (hh : (points h).card = 4)
    (hx : 9 ≤ (Finset.univ.filter fun v => x v = true).card) :
    clause x h ↔ zeroSet x ≠ points h := by
  have hlim : (zeroSet x).card ≤ 4 := by
    simp only [zeroSet, Finset.card_compl, Fintype.card_fin]
    omega
  constructor
  · rintro ⟨v, hv, hvx⟩ he
    have hmem : v ∈ zeroSet x := he ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
    simp [zeroSet, hvx] at hmem
  · intro hne
    by_contra hc
    have sub : points h ⊆ zeroSet x := by
      intro v hv
      have hbit := (Finset.mem_filter.mp hv).2
      exact Finset.mem_compl.mpr (fun hp => hc ⟨v, hbit, (Finset.mem_filter.mp hp).2⟩)
    exact hne (Finset.eq_of_subset_of_card_le sub (by omega)).symm

theorem countInputs (w : Witness) (hw : checked w = true) :
    w.steps.length = 40 ∧ (w.steps.filter (·.meet)).length = 1 ∧ (points w.zeros).card = 4 := by
  simp only [checked, Bool.and_eq_true, beq_iff_eq] at hw
  tauto

theorem outputSpec (w : Witness) (hw : checked w = true) (x : Input) (i : Fin 13) :
    (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) = true ↔
      clause x (lineBits i.val) ∧ (i.val = w.target → clause x w.zeros) := by
  have hall : (List.range 13).all (signature w (w.steps.foldl symbolic inputCNFs)) = true := by
    simp only [checked, Bool.and_eq_true] at hw
    tauto
  have h := List.all_eq_true.mp hall _ (List.mem_range.mpr i.isLt)
  rw [eval_wire]
  by_cases hit : i.val = w.target
  · have hh : (i.val == w.target) = true := by simpa using hit
    simp only [signature, hh, ite_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h <;> rw [h] <;> simp [value, hit, and_comm]
  · have hh : (i.val == w.target) = false := by simpa using hit
    simp only [signature, hh, Bool.false_eq_true, ite_false, beq_iff_eq] at h
    rw [h]
    simp [value, hit]

def covered : Finset (Finset (Fin 13)) :=
  (witnesses.map (fun w => points w.zeros)).toFinset

theorem coverOfCount (hcert : witnesses.all checked = true) (hcount : covered.card = 715) :
    covered = Finset.univ.powersetCard 4 := by
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (countInputs w (List.all_eq_true.mp hcert w hw)).2.2⟩
  · rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hcount]
    decide

theorem singleError (w : Witness) (hw : checked w = true) (x : Input) (i : Fin 13)
    (hx : 9 ≤ (Finset.univ.filter fun v => x v = true).card) :
    (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) = true ↔
      clause x (lineBits i.val) ∧ (i.val = w.target → zeroSet x ≠ points w.zeros) := by
  rw [outputSpec w hw, hits_iff x _ (countInputs w hw).2.2 hx]

theorem affectedLineIsTrue (w : Witness) (hw : checked w = true) {x : Input} {i : Fin 13}
    (hz : zeroSet x = points w.zeros) (hi : i.val = w.target) : clause x (lineBits i.val) := by
  have hpos : 0 < ((points (lineBits w.target)) \ (points w.zeros)).card := by
    simp only [checked, Bool.and_eq_true, decide_eq_true_eq] at hw
    tauto
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  obtain ⟨hl,hout⟩ := Finset.mem_sdiff.mp hv
  refine ⟨v, ?_, ?_⟩
  · rw [hi]
    exact (Finset.mem_filter.mp hl).2
  · by_contra hn
    have hin : v ∈ zeroSet x := Finset.mem_compl.mpr (fun h => hn (Finset.mem_filter.mp h).2)
    exact hout (hz ▸ hin)

theorem errorAtExactlyOneOutput (w : Witness) (hw : checked w = true) (x : Input) (i : Fin 13)
    (hx : 9 ≤ (Finset.univ.filter fun v => x v = true).card) :
    (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) ≠
      @decide (clause x (lineBits i.val)) (Classical.propDecidable _) ↔ zeroSet x = points w.zeros ∧ i.val = w.target := by
  classical
  have rel := singleError w hw x i hx
  by_cases both : zeroSet x = points w.zeros ∧ i.val = w.target
  · have yes := affectedLineIsTrue w hw both.1 both.2
    have no : (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) = false :=
      Bool.eq_false_iff.mpr (fun h => (rel.mp h).2 both.2 both.1)
    exact ⟨fun _ => both, fun _ => by rw [no, decide_eq_true yes]; decide⟩
  · have allowed : i.val = w.target → zeroSet x ≠ points w.zeros := fun a b => both ⟨b,a⟩
    have heq : (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) =
        @decide (clause x (lineBits i.val)) (Classical.propDecidable _) := Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact rel.trans ⟨And.left, fun h => ⟨h, allowed⟩⟩)
    exact ⟨fun h => (h heq).elim, fun h => (both h).elim⟩

-- The bit masks are the cyclic lines in the project's gate problem.
theorem lineIdentity : ∀ i : Fin 13, points (lineBits i.val) =
    ({0,1,3,9} : Finset (Fin 13)).image (fun u => u + i) := by decide +kernel


def orbitOK (p : Packed) : Bool := (List.range 13).all fun t => checked (expand p t)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok0 : orbitOK pattern0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok1 : orbitOK pattern1 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok2 : orbitOK pattern2 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok3 : orbitOK pattern3 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok4 : orbitOK pattern4 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok5 : orbitOK pattern5 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok6 : orbitOK pattern6 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok7 : orbitOK pattern7 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok8 : orbitOK pattern8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok9 : orbitOK pattern9 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok10 : orbitOK pattern10 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok11 : orbitOK pattern11 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok12 : orbitOK pattern12 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok13 : orbitOK pattern13 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok14 : orbitOK pattern14 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok15 : orbitOK pattern15 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok16 : orbitOK pattern16 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok17 : orbitOK pattern17 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok18 : orbitOK pattern18 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok19 : orbitOK pattern19 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok20 : orbitOK pattern20 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok21 : orbitOK pattern21 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok22 : orbitOK pattern22 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok23 : orbitOK pattern23 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok24 : orbitOK pattern24 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok25 : orbitOK pattern25 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok26 : orbitOK pattern26 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok27 : orbitOK pattern27 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok28 : orbitOK pattern28 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok29 : orbitOK pattern29 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok30 : orbitOK pattern30 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok31 : orbitOK pattern31 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok32 : orbitOK pattern32 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok33 : orbitOK pattern33 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok34 : orbitOK pattern34 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok35 : orbitOK pattern35 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok36 : orbitOK pattern36 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok37 : orbitOK pattern37 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok38 : orbitOK pattern38 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok39 : orbitOK pattern39 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok40 : orbitOK pattern40 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok41 : orbitOK pattern41 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok42 : orbitOK pattern42 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok43 : orbitOK pattern43 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok44 : orbitOK pattern44 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok45 : orbitOK pattern45 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok46 : orbitOK pattern46 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok47 : orbitOK pattern47 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok48 : orbitOK pattern48 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok49 : orbitOK pattern49 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok50 : orbitOK pattern50 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok51 : orbitOK pattern51 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok52 : orbitOK pattern52 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok53 : orbitOK pattern53 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem ok54 : orbitOK pattern54 = true := by decide +kernel

theorem certificates : witnesses.all checked = true := by
  have hs : representatives.all orbitOK = true := by
    simp only [representatives, List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47, ok48, ok49, ok50, ok51, ok52, ok53, ok54, Bool.and_self]
  apply List.all_eq_true.mpr
  intro w hw
  obtain ⟨p,hp,hmember⟩ := List.mem_flatMap.mp hw
  obtain ⟨t,hindex,rfl⟩ := List.mem_map.mp hmember
  exact List.all_eq_true.mp (List.all_eq_true.mp hs p hp) t hindex


def bitPoints (m : BitVec 13) : Finset (Fin 13) :=
  Finset.univ.filter fun i => m.getLsbD i.val = true

theorem bitPoints_ofNat (m : Nat) : bitPoints (BitVec.ofNat 13 m) = points m := by
  ext i
  simp only [bitPoints, points, Finset.mem_filter, Finset.mem_univ, true_and, BitVec.getLsbD_ofNat, decide_eq_true i.isLt, Bool.true_and]

theorem bitPoints_inj : Function.Injective bitPoints := by
  intro a b he
  apply BitVec.eq_of_getLsbD_eq
  intro v hv
  apply Bool.eq_iff_iff.mpr
  have hm : (⟨v,hv⟩ : Fin 13) ∈ bitPoints a ↔ (⟨v,hv⟩ : Fin 13) ∈ bitPoints b := by rw [he]
  simpa only [bitPoints, Finset.mem_filter, Finset.mem_univ, true_and] using hm

def maskSet : Finset (BitVec 13) :=
  (witnesses.map fun w => BitVec.ofNat 13 w.zeros).toFinset

theorem covered_eq : covered = maskSet.image bitPoints := by
  ext s
  simp only [covered, maskSet, List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨_,⟨w,hw,rfl⟩,bitPoints_ofNat w.zeros⟩
  · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨w,hw,(bitPoints_ofNat w.zeros).symm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem maskCount : maskSet.card = 715 := by decide +kernel

theorem coverageCount : covered.card = 715 := by
  rw [covered_eq, Finset.card_image_of_injective _ bitPoints_inj, maskCount]

theorem wiring (w : Witness) (hw : checked w = true) :
    w.steps.zipIdx.all (fun (s,j) => s.left < 13+j && s.right < 13+j && s.left != s.right) = true ∧
    w.outputs.length = 13 ∧ w.outputs.all (· < 53) = true ∧ w.target < 13 := by
  simp only [checked, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  exact ⟨hw.1.1.1.1.1.1.2, hw.1.1.1.1.1.2, hw.1.1.1.1.2, hw.1.1.1.2⟩

theorem necessity_of_checks (hcert : witnesses.all checked = true) (hcard : covered.card = 715)
    (H : Finset (Fin 13)) (hH : H.card = 4) :
    ∃ w ∈ witnesses, points w.zeros = H ∧ w.steps.length = 40 ∧
      (w.steps.filter (·.meet)).length = 1 ∧ w.target < 13 ∧
      (∀ x : Input, 9 ≤ (Finset.univ.filter fun v => x v = true).card → ∀ i : Fin 13,
        (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) ≠
          @decide (clause x (lineBits i.val)) (Classical.propDecidable _) ↔ zeroSet x = H ∧ i.val = w.target) := by
  have hh : H ∈ covered := by
    rw [coverOfCount hcert hcard]
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hH⟩
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hh)
  have ok := List.all_eq_true.mp hcert w hw
  have hnum := countInputs w ok
  have hidx := (wiring w ok).2.2.2
  refine ⟨w,hw,eq,hnum.1,hnum.2.1,hidx,?_⟩
  intro x hx i
  rw [← eq]
  exact errorAtExactlyOneOutput w ok x i hx

theorem everyFourSet
    (H : Finset (Fin 13)) (hH : H.card = 4) :
    ∃ w ∈ witnesses, points w.zeros = H ∧ w.steps.length = 40 ∧
      (w.steps.filter (·.meet)).length = 1 ∧ w.target < 13 ∧
      (∀ x : Input, 9 ≤ (Finset.univ.filter fun v => x v = true).card → ∀ i : Fin 13,
        (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn x) ≠
          @decide (clause x (lineBits i.val)) (Classical.propDecidable _) ↔ zeroSet x = H ∧ i.val = w.target) :=
  necessity_of_checks certificates coverageCount H hH


def rowWithout (H : Finset (Fin 13)) : Input := fun v => decide (v ∉ H)

theorem support_rowWithout (H : Finset (Fin 13)) :
    (Finset.univ.filter fun v => rowWithout H v = true) = Hᶜ := by
  ext v
  simp [rowWithout]

theorem zeroSet_rowWithout (H : Finset (Fin 13)) : zeroSet (rowWithout H) = H := by
  rw [zeroSet, support_rowWithout, compl_compl]

theorem missesOmittedRow (H : Finset (Fin 13)) (hH : H.card = 4) :
    ∃ w ∈ witnesses, ∃ i : Fin 13, w.steps.length = 40 ∧
      (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD i.val 0)).eval (List.ofFn (rowWithout H)) ≠
        @decide (clause (rowWithout H) (lineBits i.val)) (Classical.propDecidable _) ∧
      ∀ y : Input, 9 ≤ (Finset.univ.filter fun v => y v = true).card → zeroSet y ≠ H →
        ∀ j : Fin 13, (Circuit.mk (w.steps.map Step.asGate) (w.outputs.getD j.val 0)).eval (List.ofFn y) =
          @decide (clause y (lineBits j.val)) (Classical.propDecidable _) := by
  obtain ⟨w,hw,_,hsize,_,hidx,hspec⟩ := everyFourSet H hH
  let i : Fin 13 := ⟨w.target, hidx⟩
  have hx : 9 ≤ (Finset.univ.filter fun v => rowWithout H v = true).card := by
    rw [support_rowWithout, Finset.card_compl, Fintype.card_fin, hH]
  refine ⟨w,hw,i,hsize,(hspec _ hx i).mpr ⟨zeroSet_rowWithout H,rfl⟩,?_⟩
  intro y hy hyH j
  by_contra wrong
  exact hyH ((hspec y hy j).mp wrong).1

end PlaneTestNecessity
