import PEqualNP.Defs.SearchCP
import Mathlib.Tactic.FinCases

/-!
An explicit 52-line cutting-planes refutation of PHP(4,3) in the project's
integer proof system. Each 14-line block establishes the capacity of one hole.
The four pigeon clauses and six additions finish the contradiction.
The desk challenge L-meta-9679 asks for a bound of 51.
-/

namespace PigeonholeFourThree

open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V := Fin 4 × Fin 3
abbrev F := PHP 4 3

def rowClause (i : Fin 4) : Clause V :=
  Finset.univ.image (fun j : Fin 3 => ((i, j), true))

def pairClause (i j : Fin 4) (h : Fin 3) : Clause V :=
  {((i, h), false), ((j, h), false)}

theorem rowMem (i : Fin 4) : rowClause i ∈ F := Or.inl ⟨i, rfl⟩
theorem pairMem (i j : Fin 4) (h : Fin 3) (hne : i ≠ j) : pairClause i j h ∈ F :=
  Or.inr ⟨i, j, h, hne, rfl⟩

def prev (xs : List (CPLine V)) (i : Nat) : CPLine V := xs.getD i (0, 0)

theorem prevMem (xs : List (CPLine V)) (i : Nat) (hi : i < xs.length) : prev xs i ∈ xs := by
  simp [prev, List.getD, List.getElem?_eq_getElem hi]

def start : List (CPLine V) := []

theorem validStart : IsCPDerivation F start := .nil

def lines0 : List (CPLine V) :=
  clauseCP (pairClause 0 1 0) :: start

theorem valid0 : IsCPDerivation F lines0 := .ax _ validStart (pairMem 0 1 0 (by decide))

def lines1 : List (CPLine V) :=
  clauseCP (pairClause 0 2 0) :: lines0

theorem valid1 : IsCPDerivation F lines1 := .ax _ valid0 (pairMem 0 2 0 (by decide))

def lines2 : List (CPLine V) :=
  clauseCP (pairClause 1 2 0) :: lines1

theorem valid2 : IsCPDerivation F lines2 := .ax _ valid1 (pairMem 1 2 0 (by decide))

def lines3 : List (CPLine V) :=
  ((prev lines2 2).1 + (prev lines2 1).1, (prev lines2 2).2 + (prev lines2 1).2) :: lines2

theorem valid3 : IsCPDerivation F lines3 := .add valid2 (prevMem lines2 2 (by decide)) (prevMem lines2 1 (by decide))

def lines4 : List (CPLine V) :=
  ((prev lines3 0).1 + (prev lines3 1).1, (prev lines3 0).2 + (prev lines3 1).2) :: lines3

theorem valid4 : IsCPDerivation F lines4 := .add valid3 (prevMem lines3 0 (by decide)) (prevMem lines3 1 (by decide))

def lines5 : List (CPLine V) :=
  (fun v => (prev lines4 0).1 v / 2, -((-(prev lines4 0).2) / 2)) :: lines4

theorem valid5 : IsCPDerivation F lines5 := by
  apply IsCPDerivation.div 2 valid4 (prevMem lines4 0 (by decide)) (by decide)
  rintro ⟨p, h⟩
  fin_cases p <;> fin_cases h
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩

def lines6 : List (CPLine V) :=
  ((2 : ℤ) • (prev lines5 0).1, (2 : ℤ) * (prev lines5 0).2) :: lines5

theorem valid6 : IsCPDerivation F lines6 := .mul 2 valid5 (prevMem lines5 0 (by decide))

def lines7 : List (CPLine V) :=
  clauseCP (pairClause 0 3 0) :: lines6

theorem valid7 : IsCPDerivation F lines7 := .ax _ valid6 (pairMem 0 3 0 (by decide))

def lines8 : List (CPLine V) :=
  clauseCP (pairClause 1 3 0) :: lines7

theorem valid8 : IsCPDerivation F lines8 := .ax _ valid7 (pairMem 1 3 0 (by decide))

def lines9 : List (CPLine V) :=
  clauseCP (pairClause 2 3 0) :: lines8

theorem valid9 : IsCPDerivation F lines9 := .ax _ valid8 (pairMem 2 3 0 (by decide))

def lines10 : List (CPLine V) :=
  ((prev lines9 3).1 + (prev lines9 2).1, (prev lines9 3).2 + (prev lines9 2).2) :: lines9

theorem valid10 : IsCPDerivation F lines10 := .add valid9 (prevMem lines9 3 (by decide)) (prevMem lines9 2 (by decide))

def lines11 : List (CPLine V) :=
  ((prev lines10 0).1 + (prev lines10 2).1, (prev lines10 0).2 + (prev lines10 2).2) :: lines10

theorem valid11 : IsCPDerivation F lines11 := .add valid10 (prevMem lines10 0 (by decide)) (prevMem lines10 2 (by decide))

def lines12 : List (CPLine V) :=
  ((prev lines11 0).1 + (prev lines11 2).1, (prev lines11 0).2 + (prev lines11 2).2) :: lines11

theorem valid12 : IsCPDerivation F lines12 := .add valid11 (prevMem lines11 0 (by decide)) (prevMem lines11 2 (by decide))

def lines13 : List (CPLine V) :=
  (fun v => (prev lines12 0).1 v / 3, -((-(prev lines12 0).2) / 3)) :: lines12

theorem valid13 : IsCPDerivation F lines13 := by
  apply IsCPDerivation.div 3 valid12 (prevMem lines12 0 (by decide)) (by decide)
  rintro ⟨p, h⟩
  fin_cases p <;> fin_cases h
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩

def lines14 : List (CPLine V) :=
  clauseCP (pairClause 0 1 1) :: lines13

theorem valid14 : IsCPDerivation F lines14 := .ax _ valid13 (pairMem 0 1 1 (by decide))

def lines15 : List (CPLine V) :=
  clauseCP (pairClause 0 2 1) :: lines14

theorem valid15 : IsCPDerivation F lines15 := .ax _ valid14 (pairMem 0 2 1 (by decide))

def lines16 : List (CPLine V) :=
  clauseCP (pairClause 1 2 1) :: lines15

theorem valid16 : IsCPDerivation F lines16 := .ax _ valid15 (pairMem 1 2 1 (by decide))

def lines17 : List (CPLine V) :=
  ((prev lines16 2).1 + (prev lines16 1).1, (prev lines16 2).2 + (prev lines16 1).2) :: lines16

theorem valid17 : IsCPDerivation F lines17 := .add valid16 (prevMem lines16 2 (by decide)) (prevMem lines16 1 (by decide))

def lines18 : List (CPLine V) :=
  ((prev lines17 0).1 + (prev lines17 1).1, (prev lines17 0).2 + (prev lines17 1).2) :: lines17

theorem valid18 : IsCPDerivation F lines18 := .add valid17 (prevMem lines17 0 (by decide)) (prevMem lines17 1 (by decide))

def lines19 : List (CPLine V) :=
  (fun v => (prev lines18 0).1 v / 2, -((-(prev lines18 0).2) / 2)) :: lines18

theorem valid19 : IsCPDerivation F lines19 := by
  apply IsCPDerivation.div 2 valid18 (prevMem lines18 0 (by decide)) (by decide)
  rintro ⟨p, h⟩
  fin_cases p <;> fin_cases h
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩

def lines20 : List (CPLine V) :=
  ((2 : ℤ) • (prev lines19 0).1, (2 : ℤ) * (prev lines19 0).2) :: lines19

theorem valid20 : IsCPDerivation F lines20 := .mul 2 valid19 (prevMem lines19 0 (by decide))

def lines21 : List (CPLine V) :=
  clauseCP (pairClause 0 3 1) :: lines20

theorem valid21 : IsCPDerivation F lines21 := .ax _ valid20 (pairMem 0 3 1 (by decide))

def lines22 : List (CPLine V) :=
  clauseCP (pairClause 1 3 1) :: lines21

theorem valid22 : IsCPDerivation F lines22 := .ax _ valid21 (pairMem 1 3 1 (by decide))

def lines23 : List (CPLine V) :=
  clauseCP (pairClause 2 3 1) :: lines22

theorem valid23 : IsCPDerivation F lines23 := .ax _ valid22 (pairMem 2 3 1 (by decide))

def lines24 : List (CPLine V) :=
  ((prev lines23 3).1 + (prev lines23 2).1, (prev lines23 3).2 + (prev lines23 2).2) :: lines23

theorem valid24 : IsCPDerivation F lines24 := .add valid23 (prevMem lines23 3 (by decide)) (prevMem lines23 2 (by decide))

def lines25 : List (CPLine V) :=
  ((prev lines24 0).1 + (prev lines24 2).1, (prev lines24 0).2 + (prev lines24 2).2) :: lines24

theorem valid25 : IsCPDerivation F lines25 := .add valid24 (prevMem lines24 0 (by decide)) (prevMem lines24 2 (by decide))

def lines26 : List (CPLine V) :=
  ((prev lines25 0).1 + (prev lines25 2).1, (prev lines25 0).2 + (prev lines25 2).2) :: lines25

theorem valid26 : IsCPDerivation F lines26 := .add valid25 (prevMem lines25 0 (by decide)) (prevMem lines25 2 (by decide))

def lines27 : List (CPLine V) :=
  (fun v => (prev lines26 0).1 v / 3, -((-(prev lines26 0).2) / 3)) :: lines26

theorem valid27 : IsCPDerivation F lines27 := by
  apply IsCPDerivation.div 3 valid26 (prevMem lines26 0 (by decide)) (by decide)
  rintro ⟨p, h⟩
  fin_cases p <;> fin_cases h
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩

def lines28 : List (CPLine V) :=
  clauseCP (pairClause 0 1 2) :: lines27

theorem valid28 : IsCPDerivation F lines28 := .ax _ valid27 (pairMem 0 1 2 (by decide))

def lines29 : List (CPLine V) :=
  clauseCP (pairClause 0 2 2) :: lines28

theorem valid29 : IsCPDerivation F lines29 := .ax _ valid28 (pairMem 0 2 2 (by decide))

def lines30 : List (CPLine V) :=
  clauseCP (pairClause 1 2 2) :: lines29

theorem valid30 : IsCPDerivation F lines30 := .ax _ valid29 (pairMem 1 2 2 (by decide))

def lines31 : List (CPLine V) :=
  ((prev lines30 2).1 + (prev lines30 1).1, (prev lines30 2).2 + (prev lines30 1).2) :: lines30

theorem valid31 : IsCPDerivation F lines31 := .add valid30 (prevMem lines30 2 (by decide)) (prevMem lines30 1 (by decide))

def lines32 : List (CPLine V) :=
  ((prev lines31 0).1 + (prev lines31 1).1, (prev lines31 0).2 + (prev lines31 1).2) :: lines31

theorem valid32 : IsCPDerivation F lines32 := .add valid31 (prevMem lines31 0 (by decide)) (prevMem lines31 1 (by decide))

def lines33 : List (CPLine V) :=
  (fun v => (prev lines32 0).1 v / 2, -((-(prev lines32 0).2) / 2)) :: lines32

theorem valid33 : IsCPDerivation F lines33 := by
  apply IsCPDerivation.div 2 valid32 (prevMem lines32 0 (by decide)) (by decide)
  rintro ⟨p, h⟩
  fin_cases p <;> fin_cases h
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩

def lines34 : List (CPLine V) :=
  ((2 : ℤ) • (prev lines33 0).1, (2 : ℤ) * (prev lines33 0).2) :: lines33

theorem valid34 : IsCPDerivation F lines34 := .mul 2 valid33 (prevMem lines33 0 (by decide))

def lines35 : List (CPLine V) :=
  clauseCP (pairClause 0 3 2) :: lines34

theorem valid35 : IsCPDerivation F lines35 := .ax _ valid34 (pairMem 0 3 2 (by decide))

def lines36 : List (CPLine V) :=
  clauseCP (pairClause 1 3 2) :: lines35

theorem valid36 : IsCPDerivation F lines36 := .ax _ valid35 (pairMem 1 3 2 (by decide))

def lines37 : List (CPLine V) :=
  clauseCP (pairClause 2 3 2) :: lines36

theorem valid37 : IsCPDerivation F lines37 := .ax _ valid36 (pairMem 2 3 2 (by decide))

def lines38 : List (CPLine V) :=
  ((prev lines37 3).1 + (prev lines37 2).1, (prev lines37 3).2 + (prev lines37 2).2) :: lines37

theorem valid38 : IsCPDerivation F lines38 := .add valid37 (prevMem lines37 3 (by decide)) (prevMem lines37 2 (by decide))

def lines39 : List (CPLine V) :=
  ((prev lines38 0).1 + (prev lines38 2).1, (prev lines38 0).2 + (prev lines38 2).2) :: lines38

theorem valid39 : IsCPDerivation F lines39 := .add valid38 (prevMem lines38 0 (by decide)) (prevMem lines38 2 (by decide))

def lines40 : List (CPLine V) :=
  ((prev lines39 0).1 + (prev lines39 2).1, (prev lines39 0).2 + (prev lines39 2).2) :: lines39

theorem valid40 : IsCPDerivation F lines40 := .add valid39 (prevMem lines39 0 (by decide)) (prevMem lines39 2 (by decide))

def lines41 : List (CPLine V) :=
  (fun v => (prev lines40 0).1 v / 3, -((-(prev lines40 0).2) / 3)) :: lines40

theorem valid41 : IsCPDerivation F lines41 := by
  apply IsCPDerivation.div 3 valid40 (prevMem lines40 0 (by decide)) (by decide)
  rintro ⟨p, h⟩
  fin_cases p <;> fin_cases h
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(0 : ℤ), by decide⟩
  · exact ⟨(-1 : ℤ), by decide⟩

def lines42 : List (CPLine V) :=
  clauseCP (rowClause 0) :: lines41

theorem valid42 : IsCPDerivation F lines42 := .ax _ valid41 (rowMem 0)

def lines43 : List (CPLine V) :=
  clauseCP (rowClause 1) :: lines42

theorem valid43 : IsCPDerivation F lines43 := .ax _ valid42 (rowMem 1)

def lines44 : List (CPLine V) :=
  clauseCP (rowClause 2) :: lines43

theorem valid44 : IsCPDerivation F lines44 := .ax _ valid43 (rowMem 2)

def lines45 : List (CPLine V) :=
  clauseCP (rowClause 3) :: lines44

theorem valid45 : IsCPDerivation F lines45 := .ax _ valid44 (rowMem 3)

def lines46 : List (CPLine V) :=
  ((prev lines45 3).1 + (prev lines45 2).1, (prev lines45 3).2 + (prev lines45 2).2) :: lines45

theorem valid46 : IsCPDerivation F lines46 := .add valid45 (prevMem lines45 3 (by decide)) (prevMem lines45 2 (by decide))

def lines47 : List (CPLine V) :=
  ((prev lines46 0).1 + (prev lines46 2).1, (prev lines46 0).2 + (prev lines46 2).2) :: lines46

theorem valid47 : IsCPDerivation F lines47 := .add valid46 (prevMem lines46 0 (by decide)) (prevMem lines46 2 (by decide))

def lines48 : List (CPLine V) :=
  ((prev lines47 0).1 + (prev lines47 2).1, (prev lines47 0).2 + (prev lines47 2).2) :: lines47

theorem valid48 : IsCPDerivation F lines48 := .add valid47 (prevMem lines47 0 (by decide)) (prevMem lines47 2 (by decide))

def lines49 : List (CPLine V) :=
  ((prev lines48 0).1 + (prev lines48 35).1, (prev lines48 0).2 + (prev lines48 35).2) :: lines48

theorem valid49 : IsCPDerivation F lines49 := .add valid48 (prevMem lines48 0 (by decide)) (prevMem lines48 35 (by decide))

def lines50 : List (CPLine V) :=
  ((prev lines49 0).1 + (prev lines49 22).1, (prev lines49 0).2 + (prev lines49 22).2) :: lines49

theorem valid50 : IsCPDerivation F lines50 := .add valid49 (prevMem lines49 0 (by decide)) (prevMem lines49 22 (by decide))

def lines51 : List (CPLine V) :=
  ((prev lines50 0).1 + (prev lines50 9).1, (prev lines50 0).2 + (prev lines50 9).2) :: lines50

theorem valid51 : IsCPDerivation F lines51 := .add valid50 (prevMem lines50 0 (by decide)) (prevMem lines50 9 (by decide))

theorem firstHole14 : ∃ π : List (CPLine V), IsCPDerivation F π ∧ π.length = 14 ∧
    ((fun v : V => if v.2 = 0 then -1 else 0), (-1 : ℤ)) ∈ π := by
  refine ⟨lines13, valid13, by decide, ?_⟩
  have h := prevMem lines13 0 (by decide)
  have eq : prev lines13 0 = ((fun v : V => if v.2 = 0 then -1 else 0), (-1 : ℤ)) := by
    apply Prod.ext
    · funext v
      rcases v with ⟨p, h⟩
      fin_cases p <;> fin_cases h <;> decide
    · decide
  rwa [eq] at h

theorem refutation52 : ∃ π : List (CPLine V), IsCPRefutation F π ∧ π.length = 52 := by
  refine ⟨lines51, ⟨valid51, ?_⟩, by decide⟩
  have h := prevMem lines51 0 (by decide)
  have eq : prev lines51 0 = ((0 : V → ℤ), (1 : ℤ)) := by
    apply Prod.ext
    · funext v
      rcases v with ⟨p, h⟩
      fin_cases p <;> fin_cases h <;> decide
    · decide
  rwa [eq] at h

end PigeonholeFourThree
