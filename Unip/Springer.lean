import Init.Data.Repr
import Mathlib.Data.List.Range
import Mathlib.Data.Multiset.Range
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Multiset.Nodup
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Linarith.Frontend

import Lean

import Unip.Auxi
import Unip.Symbol
import Unip.Partition

open Multiset.Nat




abbrev Partition' := Multiset ℕ

namespace Partition'


/-
The Springer map for type B is definied as follows:
1.  Arrange the partition p as
 p_1 ≤  p_2 ≤ ... ≤  p_{2m}
2.  Let {2y_1 < ... <  2 y_{m}} ∪ {2y'_1+1 < 2y'_2 +1 < ... < 2y'_{m}} = {p_1, p_2+1, p_3+2, ... , p_{2m+1}+2m-1}
3. The Springer map is defined as
  A = {2y'_1+2, 2y'_2+3, ... , 2y_{m+1}+m+1}
  B = {2y'_1+1, 2y'_2+2, ... , 2y'_{m}+m}
-/

def to_dSymbolC_aux (p : Partition') : Symbol' :=  by
  let p' := if (Even <| Multiset.card p) then p else
  add_zero 1 p
  let L : List ℕ := (Multiset.sort (· ≤ ·) p').enum.map (fun x => x.1+x.2)
  let Y := (L.filter (· %2 == 0)).map (· /2)
  let Y' := (L.filter (· %2 == 1)).map (· /2)
  exact {
    A := List.toFinset <| [0] ++ (Y'.enum.map (fun x => x.1+x.2+2))
    B := List.toFinset <| Y.enum.map (fun x => x.1+x.2+1)
  }

#eval to_dSymbolC_aux {1,5,3,8,8,8,9}

#eval to_dSymbolC_aux {0,2,2,4}

/-
The Springer map for type B is definied as follows:
1.  Arrange the partition p as
 p_1 ≤  p_2 ≤ ... ≤  p_{2m+1}
2.  Let {2y_1 < ... <  2 y_{m+1}} ∪ {2y'_1+1 < 2y'_2 +1 < ... < 2y'_{m}} = {p_1, p_2+1, p_3+2, ... , p_{2m+1}+2m}
3. The Springer map is defined as
  A = {2y_1, 2y_2+1, ... , 2y_{m+1}+m}
  B = {2y'_1, 2y'_2+1, ... , 2y'_{m}+m-1}

The Springer map for type D is definied as follows:
1.  Arrange the partition p as
 p_1 ≤  p_2 ≤ ... ≤  p_{2m}
2.  Let {2y_1 < ... <  2 y_{m+1}} ∪ {2y'_1+1 < 2y'_2 +1 < ... < 2y'_{m}} = {p_1, p_2+1, p_3+2, ... , p_{2m}+2m-1}
3. The Springer map is defined as
  A = {2y_1, 2y_2+1, ... , 2y_{m}+m-1}
  B = {2y'_1, 2y'_2+1, ... , 2y'_{m}+m-1}
-/
def to_dSymbolBD_aux (p : Partition') : Symbol' :=  by
  let N := p.sum
  let p' := if (Even  <| N + Multiset.card p) then p else add_zero 1 p
  let L : List ℕ := (Multiset.sort (· ≤ ·) p').enum.map (fun x => x.1+x.2)
  let Y := (L.filter (· %2 == 0)).map (· /2)
  let Y' := (L.filter (· %2 == 1)).map (· /2)
  exact {
    A := List.toFinset <| Y'.enum.map (fun x => x.1+x.2)
    B := List.toFinset <| Y.enum.map (fun x => x.1+x.2)
  }


end Partition'

section Springer.BD
open Partition'

/-
Our component group is the component group for the full orthogonal group, which consists of all the odd parts of the partition.
-/
def component.BD (p : Partition') : Finset ℕ := (p.filter (fun x => x % 2 == 1)).toFinset



def interval.BD(p: Partition') : List (List ℕ) := by
  obtain ⟨A,B⟩ := p.to_dSymbolBD_aux
  exact interval <| ((A ∪ B) \ (A ∩ B)).sort (· ≤ ·)

lemma component_bijective_intervalBD (p : Partition') : (interval.BD p).length = (component.BD p).card:= by sorry


/-
Here c will be a Finset ℕ, which represents an element in the component group of O_p.
-/
def Springer.BD'_aux (p : Partition') (c : Finset ℕ) : Symbol' := by
  -- First step, find the distingushed symbol correspondes to p
  obtain ⟨A',B'⟩:= p.to_dSymbolBD_aux
  -- Second step, find the interval correspondes p
  let I := interval.BD p
  -- Third step, find the component group of O_p
  let C : Finset ℕ := component.BD p
  -- Zip the component group with the interval
  let Z := List.zip (C.sort (· ≤ ·)) I
  let A := ((select Z c) ∩ A') ∪ ((unselect Z c) ∩ B') ∪ (A' ∩ B')
  let B := ((select Z c) ∩ B') ∪ ((unselect Z c) ∩ A') ∪ (A' ∩ B')
  exact ⟨A,B⟩


def Springer.BD' (p : Partition') (hBD : isTypeBD p) (c : Finset ℕ) : SkippingSymbolBD' :=
  ⟨Springer.BD'_aux p c, sorry, sorry⟩


def Springer.BD (p : Partition') (hBD : isTypeBD p) (c : Finset ℕ) : SkippingSymbolBD := Quot.mk _ (Springer.BD' p hBD c)

/-
This is computable version of the Springer correspondence for type C
-/
def Springer.BD'' (p : Partition')  (c : Finset ℕ) : Option SkippingSymbolBD :=
  if h : isTypeBD p
  then some (Springer.BD p h c)
  else none

end Springer.BD


section Springer.C
open Partition'

/-
The component group consists of finite set of all non-zero even parts of the partition.
-/
def component.C (p : Partition') : Finset ℕ := (p.filter (fun x => (¬ x=0) && x % 2 == 0)).toFinset

#eval component.C {0,2,2,4,7,7,8,8,8}


/-
From a partition of type C, it will generate a distinguished SkippingSymbol of type C
-/


-- def Springer.dist.C' (p : Partition') (hC : isTypeC p): SkippingSymbolC' := ⟨⟨p.to_dSymbolC_aux, sorry,sorry⟩,sorry,sorry⟩


-- def Springer.dist.C (p : Partition') (hC : isTypeC p): SkippingSymbolC := Springer.dist.C' p hC


-- #eval Springer.dist.C {0,2,2,4} (by decide)

def interval.C (p: Partition') : List (List ℕ) := by
  obtain ⟨A,B⟩ := p.to_dSymbolC_aux
  exact List.filter (¬ 0∈ · ) <| interval <| ((A ∪ B) \ (A ∩ B)).sort (· ≤ ·)


def interval0.C (p: Partition') : List (List ℕ) := by
  obtain ⟨A,B⟩ := p.to_dSymbolC_aux
  exact List.filter ( 0 ∈ · ) <| interval <| ((A ∪ B) \ (A ∩ B)).sort (· ≤ ·)


#eval component.C {0,2,2,4}

lemma component_bijective_intervalC (p : Partition') (hC : isTypeC p) : (interval.C p).length = (component.C p).card:= by sorry

/-
Here c will be a Finset ℕ, which represents an element in the component group of O_p.
-/
def Springer.C'_aux (p : Partition') (c : Finset ℕ) : Symbol' := by
  -- First step, find the distingushed symbol correspondes to p
  let dS := p.to_dSymbolC_aux
  -- Second step, find the interval correspondes p
  let I := interval.C p
  let I0 := interval0.C p
  -- Third step, find the component group of O_p
  let C : Finset ℕ := component.C p
  -- Zip the component group with the interval
  let Z := List.zip (C.sort (· ≤ ·)) I
  let A := ((select Z c) ∩ dS.A) ∪ ((unselect Z c) ∩ dS.B) ∪ (I0.join.toFinset ∩ dS.A) ∪ (dS.A ∩ dS.B)
  let B := ((select Z c) ∩ dS.B) ∪ ((unselect Z c) ∩ dS.A) ∪ (I0.join.toFinset ∩ dS.B) ∪ (dS.A ∩ dS.B)
  exact ⟨A,B⟩


def Springer.C' (p : Partition') (hC : isTypeC p) (c : Finset ℕ) : SkippingSymbolC' :=
  ⟨⟨Springer.C'_aux p c, sorry, sorry⟩, sorry, sorry⟩


def Springer.C (p : Partition') (hC : isTypeC p) (c : Finset ℕ) : SkippingSymbolC := Quot.mk _ (Springer.C' p hC c)

/-
This is computable version of the Springer correspondence for type C
-/
def Springer.C'' (p : Partition')  (c : Finset ℕ) : Option SkippingSymbolC :=
  if h : isTypeC p
  then some (Springer.C p h c)
  else none



end Springer.C


syntax "SpringerC " term (", " term)?: term

macro_rules
  | `(SpringerC $x) => `(Springer.C $x (by decide) {})
  | `(SpringerC $x, $c) => `(Springer.C $x (by decide) $c)


syntax "SpringerBD " term (", " term)?: term

macro_rules
  | `(SpringerBD $x) => `(Springer.BD $x (by decide) {})
  | `(SpringerBD $x, $c) => `(Springer.BD $x (by decide) $c)


section test


def checkSpringerC (p : Partition') (c : Finset ℕ) :=
  match Springer.C'' p c with
  | none => IO.println "The partition is not of type C"
  | some s => do
    IO.println s!"Local system [{repr p} |{repr c}] =>  SSymbol {repr s}"
    --IO.println s!" ssymbol {repr <| Springer.dist.C_aux p}"
    IO.println s!" interval {repr <|interval.C p}"

#eval checkSpringerC {0,0,1,1,4} {4}
#eval checkSpringerC {1,1,4} {}
#eval checkSpringerC {2,2,2} {2}
#eval checkSpringerC {2,2,2} {}
#eval checkSpringerC {1,1,2,2} {2}
#eval checkSpringerC {1,1,2,2} {}
#eval checkSpringerC {1,1,1,1,2} {2}
#eval checkSpringerC {1,1,1,1,2} {}
#eval checkSpringerC {1,1,1,1,1,1} {}

end test
