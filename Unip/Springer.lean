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

def to_dSymbol_aux (p : Partition') : Symbol' :=  by
  let p' := if (Even <| Multiset.card p) then p else add_zero 0 p
  let L : List ℕ := (Multiset.sort (· ≤ ·) p').enum.map (fun x => x.1+x.2)
  let A' := (L.filter (· %2 == 1)).map (· /2)
  let B' := (L.filter (· %2 == 0)).map (· /2)
  exact {
    A := List.toFinset <| [0]++ A'.enum.map (fun x => x.1+x.2+2)
    B := List.toFinset <| B'.enum.map (fun x => x.1+x.2+1)
  }

#eval to_dSymbol_aux {1,5,3,8,8,8,9}

#eval to_dSymbol_aux {0,2,2,4}



end Partition'


/- The interval of a List ℕ is the the set of longest string of the form {i, i+1, i+2,...,j} in the list
The following function compute the interval
-/
def interval (L: List ℕ) : List (List ℕ):=
  match L with
  | [] => []
  | [a] => [[a]]
  | a::b::L' => if a+1 = b then
    let I' := interval (b::L')
    match I'.head? with
    | none => [[a]]
    | some b => (a::b)::I'.tail
    else [a]::interval (b::L')


#eval interval [0,1,2,3,5,6,7,9,10,11, 20,21,22]


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
def Springer.dist.C_aux (p : Partition') : Symbol' :=
  if (Even <| Multiset.card p) then to_dSymbol_aux p else
  to_dSymbol_aux <| insert 0 p

def Springer.dist.C' (p : Partition') (hC : isTypeC p): SkippingSymbol' := ⟨Springer.dist.C_aux p, sorry,sorry,sorry,sorry⟩


def Springer.dist.C (p : Partition') (hC : isTypeC p): SkippingSymbol := Springer.dist.C' p hC

#eval Springer.dist.C {0,2,2,4} (by decide)

def interval.C (p: Partition') : List (List ℕ) := by
  obtain ⟨A,B⟩ := Springer.dist.C_aux p
  exact List.filter (¬ 0∈ · ) <| interval <| ((A ∪ B) \ (A ∩ B)).sort (· ≤ ·)


def interval0.C (p: Partition') : List (List ℕ) := by
  obtain ⟨A,B⟩ := Springer.dist.C_aux p
  exact List.filter ( 0 ∈ · ) <| interval <| ((A ∪ B) \ (A ∩ B)).sort (· ≤ ·)


#eval interval.C {0,2,2,4}

#eval component.C {0,2,2,4}

lemma component_bijective_interval (p : Partition') (hC : isTypeC p) : (interval.C p).length = (component.C p).card:= by sorry

/-
Select the elements in the list c according to the Zip list
-/
def select (Z : List (ℕ × List ℕ)) (c : Finset ℕ) : Finset ℕ := Z.filterMap (fun x => if x.1 ∈ c then some x.2 else none) |> List.join |> List.toFinset

/-unselction the elements in the list c according to the Zip list -/
def unselect (Z : List (ℕ × List ℕ)) (c : Finset ℕ) : Finset ℕ := Z.filterMap (fun x => if x.1 ∉ c then some x.2 else none) |> List.join |> List.toFinset

/-
Here c will be a Finset ℕ, which represents an element in the component group of O_p.
-/
def Springer.C'_aux (p : Partition') (hC : isTypeC p) (c : Finset ℕ) : Symbol' := by
  -- First step, find the distingushed symbol correspondes to p
  let dS := Springer.dist.C' p hC
  -- Second step, find the interval correspondes p
  let I := interval.C p
  let I0 := interval0.C p
  -- Third step, find the component group of O_p
  let C : Finset ℕ := component.C p
  -- Zip the component group with the interval
  let Z := List.zip (C.sort (· ≤ ·)) I
  let A := (select Z c ∩ dS.A) ∪ (unselect Z c ∩ dS.B) ∪ (I0.join.toFinset ∩ dS.A) ∪ (dS.A ∩ dS.B)
  let B := (select Z c ∩ dS.B) ∪ (unselect Z c ∩ dS.A) ∪ (I0.join.toFinset ∩ dS.B) ∪ (dS.A ∩ dS.B)
  exact ⟨A,B⟩


def Springer.C' (p : Partition') (hC : isTypeC p) (c : Finset ℕ) : SkippingSymbol' :=
  ⟨Springer.C'_aux p hC c, sorry, sorry, sorry, sorry⟩


def Springer.C (p : Partition') (hC : isTypeC p) (c : Finset ℕ) : SkippingSymbol := Quot.mk _ (Springer.C' p hC c)

/-
This is computable version of the Springer correspondence for type C
-/
def Springer.C'' (p : Partition')  (c : Finset ℕ) : Option SkippingSymbol :=
  if h : isTypeC p
  then some (Springer.C p h c)
  else none



end Springer.C

section test

open Lean Lean.Elab Command Term Meta
syntax (name := springer) "#checkSpringerC" : command -- declare the syntax


syntax "SpringerC " term (", " term)?: term

macro_rules
  | `(SpringerC $x) => `(Springer.C $x (by decide) {})
  | `(SpringerC $x, $c) => `(Springer.C $x (by decide) $c)



def checkSpringerC (p : Partition') (c : Finset ℕ) :=
  match Springer.C'' p c with
  | none => IO.println "The partition is not of type C"
  | some s => do
    IO.println s!"Local system [{repr p} |{repr c}] =>  SSymbol {repr s}"
    --IO.println s!" ssymbol {repr <| Springer.dist.C_aux p}"
    --IO.println s!" interval {repr <|interval.C p}"

#eval checkSpringerC {0,0,1,1,4} {4}
#eval checkSpringerC {1,1,4} {}
#eval checkSpringerC {2,2,2} {2}
#eval checkSpringerC {2,2,2} {}
#eval checkSpringerC {1,1,2,2} {2}
#eval checkSpringerC {1,1,2,2} {}
#eval checkSpringerC {1,1,1,1,2} {2}
#eval checkSpringerC {1,1,1,1,2} {}

end test
