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

import Unip.Auxi

open BigOperators

open Multiset

/-
 We follow Lusztig's Intersection cohomology complexes on reductive groups Sectio 10-12

 A symbole of type C is a orderd pair of finite set of natural numbers (A,B) where A is a multiset of natural numbers and B is a multiset of positive natural numbers
 such that
 (1) ∀ i , {i, i+1} not contained in A nor in B
 (2) |A| + |B| is odd
-/

@[ext]
structure Bipartition' where
  A : Multiset Nat
  B : Multiset Nat
  deriving BEq, DecidableEq, Hashable

namespace Bipartition'
instance  reprBipartition' : Repr Bipartition' where
  reprPrec s _ :=
      Std.Format.join ["{", repr s.A, ";", repr s.B, "}"]


def remove_zero (S : Bipartition') : Bipartition' := by
  let pos := fun A : Multiset ℕ => A.filter (0 < ·)
  exact ⟨pos S.A, pos S.B⟩

def size (S : Bipartition') := S.A.sum + S.B.sum

end Bipartition'


open Multiset.Nat
@[ext]
structure Symbol' where
  A : Finset ℕ
  B : Finset ℕ
  deriving Inhabited, BEq, DecidableEq, Hashable

namespace Symbol'

def size (S : Symbol') : ℕ := S.A.card + S.B.card

instance coeSymbol' : Coe (Finset ℕ × Finset ℕ) Symbol' where
  coe := fun ⟨A,B⟩ => ⟨A,B⟩


instance  reprSymbol' : Repr Symbol' where
  reprPrec s _ :=
      Std.Format.join ["(", repr s.A.1, ";", repr s.B.1, ")"]

def defect (S : Symbol') : ℤ :=  S.A.card - S.B.card

/-
Let Ψ_{2n,d} is a Skipping symbol of type C and has N=2n and defect d (odd).
There is a bijection
Ψ_{2n,d} → Ψ_{2n+d(d-1),d} (with d odd)
For d ≥ 1, the map is given by
(A,B) ↦ ({0,2,4,...,2d-4} ∪ (A+2d-2), B)
For d ≤ -1
(A,B) ↦ ( A, {1, 3, 5, ... , 1-2d} ∪ B).
-/
/-
This function shift the defect by d
We only use the case where By assumption d should be odd)
-/
def shift_defectC_aux (d :ℤ) (S : Symbol') : Symbol' :=
  if h: d ≥ 0 then
    let d' := d.toNat
    let A := (List.range d' |>.map (· * 2) |>.toFinset) ∪
              (Finset.map ⟨(· + 2*d'), Nat.add_inj⟩ S.A)
    let B := S.B
    ⟨A,B⟩
  else
    let d' := (-d).toNat
    let A := S.A
    let B := (List.range d' |>.map (fun x => 2*x + 1) |>.toFinset) ∪
      (Finset.map ⟨(· + (2*d')), Nat.add_inj⟩ S.B)
    ⟨A,B⟩

/-This function shift the defect to d-/
def shift_defectC (d : ℤ) (S : Symbol')  : Symbol' :=
  shift_defectC_aux (d - S.defect) S


def regulate_defectC (S : Symbol') : Symbol' :=
  shift_defectC 1 S

/-
This function shift the defect by d
-/
def shift_defectBD_aux (d : ℤ) (S : Symbol')  : Symbol' :=
  if d ≥ 0 then
    let d' := d.toNat
    let A := (List.range d' |>.map (· * 2) |>.toFinset) ∪
              (Finset.map ⟨(· + 2*d'), Nat.add_inj⟩ S.A)
    let B := S.B
    ⟨A,B⟩
  else
    let d' := (-d).toNat
    let A := S.A
    let B := (List.range (d') |>.map (· * 2) |>.toFinset) ∪
      (Finset.map ⟨(· + 2*d'), Nat.add_inj⟩ S.B)
    ⟨A,B⟩

/-
This function shift the defect to d
-/
def shift_defectBD (d : ℤ) (S : Symbol')  : Symbol' :=
  let d0 := S.defect
  shift_defectBD_aux (d-d0) S

def regulate_defectBD (S : Symbol') : Symbol' :=
  let d := S.defect
  if d%2 = 0 then
    shift_defectBD 0 S
  else
    shift_defectBD 1 S


def shift_left_C (S : Symbol') (h : 0∈ S.A ∧ 1∈ S.B) : Symbol' where
  A := Finset.image (· - 2) (S.A.erase 0)
  B := Finset.image (· - 2) (S.B.erase 1)


def shift_left_BD (S : Symbol') (h : 0∈ S.A ∧ 0∈ S.B) : Symbol' where
  A := Finset.image (· - 2) (S.A.erase 0)
  B := Finset.image (· - 2) (S.B.erase 0)



lemma shift_left_C_size_lt (S : Symbol') (h : 0∈ S.A ∧ 1∈ S.B) : (shift_left_C S h).size < S.size := by
  simp_rw [size,shift_left_C]
  have : (Finset.image (· -2) (S.A.erase 0) |>.card) ≤ (S.A.erase 0).card := Finset.card_image_le
  have : (Finset.image (· -2) (S.B.erase 1) |>.card) ≤ (S.B.erase 1).card := Finset.card_image_le
  have : (S.A.erase 0).card < S.A.card:= Finset.card_erase_lt_of_mem h.1
  have : (S.B.erase 1).card < S.B.card:= Finset.card_erase_lt_of_mem h.2
  linarith

lemma shift_left_BD_size_lt (S : Symbol') (h : 0∈ S.A ∧ 0∈ S.B) : (shift_left_BD S h).size < S.size := by
  simp_rw [size,shift_left_BD]
  have : (Finset.image (· -2) (S.A.erase 0) |>.card) ≤ (S.A.erase 0).card := Finset.card_image_le
  have : (Finset.image (· -2) (S.B.erase 0) |>.card) ≤ (S.B.erase 0).card := Finset.card_image_le
  have : (S.A.erase 0).card < S.A.card:= Finset.card_erase_lt_of_mem h.1
  have : (S.B.erase 0).card < S.B.card:= Finset.card_erase_lt_of_mem h.2
  linarith




def toReducedC (S : Symbol') : Symbol'
:= if h : (0 ∈ S.A) ∧  (1 ∈ S.B)
  then toReducedC (shift_left_C S h)
  else S
termination_by S.size
decreasing_by
  exact shift_left_C_size_lt S h

def toReducedBD (S : Symbol') : Symbol' := if h : 0 ∈ S.A ∧  0 ∈ S.B then toReducedBD (shift_left_BD S h)  else S
termination_by S.size
decreasing_by
  exact shift_left_BD_size_lt S h



#eval shift_defectC 3 ⟨{0,3,5},{1,3}⟩
#eval shift_defectC (-2) ⟨{0,3,5},{1,3}⟩

#eval ⟨{0,3,5,9},{1,3,7}⟩ |> toReducedC
#eval ⟨{0,3,5,9},{1,3,7}⟩ |> shift_defectC   (-3:ℤ) |> toReducedC
#eval ⟨{0,3,5,9},{1,3,7}⟩ |> shift_defectC   (-9:ℤ) |> regulate_defectC |> toReducedC
#eval ⟨{0,3,5},{1,3}⟩ |> toReducedBD
#eval ⟨{0,3,5},{1,3}⟩ |> regulate_defectBD |> toReducedBD
#eval ⟨{0,3,5},{1,7}⟩ |> shift_defectBD 3
#eval ⟨{0,3,5},{1,3}⟩ |> shift_defectBD (11) |> regulate_defectBD |> toReducedBD

def remove_zero (A : Multiset ℕ) : Multiset ℕ := A.filter (0 ≠ ·)


/-
This function treats the Type C. One can see that
the algorithm is independent of the sign of the defect.


But Shoji claim s that if the defect is negative, one should switch the partition!
See, Remark 5.8, in  Shoji, (1997). Unipotent Characters of Finite Classical Groups, Finite Reductive Groups-Related Structures and Representations.

From theta's perspective, this is not a good choice.
We adopt Lusztig's normalization.
-/
def CSymbol_toBP (S : Symbol') : Bipartition' := by
  have ⟨A',B'⟩ := S
  let A := List.zip (A'.sort (· ≤ ·)) (List.range A'.card) |>.map (fun x => x.1 - 2*x.2)
  let B := List.zip (B'.sort (· ≤ ·)) (List.range B'.card) |>.map (fun x => x.1 - 2*x.2-1)
  /-
  if S.defect >0 then
    exact ⟨A,B⟩
  else
    -- If defect <0, then switch left and right partitions
    exact ⟨B,A⟩
  -/
  exact ⟨A,B⟩

/-
This function treats the Type BD defect 0, 1 case
-/
def BDSymbol_toBP (S : Symbol') : Bipartition' := by
  --let S':= shift_defectBD 0 S
  have ⟨A',B'⟩ := S
  let A := List.zip (A'.sort (· ≤ ·)) (List.range A'.card) |>.map (fun x => x.1 - 2*x.2)
  let B := List.zip (B'.sort (· ≤ ·)) (List.range B'.card) |>.map (fun x => x.1 - 2*x.2)
  exact ⟨A,B⟩
  --if S.defect <  0 then
  --  exact ⟨A,B⟩
  --else
  --exact ⟨B,A⟩


#eval ⟨{0,3,5,7}, {1, 4,5}⟩ |> shift_defectC 4 |> CSymbol_toBP |>.remove_zero

#eval ⟨{0,3,5,7}, {1, 4,5}⟩ |> shift_defectC (-3) |> CSymbol_toBP |>.remove_zero


end Symbol'

/-
A Skipping Symbol of type BD is a Symbol of type C such that
  ∀ i , {i, i+1} not contained in A nor in B
-/
@[ext]
structure SkippingSymbol' extends Symbol' where
  non_adjA : ¬ haspair' (· + 1) A
  non_adjB : ¬ haspair' (· + 1) B
  deriving BEq, DecidableEq, Hashable


macro "mkSSymbol'" x:term ";" y:term : term  =>  `(({A := $x, B:=$y, non_adjA:= (by decide),non_adjB :=(by decide)}:SkippingSymbol'))


namespace SkippingSymbol'

instance  reprSkippingSymbol' : Repr SkippingSymbol' where
  reprPrec s _ := repr s.toSymbol'

#eval mkSSymbol' {0,2,4};{5,7,9}

def size (S : SkippingSymbol') : ℕ := S.A.card + S.B.card

def defect (S : SkippingSymbol') : ℤ :=  S.A.card - S.B.card

def N_C (S : SkippingSymbol') : ℕ  :=
2 *(∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ))   -  S.size*(S.size-1)

lemma N.C_def (S : SkippingSymbol') :  2*(∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ))   = S.N_C + S.size*(S.size-1) := sorry


/-
The N (dimension of standard representation)
of a SkkipingSymbol of type C is given by
∑ a ∈ A, a + ∑ b ∈ B, b  = 1/2 N +  1/2 (|A| + |B|)(|A| + |B| - 1)
-/
def N_BD (S : SkippingSymbol') : ℕ  := 2*(
∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ))   - ((S.size-1)^2-1)


def rank_C (S : SkippingSymbol') : ℕ := S.N_C/2


/-
The N (dimension of standard representation)
of a SkkipingSymbol of type BD is given by
∑ a ∈ A, a + ∑ b ∈ B, b  = 1/2 N +  1/2 ((|A| + |B|-1)^2-1)
-/
lemma N_BD_def (S : SkippingSymbol') :  2*(∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ))   = S.N_BD + ((S.size-1)^2-1) := sorry


/-
The rank of a SkkipingSymbol of type BD is given by
half N
-/
def rank_BD (S : SkippingSymbol') : ℕ := S.N_BD/2

end SkippingSymbol'



@[ext]
structure SkippingSymbolBD' extends SkippingSymbol'
  deriving BEq, DecidableEq, Hashable

macro "mkSSymbolBD'" x:term:10 ";" y:term:10 : term  =>  `(({A := $x, B:=$y, non_adjA:= (by decide),non_adjB :=(by decide)}:SkippingSymbolBD'))


namespace SkippingSymbolBD'
open SkippingSymbol'

instance  reprSkippingSymbolBD' : Repr SkippingSymbolBD' where
  reprPrec s _ :=
      Std.Format.join [repr s.toSymbol', "_BD"]


#eval mkSSymbolBD' {0,3,5};{1,3,5}

def rank (S : SkippingSymbolBD'):= S.toSkippingSymbol'.rank_BD

def N (S: SkippingSymbolBD') := S.toSkippingSymbol'.N_BD

def shift_right (S : SkippingSymbolBD') : SkippingSymbolBD' where
  A := {0} ∪ Finset.map ⟨(· + 2), Nat.add_inj⟩ S.A
  B := {0} ∪ Finset.map ⟨(· + 2), Nat.add_inj⟩  S.B
  non_adjA := sorry
  non_adjB := sorry


def rank_shift (S : SkippingSymbolBD') :  (shift_right S).rank= S.rank:= by sorry

def defect_shift (S : SkippingSymbolBD') :  (shift_right S).defect = S.defect:= by
  simp_rw [SkippingSymbol'.defect]
  have h1 : (shift_right S).A.card = 1 + S.A.card := by simp [shift_right,_card_lem]
  have h2 : (shift_right S).B.card = 1 + S.B.card
    := by simp [shift_right,_card_lem]
  linarith


def equiv (S1 S2 : SkippingSymbolBD') : Prop :=
  S1 = shift_right S2

def isReduced (S : SkippingSymbolBD') := ¬ (0 ∈ S.A  ∧ 0 ∈ S.B)

end SkippingSymbolBD'


def SkippingSymbolBD := Quot SkippingSymbolBD'.equiv

namespace SkippingSymbolBD'

-- Repeatly shift_left will end with a reduced Symbol
def shift_left (S : SkippingSymbolBD') (h : 0∈ S.A ∧ 0∈ S.B) : SkippingSymbolBD' where
  A := Finset.image (· - 2) (S.A.erase 0)
  B := Finset.image (· - 2) (S.B.erase 0)
  non_adjA := sorry
  non_adjB := sorry



lemma shift_left_size (S : SkippingSymbolBD') (h : 0∈ S.A ∧ 0∈ S.B) : (shift_left S h).size = S.size - 2 := by
  sorry

lemma shift_left_size_le (S : SkippingSymbolBD') (h : 0∈ S.A ∧ 0∈ S.B) : (shift_left S h).size < S.size  := by
  sorry


def toReduced (S : SkippingSymbolBD') : SkippingSymbolBD'
:= if h : 0 ∈ S.A ∧  0 ∈ S.B
  then toReduced (shift_left S h)
  else S
termination_by S.size
decreasing_by
  exact shift_left_size_le S h

lemma to_reduced_reduced (S : SkippingSymbolBD') : S.toReduced  |> isReduced := by sorry




def toSymbol (S : SkippingSymbolBD') : SkippingSymbolBD := Quot.mk SkippingSymbolBD'.equiv S

end SkippingSymbolBD'

namespace SkippingSymbolBD
open SkippingSymbolBD'

instance  coe: Coe SkippingSymbolBD' SkippingSymbolBD where
  coe := SkippingSymbolBD'.toSymbol


def toReduced : SkippingSymbolBD →  SkippingSymbolBD' := Quot.lift (fun S => S.toReduced) (by sorry)



instance  reprSkippingSymbolBD : Repr SkippingSymbolBD where
  reprPrec s _ :=
      repr s.toReduced

instance  : BEq (SkippingSymbolBD) where
  beq := fun x y => x.toReduced == y.toReduced

def rank : SkippingSymbolBD → ℕ:= Quot.lift SkippingSymbolBD'.rank (by intro _ _ h; rw[h,rank_shift])



def defect: SkippingSymbolBD → ℤ := Quot.lift (·.defect)
  (by intro _ _ h; simp_rw [equiv] at h; simp [h,defect_shift])


end SkippingSymbolBD


/-
 We follow Lusztig's Intersection cohomology complexes on reductive groups Sectio 10-12

 A symbole of type C is a orderd pair of finite set of natural numbers (A,B) where A is a multiset of natural numbers and B is a multiset of positive natural numbers
 such that
 (1) ∀ i , {i, i+1} not contained in A nor in B
 (2) |A| + |B| is odd
 (3) 0 ∉ B
-/
@[ext]
structure SkippingSymbolC' extends SkippingSymbol' where
  cardodd : Odd (A.card + B.card)
  nonzeroB: 0 ∉ B
  deriving BEq, DecidableEq, Hashable

macro "mkSSymbolC'" x:term:10 ";" y:term:10 : term  =>  `(({A := $x, B:=$y, non_adjA:= (by decide),non_adjB :=(by decide),cardodd := (by decide), nonzeroB := (by decide)}:SkippingSymbolC'))

namespace SkippingSymbolC'
open SkippingSymbol'


instance  reprSkippingSymbolC' : Repr SkippingSymbolC' where
  reprPrec s _ :=
      Std.Format.join [repr s.toSymbol', "_C"]


def rank (S : SkippingSymbolC'):=  S.toSkippingSymbol'.rank_C

def shift_right (S : SkippingSymbolC') : SkippingSymbolC' where
  A := {0} ∪ Finset.map ⟨(· + 2), Nat.add_inj⟩ S.A
  B := {1} ∪ Finset.map ⟨(· + 2), Nat.add_inj⟩ S.B
  non_adjA := sorry
  non_adjB := sorry
  cardodd := sorry
  nonzeroB := sorry

abbrev equiv (S1 S2 : SkippingSymbolC') : Prop :=
  S1 = shift_right S2

def rank_shift (S : SkippingSymbolC') :  (shift_right S).rank = S.rank:= sorry


def defect_shift (S : SkippingSymbolC') :  (shift_right S).defect = S.defect:= by
  sorry

def isReduced (S : SkippingSymbolC') := ¬ (0 ∈ S.A  ∧ 1 ∈ S.B)


def shift_left (S : SkippingSymbolC') (h : 0∈ S.A ∧ 1∈ S.B) : SkippingSymbolC' where
  A := Finset.image (· - 2) (S.A.erase 0)
  B := Finset.image (· - 2) (S.B.erase 1)
  non_adjA := sorry
  non_adjB := sorry
  cardodd := sorry
  nonzeroB := sorry


lemma shift_left_size (S : SkippingSymbolC') (h : 0∈ S.A ∧ 1∈ S.B) : (shift_left S h).size = S.size - 2 := by
  sorry

lemma shift_left_size_le (S : SkippingSymbolC') (h : 0∈ S.A ∧ 1∈ S.B) : (shift_left S h).size < S.size  := by
  sorry


def toReduced (S : SkippingSymbolC') : SkippingSymbolC' := if h : 0 ∈ S.A ∧  1 ∈ S.B then toReduced (shift_left S h)  else S
termination_by S.size
decreasing_by
  exact shift_left_size_le S h


lemma to_reduced_reduced (S : SkippingSymbolC') : S.toReduced  |> isReduced := by sorry


end SkippingSymbolC'

def SkippingSymbolC := Quot SkippingSymbolC'.equiv

def SkippingSymbolC'.toSymbol (S : SkippingSymbolC') : SkippingSymbolC := Quot.mk SkippingSymbolC'.equiv S

namespace SkippingSymbolC

instance  coe: Coe SkippingSymbolC' SkippingSymbolC where
  coe := SkippingSymbolC'.toSymbol

open SkippingSymbolC'

def toReduced : SkippingSymbolC →  SkippingSymbolC' := Quot.lift (fun S => S.toReduced) (by sorry)

instance  reprSkippingSymbolC : Repr SkippingSymbolC where
  reprPrec s _ :=
      repr s.toReduced

def defect: SkippingSymbolC → ℤ := Quot.lift (·.defect)
  (by intro _ _ h; simp_rw [equiv] at h; simp [h,defect_shift])

def rank : SkippingSymbolC → ℕ:= Quot.lift SkippingSymbolC'.rank (by intro _ _ h; rw[h,rank_shift])

instance  : BEq (SkippingSymbolC) where
  beq := fun x y => x.toReduced == y.toReduced

end SkippingSymbolC


section Bipartition

--#eval add_zero 3 {1,2,3}

namespace Bipartition'

def rank (S : Bipartition') : ℕ := S.A.sum + S.B.sum




@[simp]
def pos (A : Multiset ℕ) : Multiset ℕ := A.filter (0 < ·)

@[simp]
def upto_zero (S1 S2 : Bipartition') : Prop :=
  pos S1.A = pos S2.A ∧ pos S1.B = pos S2.B


def swap : Bipartition'→ Bipartition':= fun x => {A:=x.B,B:=x.A}

def to_ssymbol_aux (init : ℕ) (S : List ℕ) : List ℕ
:= S.enum.map (fun (i, x) => x + i * 2 + init)

def to_ssymbol (init : ℕ) (S : Multiset ℕ) : Finset ℕ where
 val := (S.sort (· ≤ ·)).enum.map (fun (i, x) => x + i * 2 + init)
 nodup := by
  set L:= S.sort (· ≤ ·)
  apply List.nodup_iff_get?_ne_get?.2
  intro i j hij hj
  replace hj : j<L.length := by aesop
  have hi : i < L.length := by linarith
  have hh : L.get ⟨i,hi⟩  ≤ L.get ⟨j,hj⟩ := by
    have : L.Sorted (· ≤ ·) :=
      Multiset.sort_sorted (· ≤ ·) S
    exact List.Sorted.rel_get_of_lt  this hij
  simp [List.get?_map,List.get?_eq_get hi,List.get?_eq_get hj]
  linarith

lemma card_to_ssymbol (init : ℕ) (S : Multiset ℕ) : (to_ssymbol init S).card = Multiset.card S:= by
  simp [to_ssymbol]


def toSkippingSymbolB' (P : Bipartition') : SkippingSymbolBD' :=
  by
    let a := Multiset.card P.A
    let b := Multiset.card P.B
    exact
      if h : b<a
      then ⟨⟨to_ssymbol 0 P.A, to_ssymbol 0 (add_zero (a-b-1) P.B)⟩ , sorry, sorry⟩
      else ⟨⟨to_ssymbol 0 (add_zero (b-a+1) P.A), to_ssymbol 0 P.B⟩, sorry, sorry,⟩


def toSkippingSymbolD' (P : Bipartition') : SkippingSymbolBD' :=
  by
    let a := Multiset.card P.A
    let b := Multiset.card P.B
    exact
      if h : b<a
      then ⟨⟨to_ssymbol 0 P.A, to_ssymbol 0 (add_zero (a-b) P.B)⟩ , sorry, sorry⟩
      else ⟨⟨to_ssymbol 0 (add_zero (b-a) P.A), to_ssymbol 0 P.B⟩, sorry, sorry,⟩


def toSkippingSymbolC' (P : Bipartition') : SkippingSymbolC' :=
  by
    let a := Multiset.card P.A
    let b := Multiset.card P.B
    exact
      if h : b<a
      then ⟨⟨⟨to_ssymbol 0 P.A, to_ssymbol 1 (add_zero (a-b-1) P.B)⟩ , sorry, sorry⟩, sorry,sorry⟩
      else ⟨⟨⟨to_ssymbol 0 (add_zero (b-a+1) P.A), to_ssymbol 1 P.B⟩, sorry, sorry⟩, sorry, sorry⟩


#eval (toSkippingSymbolC' ⟨{0,0,1,3,7,7},{0,0,0,3,3,4}⟩:SkippingSymbolC)


#eval (toSkippingSymbolC' ⟨{1,3,7,7},{0,0,0,3,3,4}⟩:SkippingSymbolC)


end Bipartition'

def Bipartition := Quot Bipartition'.upto_zero

namespace Bipartition

def rank : Bipartition → ℕ:= Quot.lift Bipartition'.rank (by sorry)

def toBP' : Bipartition →  Bipartition' :=
  Quot.lift Bipartition'.remove_zero (by
  intro S1 S2 h
  rcases h with ⟨h1, h2⟩
  simp_rw [Bipartition'.pos] at h1
  simp_rw [Bipartition'.pos] at h2
  simp_rw [Bipartition'.remove_zero,h1,h2]
  )


instance  reprBipartition: Repr Bipartition where
  reprPrec s _ :=
      repr s.toBP'

end Bipartition


namespace SkippingSymbolC'
def toBP'_aux (sofar rest: List ℕ) (n : ℕ): List ℕ :=
  match sofar, rest, n with
  | sofar, [], _ => sofar
  | sofar, h::t, n => toBP'_aux (sofar ++ [h-n]) t (n+2)

def toBP' (S : SkippingSymbolC') : Bipartition' where
  A := toBP'_aux [] (S.A.sort (· ≤ ·)) 0
  B := toBP'_aux [] (S.B.sort (· ≤ ·)) 1


def toBP (S : SkippingSymbolC') : Bipartition := Quot.mk _ (S.toBP')

end SkippingSymbolC'


end Bipartition


/-
section test

def s1' := mkSSymbolC' {0, 2,4,7,21};{2,4,9,12}

def s2' := mkSSymbolC' {0, 2,4,6,8,21,24};{1, 3,5,7,9,12}
def s3' := mkSSymbolC' {0, 2,4,6,8,21,24};{1, 3,5,7,9,12}

#eval s2' = s3'

def s1 : SkippingSymbolC := s1'

def s2 : SkippingSymbolC := s2'





#eval s1'
#eval s1
#eval s1'.size



#eval s1.rank
#eval s1.defect


#eval s1'.shift_right.shift_right
#eval (s1'.shift_right.shift_right.shift_right.toSymbol : SkippingSymbolC)

#eval s1'.shift_right.rank

#eval s1'.defect
#eval s1'.shift_right.defect

#eval s1'.toBP'
#eval s1'.toBP

#eval s2'
#eval s2'.toReduced
#eval s2

end test
-/
