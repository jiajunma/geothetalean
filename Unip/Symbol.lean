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
def haspair (f : α → α) (A: Finset α) : Prop := ∃ (i:α), i ∈ A ∧ f i ∈ A

@[simp]
def haspair' [DecidableEq α] (f : α → α) (A: Finset α) : Bool := A.filter (λ i => f i ∈ A) ≠ ∅

@[simp]
lemma haspair'_iff {α} [DecidableEq α] (f : α → α) (A: Finset α) : haspair f A  ↔  haspair' f A = true := by
  sorry

structure SkippingSymbol' where
  A : Finset ℕ
  B : Finset ℕ
  non_adjA : ¬ haspair' (· + 1) A
  non_adjB : ¬ haspair' (· + 1) B
  cardodd : Odd (A.card + B.card)
  nonzeroB: 0 ∉ B




/-Triagle_number is the number of * in the following diagram of (n-1 rows)
  * * ... *
  * * ..*
  ....
  * *
  *
-/
def triangle_number (n : ℕ) : ℕ := n * (n - 1) / 2

/-
The rank of a Symbol is given by
∑ a ∈ A, a + ∑ b ∈ B, b - 1/2 (|A| + |B|)(|A| + |B| - 1)
-/
namespace SkippingSymbol'

instance Nat.le.decidable : DecidableRel (· ≤ · : ℕ → ℕ → Prop) := inferInstance


instance PNat.le.decidable : DecidableRel (· ≤ · : PNat → PNat → Prop) := inferInstance


instance FinsetNat.repr : Repr (Multiset ℕ) where
  reprPrec s _ :=
      Std.Format.joinSep (s.sort (· ≤ ·)) ", "

/-
instance FinsetPNat.repr : Repr (Multiset PNat) where
  reprPrec s _ :=
      Std.Format.joinSep ((s.sort (· ≤ ·)).map Subtype.val) ", "
      --Std.Format.join ["{", Std.Format.joinSep ((s.sort (· ≤ ·)).map  repr) ", ", "}"]
-/

instance  reprSkippingSymbol' : Repr SkippingSymbol' where
  reprPrec s _ :=
      Std.Format.join ["(", repr s.A.1, ";", repr s.B.1, ")"]


structure ReducedSkippingSymbol extends SkippingSymbol' where
  reduced: ¬ (0 ∈ A  && 1 ∈ B)

instance  reprReducedSkippingSymbol : Repr ReducedSkippingSymbol where
  reprPrec s _ := repr s.toSkippingSymbol'


def size (S : SkippingSymbol') : ℕ := S.A.card + S.B.card

def rank (S : SkippingSymbol') : ℕ  :=
∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ)   - triangle_number S.size

lemma rank_def (S : SkippingSymbol') :  ∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ)   = S.rank + triangle_number S.size := sorry

def defect (S : SkippingSymbol') : ℤ :=  S.A.card - S.B.card

lemma _root_.Nat.add_inj (a : ℕ) :
  Function.Injective <| fun x : ℕ => x+n := by
  intro _ _ _; aesop



def shift_right (S : SkippingSymbol') : SkippingSymbol' where
  A := {0} ∪ Finset.map ⟨(· + 2), Nat.add_inj 2⟩ S.A
  B := {1} ∪ Finset.map ⟨(· + 2), Nat.add_inj 2⟩ S.B
  non_adjA := sorry
  non_adjB := sorry
  cardodd := sorry
  nonzeroB := sorry

abbrev equiv (S1 S2 : SkippingSymbol') : Prop :=
  S1 = shift_right S2

def rank_shift (S : SkippingSymbol') :  (shift_right S).rank = S.rank:= sorry


def defect_shift (S : SkippingSymbol') :  (shift_right S).defect = S.defect:= by
  sorry



def shift_left (S : SkippingSymbol') (h : 0∈ S.A && 1∈ S.B) : SkippingSymbol' where
  A := Finset.image (· - 2) (S.A.erase 0)
  B := Finset.image (· - 2) (S.B.erase 1)
  non_adjA := sorry
  non_adjB := sorry
  cardodd := sorry
  nonzeroB := sorry


lemma shift_left_size (S : SkippingSymbol') (h : 0∈ S.A && 1∈ S.B) : (shift_left S h).size = S.size - 2 := by
  sorry

lemma shift_left_size_le (S : SkippingSymbol') (h : 0∈ S.A && 1∈ S.B) : (shift_left S h).size < S.size  := by
  sorry


def toReduced (S : SkippingSymbol') : ReducedSkippingSymbol := if h : 0 ∈ S.A && 1 ∈ S.B then toReduced (shift_left S h)  else ⟨S, h⟩
termination_by S.size
decreasing_by
  exact shift_left_size_le S h

end SkippingSymbol'


def SkippingSymbol := Quot SkippingSymbol'.equiv

namespace SkippingSymbol
open SkippingSymbol'

unsafe instance  reprSkippingSymbol : Repr SkippingSymbol where
  reprPrec s _ :=
      repr s.unquot


def rank : SkippingSymbol → ℕ:= Quot.lift SkippingSymbol'.rank (by intro _ _ h; rw[h,rank_shift])


def defect: SkippingSymbol → ℤ := Quot.lift SkippingSymbol'.defect (by intro _ _ h; rw [h,defect_shift])

end SkippingSymbol


section bipartition

structure Bipartition' where
  A : Multiset Nat
  B : Multiset Nat

namespace Bipartition'

def rank (S : Bipartition') : ℕ := S.A.sum + S.B.sum



instance  reprBipartition' : Repr Bipartition' where
  reprPrec s _ :=
      Std.Format.join ["{", repr s.A, ";", repr s.B, "}"]

@[simp]
def pos (A : Multiset ℕ) : Multiset ℕ := A.filter (0 < ·)

@[simp]
def upto_zero (S1 S2 : Bipartition') : Prop :=
  pos S1.A = pos S2.A ∧ pos S1.B = pos S2.B


def remove_zero (S : Bipartition') : Bipartition' where
  A := pos S.A
  B := pos S.B


end Bipartition'

def Bipartition := Quot Bipartition'.upto_zero

namespace Bipartition

def rank : Bipartition → ℕ:= Quot.lift Bipartition'.rank (by sorry)

def toBP' : Bipartition →  Bipartition' :=
  Quot.lift Bipartition'.remove_zero (by
  intro S1 S2 h
  rcases h with ⟨h1, h2⟩
  simp_rw [Bipartition'.remove_zero,h1,h2]
  )


instance  reprBipartition: Repr Bipartition where
  reprPrec s _ :=
      repr s.toBP'

end Bipartition



def SkippingSymbol'.to_aux (sofar rest: List ℕ) (n : ℕ): List ℕ :=
  match sofar, rest, n with
  | sofar, [], _ => sofar
  | sofar, h::t, n => SkippingSymbol'.to_aux (sofar ++ [h-n]) t (n+2)

def SkippingSymbol'.toBP' (S : SkippingSymbol') : Bipartition' where
  A := SkippingSymbol'.to_aux [] (S.A.sort (· ≤ ·)) 0
  B := SkippingSymbol'.to_aux [] (S.B.sort (· ≤ ·)) 1


def SkippingSymbol'.toBP (S : SkippingSymbol') : Bipartition := Quot.mk _ (S.toBP')

end bipartition

section test

def s1' : SkippingSymbol' where
   A := {0, 2,4,7,21}
   B := {2,4,9,12}
   non_adjA := by decide
   non_adjB := by decide
   cardodd := by decide
   nonzeroB := by decide

def s1'' : ReducedSkippingSymbol := ⟨s1', by decide⟩

def s1 : SkippingSymbol := Quot.mk _ s1'




#eval s1'
#eval s1
#eval s1'.size

#eval s1''.rank
#eval s1''

#eval s1.rank
#eval s1.defect

#eval s1'.shift_right

#eval s1'.shift_right.rank

#eval s1'.defect
#eval s1'.shift_right.defect

#eval s1'.toBP'
#eval s1'.toBP

end test
