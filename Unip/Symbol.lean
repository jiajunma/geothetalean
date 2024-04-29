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
  B : Finset PNat
  non_adjA : ¬ haspair' (· + 1) A
  non_adjB : ¬ haspair' (· + 1) B
  --non_adjA : ∀ i, ¬  {i,i+1} ⊆ A
  --non_adjB : ∀ i, ¬  {i,i+1} ⊆ B
  cardodd : Odd (A.card + B.card)




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


instance FinsetNat.repr : Repr (Finset ℕ) where
  reprPrec s _ :=
      Std.Format.joinSep (s.sort (· ≤ ·)) ", "

instance FinsetPNat.repr : Repr (Finset PNat) where
  reprPrec s _ :=
      Std.Format.joinSep ((s.sort (· ≤ ·)).map Subtype.val) ", "
      --Std.Format.join ["{", Std.Format.joinSep ((s.sort (· ≤ ·)).map  repr) ", ", "}"]

unsafe instance  reprSkippingSymbol' : Repr SkippingSymbol' where
  reprPrec s _ :=
      Std.Format.join ["(", repr s.A, ";", repr s.B, ")"]

def size (S : SkippingSymbol') : ℕ := S.A.card + S.B.card

def rank (S : SkippingSymbol') : ℕ  :=
∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ)   - triangle_number S.size

lemma rank_def (S : SkippingSymbol') :  ∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ)   = S.rank + triangle_number S.size := sorry

def defect (S : SkippingSymbol') : ℤ :=  S.A.card - S.B.card

lemma _root_.PNat.add_inj (a : Nat) :
  Function.Injective <| fun x : PNat => (x+n:PNat) := by
  intro _ _ _; aesop

lemma _root_.Nat.add_inj (a : ℕ) :
  Function.Injective <| fun x : ℕ => x+n := by
  intro _ _ _; aesop

def shift_right (S : SkippingSymbol') : SkippingSymbol' where
  A := {0} ∪ Finset.map ⟨(· + 2), Nat.add_inj 2⟩  S.A
  B := {1} ∪ Finset.map ⟨(· + 2), PNat.add_inj 2⟩ S.B
  non_adjA := sorry
  non_adjB := sorry
  cardodd := sorry

abbrev equiv (S1 S2 : SkippingSymbol') : Prop :=
  S1 = shift_right S2

def rank_shift (S : SkippingSymbol') :  (shift_right S).rank = S.rank:= sorry


def defect_shift (S : SkippingSymbol') :  (shift_right S).defect = S.defect:= sorry

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

structure Bipartition where
  A : Finset PNat
  B : Finset PNat

namespace Bipartition

def rank (S : Bipartition) : ℕ := ∑ a in S.A, (a:ℕ) + ∑ b in S.B, (b:ℕ)



end Bipartition

end bipartition

section test

def s1' : SkippingSymbol' where
   A := {0, 2,4,7,21}
   B := {2,4,9,12}
   non_adjA := by decide
   non_adjB := by decide
   cardodd := by decide

def s1 : SkippingSymbol := Quot.mk _ s1'


#eval s1'
#eval s1
#eval s1'.size

#eval s1.rank
#eval s1.defect

#eval s1'.shift_right

#eval s1'.shift_right.rank

#eval s1'.defect
#eval s1'.shift_right.defect


end test
