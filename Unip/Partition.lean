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

import Unip.Auxi

-- We identify a partition as a multiset of natural number
-- Duality in Type A

open Multiset

def Multiset.max (l : Multiset ℕ ):= Multiset.fold Nat.max 0 l

#eval {1,2,3,4} |> Multiset.max

def transpose (a : Multiset ℕ) : Multiset ℕ:=
  Multiset.range
  a.max
  |> Multiset.map (fun i => Multiset.countP (fun x => x > i) a)
  |> Multiset.filter (. != 0)


#eval {0,0,1,1,2,3,3} |> transpose
#eval {0,0,1,1,2,3,3} |> transpose |> transpose


--def isTypeBD (a: Multiset ℕ):= ∀ i ∈ a, (i%2=0)-> Multiset.count i a %2 =0
def isTypeBD (a: Multiset ℕ) : Bool :=
  a.all (fun r => r == 0 || r % 2 == 1 || Multiset.count r a %2 ==0)

lemma isTypeBD_iff (a: Multiset ℕ) : isTypeBD a = true ↔ ∀ i ∈ a, i≠0 ∧ (i%2=0)-> Multiset.count i a %2 =0 :=by
  rw [isTypeBD,all_iff]
  apply iff_of_eq
  apply forall_congr
  intro i
  congr
  rw [Bool.or_eq_true, beq_iff_eq, ne_eq, and_imp, eq_iff_iff]
  constructor
  . intro h hi1 hi2
    simp only [hi2, Nat.reduceBEq, Bool.or_false, beq_iff_eq, hi1, false_or] at h
    rw [h]
  . intro h
    repeat rw [imp_iff_not_or] at h
    push_neg at h
    have : (i==0 || i%2==1) = true ↔ i=0 ∨ i%2 ≠ 0 := by
      rw [Bool.or_eq_true, beq_iff_eq, ne_eq]
      rw [or_congr_right]
      rw [beq_iff_eq, Nat.mod_two_ne_zero]
    rw [this,or_assoc]
    exact h

def isTypeC (a: Multiset ℕ) : Bool :=
  a.all (fun r => r % 2 ==0 || Multiset.count r a % 2 ==0)


structure Partition where
  lam :Multiset ℕ
  nonzero : 0 ∉ lam

instance partition.coe : Coe (Partition) (Multiset ℕ) where
  coe := fun p => p.lam


abbrev Marking (p : Partition) : Set (Finset ℕ) := {nu | nu.val ⊆ p.lam}


structure MarkedPartition where
  nu : Finset ℕ
  lam : Multiset ℕ
  nonzero : 0 ∉ lam
  nusub : nu.val ⊆ lam

def coe_marking (m : Marking p) : MarkedPartition := {
    lam := p.lam
    nonzero := p.nonzero
    nu := m.val
    nusub := m.prop
  }

attribute [coe] coe_marking

instance coe_mp : CoeOut (Marking p) (MarkedPartition) where
  coe := coe_marking

namespace MarkedPartition


unsafe instance  reprMP : Repr MarkedPartition where
  reprPrec p _ :=
    if p.lam = 0
      then "∅"
      else Std.Format.join ["(", repr p.nu.val, ",", repr p.lam, ")"]

abbrev mu (p : MarkedPartition) : Multiset ℕ := p.lam  - p.nu.val

end MarkedPartition

structure MarkedPartitionBD extends MarkedPartition where
  typeBD : isTypeBD lam
  nuodd  : nu.val.all (fun r => Odd r)
  nucardeven : Even nu.card


unsafe instance  reprMP : Repr MarkedPartitionBD where
  reprPrec p _ :=
    if p.lam = 0
      then "∅"
      else Std.Format.join ["(", repr p.nu.val, ",", repr p.lam, ")"]

structure MarkedPartitionC extends MarkedPartition where
  typeC : isTypeC lam
  nuodd  : nu.val.all (fun r => Even r)


section test

#eval {1,1,2,2,3,3,3} |> isTypeBD

#eval {1,1,2,2,3,3,1,0} |> isTypeBD


#eval {1,1,2,2,4,6,8,3,3} |> isTypeC

def p : MarkedPartition := ⟨{5,3},{5,5,3,3,4,2}, by trivial,by simp⟩

def q : MarkedPartitionBD where
  nu := {3,1}
  lam := {3,3,3,4,4,4,4,2,2,1,1}
  nusub := by simp
  nonzero := by decide
  typeBD := by simp; decide
  nuodd := by simp; decide
  nucardeven := by simp




#check q


#eval p

#eval q


end test