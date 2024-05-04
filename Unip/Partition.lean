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
import Mathlib.Tactic.Linarith.Frontend


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



section generator


/-
Generate all partitions of size n with all parts less then or equal to m
-/
def gen_parts (n : ℕ ) (m : ℕ) : List (Multiset ℕ ) :=
  match n with
  | 0 => [{}]
  | n'+1 => List.range (min (n'+1) m) >>= (fun i => ((gen_parts (n'-i) (i+1)).map (fun l => {i+1} + l)))
termination_by n

#eval gen_parts 4 2


#eval List.range' 1 10 >>=  (fun i => [i+1])


def ALlPartitions' (n : ℕ) : List (Multiset ℕ) := gen_parts n n

/-
Generate all partitions of type C of size n with all parts less then or equal to m
-/
def gen_parts_C (n : ℕ ) (m : ℕ) : List (Multiset ℕ ) :=
  match n with
  | 0 => [{}]
  -- For induction each time only add even number of boxes
  -- either add {2i} or add {i,i} with i odd
  | n'+1 => List.range (min n m) >>= (
    fun i => if (i+1) % 2 = 0 then
      (gen_parts_C (n'-i) (i+1)).map (fun l => {i+1} + l)
    else (if 2*(i +1) ≤ n'+1 then
      (gen_parts_C (n'-2*i-1) (i+1)).map (fun l => {i+1,i+1} + l)
    else
      [] )
    )
termination_by n

lemma gen_parts_C_isTypeC : p ∈ gen_parts_C n m → isTypeC p := by sorry



def ALlPartitionsC' (n : ℕ) : List (Multiset ℕ) := gen_parts_C n n

#eval gen_parts_C 10 10
#eval gen_parts_C 11 11


/-
Generate all partitions of type BD of size n with all parts less then or equal to m
-/
def gen_parts_BD (n : ℕ ) (m : ℕ) : List (Multiset ℕ ) :=
  match n with
  | 0 => [{}]
  -- For induction each time only add even number of boxes
  -- either add {2i} or add {i,i} with i odd
  | n'+1 => List.range (min n m) >>= (
    fun i => if (i+1) % 2 = 1 then
      (gen_parts_BD (n'-i) (i+1)).map (fun l => {i+1} + l)
    else (if 2*(i +1) ≤ n'+1 then
      (gen_parts_BD (n'-2*i-1) (i+1)).map (fun l => {i+1,i+1} + l)
    else
      [] )
    )
termination_by n



lemma gen_parts_BD_isTypeBD : p ∈ gen_parts_BD n m → isTypeBD p := by sorry


def ALlPartitionsBD' (n : ℕ) : List (Multiset ℕ) := gen_parts_BD n n


#eval gen_parts_BD 11 11

-- compute the maximal multiplicity of (k1,k2) contained in (m,n)
-- If k1=k2=0, the return will be 0!
def maxmul (m n k1 k2 : ℕ) : ℕ :=
  if k1 = 0 then n/k2
  else if k2 = 0 then m/k1
  else min (m/k1) (n/k2)

/-
For dual pair (O_m, Sp_n).
Now we generate all the pairs of orthosymplectic orbits
These are multi-sets of partitions such that (k+1,k) and (k,k+1) and pair {(k,k),(k,k)} can occure.
Moreover, if k is even, then (k,k+1) has even multiplicity and if k is odd, then (k+1,k) has even multiplicity.
-/
-- k stands for length of row length currently are placing.
def gen_OS(m : ℕ) (n : ℕ) (k: ℕ) : List (Multiset (ℕ × ℕ)) :=
  if n % 2 = 1 then []
  else
    match k with
    | 0 => if m=0 ∧ n=0 then [{}] else []
    | k'+1 =>
      -- First add {(k'+1,k'+1), (k'+1,k'+1)} pairs
      List.range (1 + maxmul m n (2*(k'+1)) (2*(k'+1))) >>=
        fun a =>
          let m1 := (m-2*(k'+1)*a)
          let n1 := (n-2*(k'+1)*a)
          List.map ((Multiset.replicate (2*a) (k'+1,k'+1)) + ·) <|
          -- Now add {(k'+1,k')} pairs
          List.range (1 + maxmul m1 n1 (k'+1) k') >>= fun b =>
           let m2 := (m1-(k'+1)*b)
           let n2 := (n1-k'*b)
           if (k'+1) % 2 = 0 ∧ b % 2 = 1 then []
           else
            List.map  ((Multiset.replicate b (k'+1,k'))  + ·) <|
            -- Now add {(k',k'+1)} pairs
            List.range (1 + maxmul m2 n2 k' (k'+1)) >>= fun c =>
            let m3 := (m2-k'*c)
            let n3 := (n2-(k'+1)*c)
            if k' % 2 = 0 ∧ c % 2 = 1 then []
            else
              -- Lastly do the recursion
              List.map ((Multiset.replicate c (k',k'+1)) + ·) <| gen_OS m3 n3 k'

def AllOrthoSymplectic (m : ℕ) (n : ℕ) : List (Multiset (ℕ × ℕ)) :=
  gen_OS m n (max m n)

#eval AllOrthoSymplectic 4 4

/-Projection to the first coordiante -/
def projO (p : Multiset (ℕ × ℕ)) : Multiset ℕ :=
  p.map (fun x => x.1)


/-Projection to the second coordiante -/
def projSp (p : Multiset (ℕ × ℕ)) : Multiset ℕ :=
  p.map (fun x => x.1)

/-
Now we generate the pairs of relevent orthosymplectic orbits
These are orbits such that (k+1,k) and (k,k+1) are not appear simautaonously.
-/
def isRelevent (p : Multiset (ℕ × ℕ)) : Bool :=
  p.projO.all (fun x => )

end generator


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
