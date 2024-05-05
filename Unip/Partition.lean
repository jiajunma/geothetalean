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
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Basic
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
  if k1 = 0 ∧ k2 = 0 then 0
  else if k1 = 0  then n/k2
  else if k2 = 0 then m/k1
  else min (m/k1) (n/k2)

/-
For dual pair (O_m, Sp_n).
Now we generate all the pairs of orthosymplectic orbits
These are multi-sets of partitions such that (k+1,k) and (k,k+1) and pair {(k,k),(k,k)} can occure.
Moreover, if k is even, then (k,k+1) has even multiplicity and if k is odd, then (k+1,k) has even multiplicity.
-/
-- k stands for row length in the ab-diagram currently are placing.
def gen_OS(m : ℕ) (n : ℕ) (k: ℕ) : List (Multiset (ℕ × ℕ)) :=
  if n % 2 = 1 then []
  else
    match k with
    | 0 => if m=0 ∧ n=0 then [{}] else []
    | k'+1 =>
      if k % 2 = 0 then
      -- First add {(k/2,k/2), (k/2,k/2)} pairs
      List.range (1 + maxmul m n (k) (k)) >>=
        fun a =>
          let m1 := (m-k*a)
          let n1 := (n-k*a)
          List.map ((Multiset.replicate (2*a) (k/2,k/2)) + ·) <|
          gen_OS m1 n1 k'
      else
      -- Then add {(k/2+1,k/2), (k/2,k/2)} pairs
          List.range (1 + maxmul m n (k/2 + 1) (k/2)) >>= fun a =>
           let m1 := (m-(k/2+1)*a)
           let n1 := (n-k/2*a)
           if (k/2+1) % 2 = 0 ∧ a % 2 = 1 then []
           else
            List.map  ((Multiset.replicate a (k/2+1,k/2))  + ·) <|
            -- Now add {(k/2,k/2+1)} pairs
            List.range (1 + maxmul m1 n1 (k/2) (k/2+1)) >>= fun c =>
            let m2 := (m1-k/2*c)
            let n2 := (n1-(k/2+1)*c)
            if (k/2) % 2 = 0 ∧ c % 2 = 1 then []
            else
              -- Lastly do the recursion
              List.map ((Multiset.replicate c (k/2,k/2+1)) + ·) <| gen_OS m2 n2 k'


/-
Another version of the above function
-/
def gen_OS'(m : ℕ) (n : ℕ) (k: ℕ) : List (Multiset (ℕ × ℕ)) :=
  if n % 2 = 1 then []
  else
    match k with
    | 0 => if m=0 ∧ n=0 then [{}] else []
    | k'+1 =>
      -- First add {(k'+1,k'+1), (k'+1,k'+1)} pairs
      List.range (1 + maxmul m n (2*k) (2*k)) >>=
        fun a =>
          let m1 := (m-2*k*a)
          let n1 := (n-2*k*a)
          List.map ((Multiset.replicate (2*a) (k,k)) + ·) <|
          -- Now add {(k'+1,k')} pairs
          List.range (1 + maxmul m1 n1 (k'+1) k') >>= fun b =>
           let m2 := (m1-(k'+1)*b)
           let n2 := (n1-k'*b)
           if (k'+1) % 2 = 0 ∧ b % 2 = 1 then []
           else
            List.map  ((Multiset.replicate b (k'+1,k')) + ·) <|
            -- Now add {(k',k'+1)} pairs
            List.range (1 + maxmul m2 n2 k' (k'+1)) >>= fun c =>
            let m3 := (m2-k'*c)
            let n3 := (n2-(k'+1)*c)
            if k' % 2 = 0 ∧ c % 2 = 1 then []
            else
              -- Lastly do the recursion
              List.map ((Multiset.replicate c (k',k'+1)) + ·) <| gen_OS' m3 n3 k'



def gen_OS_relevent (m : ℕ) (n : ℕ) (k: ℕ) : List (Multiset (ℕ × ℕ)) :=
  if n % 2 = 1 then []
  else
    match k with
    | 0 => if m=0 ∧ n=0 then [{}] else []
    | k'+1 =>
      if k % 2 = 0 then
      -- Add {(k/2,k/2), (k/2,k/2)} pairs
      List.range (1 + maxmul m n (k) (k)) >>=
        fun a =>
          let m1 := (m-k*a)
          let n1 := (n-k*a)
          List.map ((Multiset.replicate (2*a) (k/2,k/2)) + ·) <| gen_OS_relevent m1 n1 k'
      else
          -- Add {(k/2+1,k/2), (k/2,k/2)} pairs
          (List.range (1 + maxmul m n ((k/2) + 1) (k/2)) >>= fun a =>
           let m1 := (m-((k/2)+1)*a)
           let n1 := (n-(k/2)*a)
           if ((k/2)+1) % 2 = 0 ∧ a % 2 = 1 then []
           else
            List.map  ((Multiset.replicate a ((k/2)+1,k/2))  + ·) <| gen_OS_relevent m1 n1 k' )
          ++
          -- Add {(k/2,k/2+1)} pairs
          (List.range (1 + maxmul m n (k/2) ((k/2)+1)) >>= fun a =>
            let m1 := (m-(k/2)*a)
            let n1 := (n-((k/2)+1)*a)
            -- Very tricky, have to avoid the case where no rows are added,
            -- the case was already covered in the previous list
            if a =0 ∨ ((k/2) % 2 = 0 ∧ a % 2 = 1) then []
            else
              List.map ((Multiset.replicate a (k/2,(k/2)+1)) + ·) <| gen_OS_relevent m1 n1 k' )



def AllOrthoSymplectic' (m : ℕ) (n : ℕ) : List (Multiset (ℕ × ℕ)) :=
  gen_OS' m n (max m n)

def AllOrthoSymplectic (m : ℕ) (n : ℕ) : List (Multiset (ℕ × ℕ)) :=
  gen_OS m n (m+n)


def AllOrthoSymplectic_relevent (m : ℕ) (n : ℕ) : List (Multiset (ℕ × ℕ)) :=
  gen_OS_relevent m n (m+n)


/-Projection to the first coordiante -/
def projO (p : Multiset (ℕ × ℕ)) : Multiset ℕ :=
  p.map (fun x => x.1)


/-Projection to the second coordiante -/
def projSp (p : Multiset (ℕ × ℕ)) : Multiset ℕ :=
  p.map (fun x => x.2)


def ff :=  gen_OS 4 4 8

#eval ff

def ff' := gen_OS' 4 4 4

#eval ff'

#eval ff=ff'

def n := 9
def m := 12

#eval (AllOrthoSymplectic n m).map (fun x => (projO x).sum)
#eval (AllOrthoSymplectic n m).map (fun x => (projSp x).sum)
#eval (AllOrthoSymplectic' n m).length
#eval (AllOrthoSymplectic' n m) --.toFinset.card
#eval (AllOrthoSymplectic n m).length
#eval ((AllOrthoSymplectic n m).toFinset \ (AllOrthoSymplectic' n m).toFinset)

#eval AllOrthoSymplectic n m = AllOrthoSymplectic' n m


#eval AllOrthoSymplectic 9 10 |>.length


/-
Now we generate the pairs of relevent orthosymplectic orbits
These are orbits such that (k+1,k) and (k,k+1) are not appear simultaneously.
-/
def isRelevent (p : Multiset (ℕ × ℕ)) : Bool :=
  -- First find all possible rows
  p.map (fun r => r.1+r.2) |>.all
  (fun r => r % 2 = 0 ∨
            -- either r is even
            ¬ ((r/2,r/2+1)∈ p ∧ (r/2+1,r/2)∈ p)
            -- or (r/2,r/2+1) and (r/2+1,r/2) are not appear simultaneously
            )

#eval AllOrthoSymplectic 10 10 |>.filter isRelevent |>.length

#eval AllOrthoSymplectic_relevent 10 10 |>.length
#eval AllOrthoSymplectic_relevent 10 10 |>.toFinset.card


/-
Given a relevent orthosymplectic orbit,
now we generate all relevent orbit data

-- We assume the orbit is relevent!
-/

def Msort (p : Multiset ℕ) : List ℕ :=
  p.sort (· ≤ · )

def Fsort (p : Finset ℕ) : List ℕ :=
  p.sort (· ≤ · )


def gen_OS_component_data (p : Multiset (ℕ × ℕ)) : List (Finset ℕ × Finset ℕ) :=
  -- The Projectors
  let pr1 := fun s : Finset (ℕ × ℕ) => Finset.image (fun x => x.1) s
  let pr2 := fun s : Finset (ℕ × ℕ) => Finset.image (fun x => x.2) s
  -- The projection to Orthogonal side
  let O1 := projO p
  -- The projection to Symplectic side
  let O2 := projSp p
  -- The component group of  the orthogonal side
  let C1 : List ℕ := filter (Odd · ) O1|>.toFinset |> Fsort
  -- The component group of  the symplectic side
  -- Becareful about zero!
  let C2 :List ℕ := filter (fun x => x>0 ∧ Even x) O2|>.toFinset |> Fsort
  -- Build the dictionary that both side must be the same
  -- only for odd lenght pairs (k, k+1) or (k,k-1).
  -- They are in the dictionary only if k is odd
  -- Becareful about zero!
  -- "0" is not in the compoent group of "Sp"
  let D := filter (fun x => Odd x.1 ∧ Odd (x.1+x.2) ∧ x.2 >0) p |>.toFinset
  -- The linked component for the orthogonal side
  let L1 := pr1 D |> Fsort
  -- The linked component for the symplectic side
  let L2 := pr2 D |> Fsort
  let DD := List.zip L1 L2
  -- Now all relevent orbit data is in one-one correspondence with
  -- P(D) x P(C1-L1) x P(C2-L2)
  List.map (fun x => (
      if (1,0) ∈ D then [1] else [] ++
      List.filter (fun y :ℕ × ℕ => y.2 ∈ x.1) DD |>.map (fun y: ℕ × ℕ => y.1) ++ x.2.1
      |>.toFinset,
      L2 ++ x.2.2 |>.toFinset))
  <| List.product (List.sublists L2)
     (List.product (List.sublists (C1.filter (· ∉ L1)))
                     (List.sublists (C2.filter (· ∉ L2))))


def gen_OS_data (p : Multiset (ℕ × ℕ)) : List <|(Multiset ℕ × Finset ℕ)× (Multiset ℕ × Finset ℕ ) :=
  -- The projection to Orthogonal side
  let O1 := projO p
  -- The projection to Symplectic side
  let O2 := projSp p
  List.map (fun x => ((O1,x.1), (O2,x.2)))
  <| gen_OS_component_data p



#eval AllOrthoSymplectic_relevent  4 4 |> List.map gen_OS_data



def gen_OS_od' (p : Multiset (ℕ × ℕ)) : IO <| List (Finset ℕ × Finset ℕ) := do
  -- The Projectors
  let pr1 := fun s : Finset (ℕ × ℕ) => Finset.image (fun x => x.1) s
  let pr2 := fun s : Finset (ℕ × ℕ) => Finset.image (fun x => x.2) s
  -- The projection to Orthogonal side
  let O1 := projO p
  -- The projection to Symplectic side
  let O2 := projSp p
  -- The component group of  the orthogonal side
  let C1 : List ℕ := filter (Odd · ) O1|>.toFinset |> Fsort
  -- The component group of  the symplectic side
  -- Becareful about zero!
  let C2 :List ℕ := filter (fun x => x>0 ∧ Even x) O2|>.toFinset |> Fsort
  -- Build the dictionary that both side must be the same
  -- only for odd lenght pairs (k, k+1) or (k,k-1).
  -- They are in the dictionary only if k is odd
  -- Becareful about zero!
  -- "0" is not in the compoent group of "Sp"
  let D := p.bind (fun x => if Odd x.1 ∧ Odd (x.1+x.2) then {x.1,x.2} else {}) |>.toFinset |> Fsort
  --IO.println s!"D := {D}"
  -- Compute the intervals
  let I := interval D
  let I1 := I.filter (fun x => 0 ∉ x)
  -- The interval I0 is always selected
  let I0 := I.filter (fun x => 0 ∈ x) |>.join
  --IO.println s!"I := {I}"
  -- Now all relevent orbit data is in one-one correspondence with
  -- P(D) x P(C1-L1) x P(C2-L2)
  pure <|
  List.map (fun x =>
    -- selected
    let sel := I0 ++ (x.1.join)
    (sel.filter (· ∈ C1) ++ x.2.1 |>.toFinset,
     sel.filter (· ∈ C2) ++ x.2.2 |>.toFinset))
  <| List.product (List.sublists I1)
     (List.product (List.sublists (C1.filter (· ∉ D)))
                     (List.sublists (C2.filter (· ∉ D))))


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
