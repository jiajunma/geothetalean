import Mathlib.Data.Finset.Sort
import Init.Data.Nat.Basic
import Mathlib.Data.Multiset.Fold
import Mathlib.Data.Multiset.Basic

open Decidable Multiset

#eval Multiset.sort (. ≤ .)  ({5,3,3,7}: Multiset ℕ)


namespace Multiset

instance Or.Commutative :Std.Commutative (· || ·) := ⟨Bool.or_comm⟩

instance Or.Associative :Std.Associative (· || ·) := ⟨Bool.or_assoc⟩


def any_aux (a : Multiset Bool) := Multiset.fold (. || .) false a

lemma any_aux_iff (a : Multiset Bool) : any_aux a = true ↔ ∃ x ∈ a, x = true := by
  simp only [any_aux, exists_eq_right]
  exact Multiset.induction_on a (by simp) (by
    intro x s ih
    simp only [fold_cons_left, Bool.or_eq_true, ih, mem_cons]
    apply or_congr_left eq_comm
  )

def any (s : Multiset α) (p : α → Bool) : Bool := any_aux (map p s)

--lemma any_eq_fold (s : Multiset α) (p : α → Bool) : any s p = fold (. || .) false (map p s) := rfl

lemma any_iff (s : Multiset α) (p : α → Bool) : any s p = true ↔ ∃ a ∈ s, p a = true := by
  rw [any, any_aux_iff]
  constructor
  . rintro ⟨x, hx,hxt⟩
    rw [mem_map,hxt] at hx
    exact hx
  . rintro ⟨x, hx, hxt⟩
    use p x
    rw [mem_map]
    exact ⟨⟨x,⟨hx,rfl⟩⟩,hxt⟩

lemma not_any_iff (s : Multiset α) (p : α → Bool) : any s p = false ↔ ∀ a ∈ s, p a = false := by
  apply _root_.not_iff_not.mp
  simp only [Bool.not_eq_false, not_forall, exists_prop,any_iff]


instance And.Commutative :Std.Commutative (· && ·) := ⟨Bool.and_comm⟩

instance And.Associative :Std.Associative (· && ·) := ⟨Bool.and_assoc⟩


def all_aux (a : Multiset Bool) := Multiset.fold (. && .) true a


lemma all_aux_iff (a : Multiset Bool) : all_aux a = true ↔ ∀ x ∈ a, x = true := by
  simp only [all_aux, Bool.forall_bool, imp_false, implies_true, and_true]
  exact Multiset.induction_on a (by simp) (by
    intro x s ih
    simp only [fold_cons_left, Bool.and_eq_true, ih, mem_cons, not_or, and_congr_left_iff]
    intro _
    constructor
    . intro h; simp [h]
    . intro h; have : ¬ x = false := by
        push_neg; push_neg at h; exact Ne.symm h
      exact  Bool.of_not_eq_false this
  )

def all (s : Multiset α) (p : α → Bool) : Bool := all_aux (map p s)

lemma all_iff (s : Multiset α) (p : α → Bool) : all s p = true ↔ ∀ a ∈ s, p a = true := by
  rw [all, all_aux_iff]
  constructor
  . intro h x hx
    apply h (p x)
    rw [mem_map]; exact ⟨x,hx,rfl⟩
  . intro h x hx
    rw [mem_map] at hx
    rcases hx with ⟨x, hx, rfl⟩
    exact h x hx


lemma not_all_iff (s : Multiset α) (p : α → Bool) : all s p = false ↔ ∃ a ∈ s, p a = false := by
  apply _root_.not_iff_not.mp
  simp only [Bool.not_eq_false, all_iff, not_exists, not_and]


end Multiset



section prelude

def haspair (f : α → α) (A: Finset α) : Prop := ∃ (i:α), i ∈ A ∧ f i ∈ A

@[simp]
def haspair' [DecidableEq α] (f : α → α) (A: Finset α) : Bool := A.filter (λ i => f i ∈ A) ≠ ∅

@[simp]
lemma haspair'_iff {α} [DecidableEq α] (f : α → α) (A: Finset α) : haspair f A  ↔  haspair' f A = true := by
  sorry

namespace Multiset.Nat

def add_zero (n:ℕ) (S : Multiset ℕ) : Multiset ℕ := Multiset.replicate n 0 + S

end Multiset.Nat


lemma Nat.add_inj {a : ℕ} :
  Function.Injective <| fun x : ℕ => x+a := by
  intro _ _ _; aesop

instance Nat.le.decidable : DecidableRel (· ≤ · : ℕ → ℕ → Prop) := inferInstance



instance Multiset.Nat.repr : Repr (Multiset ℕ) where
  reprPrec s _ :=
      Std.Format.joinSep (s.sort (· ≤ ·)) ", "

instance Finset.Nat.repr : Repr (Finset ℕ) where
  reprPrec s _ :=
      Std.Format.joinSep (s.sort (· ≤ ·)) ", "

instance Finset.Nat.hashable : Hashable (Finset ℕ) where
  hash s := hash <| s.sort (· ≤ ·)

instance Multiset.Nat.hashable : Hashable (Multiset ℕ) where
  hash s := hash <| s.sort (· ≤ ·)

/-Triagle_number is the number of * in the following diagram of (n-1 rows)
  * * ... *
  * * ..*
  ....
  * *
  *
-/
def triangle_number (n : ℕ) : ℕ := n * (n - 1) / 2


def _card_lem (A : Finset ℕ) : ({0} ∪ Finset.map ⟨(· + 2), Nat.add_inj⟩ A).card = 1 + A.card  := by calc
      _ = ({0}:Finset ℕ).card + (Finset.map ⟨(· + 2), Nat.add_inj⟩ A).card
      := by simp [Finset.card_union_of_disjoint]
      _ = _ := by simp




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


/-
Select the elements in the list c according to the Zip list
-/
def select (Z : List (ℕ × List ℕ)) (c : Finset ℕ) : Finset ℕ := Z.filterMap (fun x => if x.1 ∈ c then some x.2 else none) |> List.join |> List.toFinset

/-unselction the elements in the list c according to the Zip list -/
def unselect (Z : List (ℕ × List ℕ)) (c : Finset ℕ) : Finset ℕ := Z.filterMap (fun x => if x.1 ∉ c then some x.2 else none) |> List.join |> List.toFinset


end prelude
