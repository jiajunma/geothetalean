import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Multiset.Fold

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
