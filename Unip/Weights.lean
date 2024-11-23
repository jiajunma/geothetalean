import Mathlib


namespace Finsupp

variable {α : Type*} [DecidableEq α] {M : Type*} [Zero M]
variable (t : Equiv α α)

def shift : Finsupp α M → Finsupp α M := fun x =>
  {
    support := Finset.image t.2 x.support
    toFun := x.toFun ∘ t.1
    mem_support_toFun := by
      intro a
      rw [Finset.mem_image]
      constructor
      · intro H; obtain  ⟨b,hb⟩ := H
        have : b= t.toFun a := by simp [<-hb.2]
        simp only [Equiv.toFun_as_coe] at this
        simp only [Equiv.toFun_as_coe, Function.comp_apply, <- this, ne_eq]
        exact (x.mem_support_toFun _).1 hb.1
      · intro H
        simp only [Equiv.toFun_as_coe, Function.comp_apply] at H
        use (t a)
        exact ⟨(x.mem_support_toFun _).2 H, by simp⟩
  }


end Finsupp

section Stratification
open Finsupp LaurentPolynomial
open BigOperators

/-
X = ⊔ X_a with a running over an index set S
for each startification, it has a dimention $d : S \to ℕ$.
-/

def add (n :ℤ) : Equiv ℤ ℤ := {
   toFun := (· + n)
   invFun := (· - n )
   left_inv := by intro; simp
   right_inv := by intro; simp
}


variable {S : Type*} [Fintype S]
variable (d : S → ℕ)

/-
Here T=v.
The generic Hecke module is a module over R = Z[v,v⁻¹] with basis S.
-/
abbrev R := LaurentPolynomial ℤ
instance : Algebra ℤ ℝ := inferInstance

abbrev M := Finsupp S R

/-
The Tate Module is a direct sum of Tate twists ℚₗ (k/2) .
So the Gorthendieck group of Tate twists is given by ⊕ₖ ℚₗ (k/2)^m_k  are free module over ℤ,
-/
def Tate := Finsupp ℤ ℤ

instance Tate.zero : Zero Tate := Finsupp.instZero
noncomputable instance Tate.addcommmonoid: AddCommGroup Tate := Finsupp.instAddCommGroup

/- Tate twist by n/2 of a Tate module
  It send ℚₗ (k/2) to ℚₗ ((k+n)/2)
-/
def TateTwist (n : ℤ): Tate → Tate := shift (add (-n))

noncomputable abbrev v (k : ℤ) : R := LaurentPolynomial.T k
noncomputable abbrev vv : R := LaurentPolynomial.T 1

noncomputable abbrev nv (k : ℤ) : R :=
  if Even k then LaurentPolynomial.T k else - LaurentPolynomial.T k

lemma nv_mul_add (k l : ℤ ): (nv k) * (nv l) = nv (k+l) := by
  simp_rw [nv]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  all_goals rw [LaurentPolynomial.T_add] ; try ring_nf
  · exfalso; exact h3 (Even.add h1 h2)
  · exfalso; apply h2 ; exact (Int.even_add.1 h4).1 h1
  · exfalso; apply h1 ; exact (Int.even_add.1 h6).2 h5
  · exfalso; apply h7 ; rw [<-Int.odd_iff_not_even] at h1
    rw [<-Int.odd_iff_not_even] at h5
    exact Odd.add_odd h1 h5

lemma nv_zero : nv 0 = 1 := by simp only [nv, even_zero, reduceIte, T_zero]

/-
M is called has weight w if H^i is a copy of ℚₗ (-(w+i)/2)
If H^i contains ℚₗ (k/2) = ℚₗ (- (-k -i  +i) /2), then it will be send to (-v)^(-k-i)
Here i denote the homology degree
-/
noncomputable def Hich (i : ℤ): Tate → R := fun x =>
  ∑ k in x.support, nv (-k-i)


variable (i) in
lemma shiftHich (r : Tate) (k : ℤ): Hich i r = (nv k) * Hich (i+k) r := by
  simp_rw [Hich]
  rw [Finset.mul_sum]
  congr 1; ext r l
  rw [nv_mul_add]; ring_nf


lemma shiftHich' (r : Tate) (k : ℤ):  Hich (i+k) r = nv (-k) * Hich i r := by
  rw [shiftHich i r k,<-mul_assoc,nv_mul_add]
  simp only [add_left_neg,nv_zero]


#check bigsum
/-
We view a chaim complex as free module over ℤ
-/
/-
The K group of chain compleses is then
ℤ → Tate
-/
def KT := Finsupp ℤ Tate

/-
The shift of complex is given by (M[k])_i  = M_(k+i)
-/

def DegreeShift (n:ℤ) : KT → KT := shift (add n)


noncomputable def ch : KT → R  := fun F =>
  ∑ i in F.support, if Even i then  Hich i (F.toFun i) else - Hich i (F.toFun i)

lemma degreeshift_ch (M : KT) :  ch (DegreeShift n M) = (nv (-n)) * ch M := by
  simp_rw [DegreeShift,ch,shift,add]
  rw [Finset.mul_sum]
  apply Finset.sum_equiv (add (n))
  · simp [add]
    intro i
    constructor
    · intro h; obtain ⟨a,ha⟩ := h
      have :a = i+n := by linarith [ha.2]
      rw [this] at ha
      exact ha.1
    · intro h
      use (i+n); simp [h]
  · intro i hi
    by_cases H : Even n
    · by_cases H' : Even i
      · have : Even (i+n) := Even.add H' H
        simp [add,H,H',this,reduceIte,toFun]
        simp [shiftHich'] 
      · sorry
    · sorry





end Stratification
