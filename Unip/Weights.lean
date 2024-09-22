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

def add (n :ℤ) : Equiv ℤ ℤ :=
  { toFun := (· + n)
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

noncomputable abbrev v (k : ℤ) :Tate := LaurentPolynomial.T k
/-
M is called has weight w if H^i is a copy of ℚₗ (-(w+i)/2)
If H^i contains ℚₗ (k/2) = ℚₗ (- (-k -i  +i) /2), then it will be send to (-v)^(-k-i)
Here i denote the homology degree
-/
noncomputable def Hich (i : ℤ): Tate → R := fun x =>
  ∑ k in x.support, v (-k-i)

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


def ch : KT → ℤ  := fun F =>
  ∑ i in F.support, (-1)^i * Hich (F i)





end Stratification
