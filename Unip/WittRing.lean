import Mathlib

section FiniteField
/-
In this section we define the Witt class of finite field.
-/

-- Square class has two element 1 and s such that s^2 = 1.
inductive Squareclass where
  | one
  | s

instance Squareclass.repr : Repr Squareclass where
  reprPrec := fun a _ =>  match a with
    | one => "1"
    | s => "s"

#eval (.s:Squareclass)

instance Squareclass.monoid : Monoid Squareclass where
  mul :=  fun a b => match (a, b) with
  | (one, one) => one
  | (one, s) => s
  | (s, one) => s
  | (s, s) => one
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one := one
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl

instance Squareclass.group: Group Squareclass where
  inv := fun a => a
  mul_left_inv := fun a => by cases a <;> rfl

inductive Witt
| zero  -- Zero space
| one   -- the space <1>
| nonsquare  -- the space <s> where s is a non-square
| quad -- the quadratic field extension

def Witt.dim (V : Witt) : ℕ := match V with
| zero => 0
| one => 1
| nonsquare => 1
| quad => 2

/-
For finite field with q elements
If  q == 1 (mod 4), then -1 is a square
  the Witt group is Z_2 × Z_2
If q == 3 (mod 4), then -1 is a nonsquare,
  the Witt group is Z_4
-/
def Witt.monoid1 : CommGroup Witt where
  mul := fun a b => match (a,b) with
   | (zero,c) => c
   | (c, zero) => c
   | (quad,quad) => zero
   | (quad,nonsquare) => one
   | (quad,one) => nonsquare
   | (nonsquare,quad) => one
   | (nonsquare,nonsquare) => zero
   | (nonsquare,one) => quad
   | (one,quad) => nonsquare
   | (one,nonsquare) => quad
   | (one,one) => zero
  mul_assoc := fun a b c => by
    cases a <;> cases b <;> cases c <;> rfl
  one := zero
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  mul_comm := fun a b => by cases a <;> cases b <;> rfl
  inv := fun a => a
  mul_left_inv :=  fun a => by cases a <;> rfl

/-
When q == 3 (mod 4), -1 is a non-square
The list of anisotropic spaces are
0, <1>, <1,1>, <-1>
-/
def Witt.monoid3 : CommGroup Witt where
  mul := fun a b => match (a,b) with
   | (zero,c) => c
   | (c, zero) => c
   | (one,one) => quad
   | (one,quad) => nonsquare
   | (quad,one) => nonsquare
   | (quad,quad) => zero
   | (quad,nonsquare) => one
   | (nonsquare,quad) => one
   | (nonsquare,nonsquare) => quad
   | (nonsquare,one) => zero
   | (one,nonsquare) => zero
  mul_assoc := fun a b c => by
    cases a <;> cases b <;> cases c <;> rfl
  one := zero
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  mul_comm := fun a b => by cases a <;> cases b <;> rfl
  inv := fun a => match a with
    | zero => zero
    | one => nonsquare
    | nonsquare => one
    | quad => quad
  mul_left_inv :=  fun a => by cases a <;> rfl

--
-- The value (dim [V0] + dim [W0] - dim ([V0]+[W0]))/2
def Witt.drank [hW : CommGroup Witt]: Witt → Witt → ℕ:= fun a b => (dim a + dim b - dim (hW.mul a b))/2

lemma Witt.drank_eq1 (V0 W0 : Witt) : dim V0 + dim W0 = dim (Witt.monoid1.mul V0 W0) + 2* (Witt.drank (hW := Witt.monoid1) V0 W0) := by
  cases V0 <;> cases W0 <;> rfl

lemma Witt.drank_eq3 (V0 W0 : Witt) : dim V0 + dim W0 = dim (Witt.monoid3.mul V0 W0) + 2* (Witt.drank (hW := Witt.monoid3) V0 W0) := by
  cases V0 <;> cases W0 <;> rfl

/-
Quadratic space
  V = V0 + H^n
here V0 is the anisotropic space H is the 2-dim hypebolic space

To simplify the computation, we allow n to be negative.
So n is na integer instead of a natural number.
-/
inductive QSpace where
  | Sum (V0 : Witt) (n :ℤ) : QSpace

instance QSpace.Group [hW : CommGroup Witt] : CommGroup QSpace where
  mul := fun a b =>
    match a, b with
    | Sum V0 n , Sum W0 m => Sum (hW.mul V0 W0) (n+m + Witt.drank (hW:=hW) V0 W0)
  mul_assoc := sorry
  one := Sum hW.one 0
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry
  inv := fun a => match a with
  | Sum V0 n => Sum (hW.inv V0) (n - V0.dim)
  mul_left_inv := by
    intro a
    match



end FiniteField
