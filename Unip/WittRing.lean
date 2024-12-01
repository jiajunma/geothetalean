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

instance Witt.repr : Repr Witt where
  reprPrec := fun a _ =>  match a with
    | zero => ""
    | one => "<1>"
    | nonsquare => "<s>"
    | quad => "Q"


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
def Witt.group1 : CommGroup Witt where
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
def Witt.group3 : CommGroup Witt where
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





end FiniteField

/- Set up the group structure on the Witt ring-/
instance Witt.WittGroup : CommGroup Witt := Witt.group3
instance Witt.WittMonoid : CommMonoid Witt := inferInstance
instance Witt.Hadd: HAdd Witt Witt Witt where
  hAdd := Witt.WittGroup.mul
instance Witt.Neg: Neg Witt  where
  neg := Witt.WittGroup.inv


section QuadraticSpace


--
-- The value (dim [V0] + dim [W0] - dim ([V0]+[W0]))/2
def Witt.drank [hW : CommGroup Witt]: Witt → Witt → ℕ:= fun a b => (dim a + dim b - dim (hW.mul a b))/2

lemma Witt.drank_eq (V0 W0 : Witt) : dim V0 + dim W0 = dim (V0 + W0) + 2* (Witt.drank V0 W0) := by
  cases V0 <;> cases W0 <;> rfl


lemma Witt.drank_neg_sum_eq (V0 : Witt) : (Witt.drank (-V0) (V0)) = V0.dim:= by
  cases V0 <;> rfl

lemma Witt.drank_neg_sum_eq' (V0 : Witt) : (Witt.drank (V0) (-V0)) = V0.dim:= by
  cases V0 <;> rfl

/-
Quadratic space
  V = V0 + H^n
here V0 is the anisotropic space H is the 2-dim hypebolic space

To simplify the computation, we allow n to be negative.
So n is na integer instead of a natural number.
-/
--def QSpace := Witt × ℤ
structure QSpace where
  W : Witt
  n : ℤ

instance QSpace.inhabited : Inhabited QSpace where
  default := ⟨Witt.zero,0⟩


instance : Repr QSpace where
  reprPrec := fun qs prec =>
    match qs with
    | ⟨Witt.zero, n⟩ => s!"H^{n}"
    | ⟨W, n⟩ =>
      match n with
      | 0 => s!"{repr W}"
      | n => s!"{repr W} ⊕ H^{n}"


abbrev qspace_sum :QSpace -> QSpace -> QSpace := fun ⟨V0,n⟩  ⟨W0,m⟩  =>
   ⟨(V0+W0),(n+m + Witt.drank  V0 W0)⟩

instance QSpace.hAdd : HAdd QSpace QSpace QSpace where
  hAdd := qspace_sum

instance QSpace.Monoid: CommMonoid QSpace where
  mul := qspace_sum
  mul_assoc := sorry
  one := ⟨Witt.zero,0⟩
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry


instance QSpace.Group : CommGroup QSpace where
  mul_comm := QSpace.Monoid.mul_comm
  inv := fun ⟨V0,n⟩  => ⟨-V0,(- n - V0.dim)⟩
  mul_left_inv := by
    intro ⟨V0,n⟩
    sorry
    /-
    calc
      _ = ⟨-V0 + V0, -n - V0.dim + n +Witt.drank (-V0) V0 ⟩ := rfl
      _ = ⟨Witt.zero,0⟩ := by
        rw [Witt.drank_neg_sum_eq]
        ext <;> norm_num <;> try linarith
        cases V0 <;> rfl
    -/

#check QSpace

instance QSpace.hNeg: Neg QSpace where
  neg := QSpace.Group.inv

instance QSpace.hSub: HSub QSpace QSpace QSpace where
  hSub := fun a b => a + (-b)

#eval (⟨Witt.one,10⟩  :QSpace)  - (⟨Witt.one,14⟩ :QSpace)

def QSpace.op : QSpace → QSpace := fun ⟨W,n⟩ => ⟨-W,n⟩

def QSpace.dim : QSpace → ℤ := fun ⟨W,n⟩ => W.dim + 2*n

def QSpace.toStrgp : QSpace → String :=
  fun Q =>
    match Q with
    | ⟨Witt.zero,_⟩  => s!"O^+({Q.dim})"
    | ⟨Witt.one,_⟩  => s!"O^+({Q.dim})"
    | ⟨Witt.nonsquare,_⟩  => s!"O^-({Q.dim})"
    | ⟨Witt.quad,_⟩  => s!"O^-({Q.dim})"
/-
 Nilpotent orbit is classified by Quardatic space
 together with the row length
-/
abbrev Nil := List (QSpace×ℕ)

/-
Regularize nilpotent oribt
-/
def Nil.reg (N : Nil) : Nil :=
  let nonZero := N.filter (fun (_, n) => n ≠ 0)
  let sorted := List.insertionSort (fun (_, n1) (_, n2) => n1 ≥ n2) nonZero
  let grouped := sorted.groupBy (fun (_, n1) (_, n2) => n1 == n2)
  let merged := grouped.map (fun group =>
    let n := (group.head!).2  -- Get the n value from the first element
    let mergedQSpace := group.foldl (fun acc (qs, _) => acc + qs) ⟨Witt.zero,0⟩
    (mergedQSpace, n))
  merged.filter (fun (qs, _) => qs.dim ≠ 0)


def jordanspace (R : QSpace) (n : ℕ) : QSpace:=
  match n with
  | 0 => ⟨Witt.zero,0⟩
  | n+1 => R + jordanspace R.op n

#eval jordanspace ⟨Witt.quad,0⟩ 17 |>.dim
#eval (jordanspace ⟨Witt.quad,1⟩ 17).dim

def Nil.space (N : Nil) : QSpace :=
  let jordanSpaces := N.map (fun (qs, n) => jordanspace qs n)
  jordanSpaces.foldl (fun acc js => acc + js) ⟨Witt.zero, 0⟩

def Nil.dim (N : Nil) := N.space.dim


/-
  The following function realizes the usual lifting
-/
def liftNil (N : Nil) (Q : QSpace) : Nil :=
  match N with
  | [] => [(Q,1)]
  | (R,r)::N => (R.op,r+1)::liftNil N (Q - jordanspace R.op (r+1))

#eval liftNil [(⟨Witt.one,1⟩ ,1)] ⟨Witt.zero,4⟩

def QSpaceplus (n : ℕ) : QSpace :=
  let V0 := if n % 2 = 0 then Witt.zero else Witt.one
  ⟨V0,n/2⟩

lemma QSpaceplus.dim_eq : (QSpaceplus n).dim = n :=
  by
    by_cases h : n %2 = 0
    · simp only [QSpace.dim, QSpaceplus, h, reduceIte]
      sorry
    · simp only [QSpace.dim, QSpaceplus, h, reduceIte]
      sorry



def QSpaceminus (n : ℕ) : QSpace :=
  let V0 := if n % 2 = 0 then Witt.quad else Witt.nonsquare
  ⟨V0,(n-1)/2⟩

def QSofUnipSp (k : ℕ) : QSpace := ⟨Witt.zero, k*(k+1)⟩
def QSofUnipMp (k : ℕ) : QSpace := ⟨Witt.zero, k*k⟩

def QSofUnipOeven (k : ℕ) : QSpace := match k%2 with
  | 0 =>  ⟨Witt.zero, k*k⟩
  | _ =>  ⟨Witt.quad, k*k-1⟩

def QSofUnipOodd (k : ℕ) : QSpace := match k%2 with
  | 0 =>  ⟨Witt.one, k*(k+1)⟩
  | _ =>  ⟨Witt.nonsquare, k*(k+1)⟩


lemma QSofUnipOeve_dim : (QSofUnipOeven k).dim = 2*k*k := by
  sorry


def GenUnip_aux (Q0 : Nil) (sofar : List Nil) (k n: ℕ )  :=
  let Q1 := liftNil Q0 (QSofUnipSp k)
  let Q2 := liftNil Q1 (QSofUnipOeven k)
  let sofar := Q2::Q1::sofar
  match k,n with
  | _, 0 => sofar
  | k, n+1 =>
    GenUnip_aux Q2 (Q2::Q1::sofar) (k+1) n

def GenUnip (k : ℕ) : List Nil :=
    GenUnip_aux [] [] 0 k

#eval (GenUnip 1).map Nil.reg

#eval (GenUnip 1).map (fun N => N.dim)


/-
The type representing the (quadratic)-unipotent represent
the unipotent representation over finite feild
-/
inductive UnipF
| Sp (k:ℕ) : UnipF  -- the unique one for Sp(2 * k *(k+1))
| Oeven (k:ℕ) (sign: Fin 2) : UnipF -- the unique one for O^±(2 * k)
| Oodd (k:ℕ) (sign: Fin 2) : UnipF
| Mp (k : ℕ) (sign: Fin 2) : UnipF

/-
This function generate the space supporting the unipotent representation
-/
def UnipF.space (U : UnipF) : QSpace := match U with
| Sp k => ⟨Witt.zero, k*(k+1)⟩
| Mp k _ => ⟨Witt.zero, k*k⟩
| Oeven k _ => match k%2 with
  | 0 =>  ⟨Witt.zero, k*k⟩
  | _ =>  ⟨Witt.quad, k*k-1⟩
| Oodd k _ => match k%2 with
  | 0 =>  ⟨Witt.one, k*(k+1)⟩
  | _ =>  ⟨Witt.nonsquare, k*(k+1)⟩

instance UnipF.repr : Repr UnipF where
  reprPrec := fun a _ =>
  match a with
  | Sp k => s!"Sp({2*k*(k+1)})"
  | Mp k s => s!"Mp({2*k*k})_{s}"
  | Oeven _ s => s!"{a.space.toStrgp}_{s}"
  | Oodd _ s => s!"{a.space.toStrgp}_{s}"

/-
The decsent sequence for unipotent representation
-/
def UnipF.descent (U : UnipF) : UnipF := match U with
| Sp k => Oeven k 0
| Oeven k _ => Sp (k-1)
| Mp k _ => Oodd (k-1) 0
| Oodd k _ => Mp k 0

def UnipF.rank (U : UnipF): ℕ := match U with
| Sp k => k
| Oeven k _ => k
| Mp k _ => k
| Oodd k _ => k

lemma dim_dec (U: UnipF) : U.descent.descent.rank < U.rank := by sorry

/-
This is defined recursively
-/
def UnipF.descentSeq : UnipF → List UnipF := fun U => match U with
| Oeven 0 _ => [U]
| Mp 0 _ =>  [U]
| U => U :: UnipF.descentSeq (U.descent)
termination_by U => U.rank
decreasing_by
  sorry

#eval UnipF.descentSeq (UnipF.Sp 3)
#eval UnipF.descentSeq (UnipF.Mp 3 0)
#eval UnipF.descentSeq (UnipF.Oeven 3 0)
#eval UnipF.descentSeq (UnipF.Oodd 3 0)

#check QSpace
-- Define the function to calculate the desired new list recursively.
def computeNil : List QSpace → List Nil := fun L =>
match L with
| [] => []
| [x] => [(Nil.reg [(x,1)])]
| x :: y :: xs =>
    let tail_seq := computeNil (y :: xs)
    let head_nil := (liftNil tail_seq.head! x).reg
    head_nil :: tail_seq

#eval computeNil <| List.map UnipF.space (UnipF.descentSeq (UnipF.Sp 5))

#eval computeNil <| List.map UnipF.space (UnipF.descentSeq (UnipF.Mp 3 0))


/-
The function to print the results
-/
def GenUnipSpM (n : ℕ) : IO (List Nil) := do
  let mut N0 :Nil:= []
  let mut res : List Nil := []
  for k in [0:n+1] do
    let Q1 := QSofUnipOeven k
    let Q2 := QSofUnipSp k
    let N1 := liftNil N0 Q1 |>.reg
    let N2 := liftNil N1 Q2 |>.reg
    IO.println s!"2*k*k = {2*k*k} \t {Q1.toStrgp} : {repr N1}"
    IO.println s!"2*k*(k+1) = {2*k*(k+1)} \t Sp({Q2.dim}) : {repr N2}"
    N0 := N2
    res := N2::N1::res
   pure res

#eval GenUnipSpM 3

def GenUnipMpM (n : ℕ) : IO (List Nil) := do
  let mut N0 :Nil:= []
  let mut res : List Nil := []
  for k in [0:n+1] do
    let Q1 := QSofUnipOodd k
    let Q2 := QSofUnipMp (k+1)
    let N1 := liftNil N0 Q1 |>.reg
    let N2 := liftNil N1 Q2 |>.reg
    --IO.println s!"2*k*k +1= {2*k*k+1} \t {Q1.toStrgp} : {repr N1}"
    IO.println s!"{Q1.toStrgp}:\t{repr N1}"
    --IO.println s!"2*(k+1)*(k+1) = {2*(k+1)*(k+1)} \t Sp({Q2.dim}) : {repr N2}"
    IO.println s!"Mp({Q2.dim}):\t{repr N2}"
    N0 := N2
    res := N2::N1::res
   pure res


#eval GenUnipMpM 7


section Padic


def QSpaceP := Witt × Witt × ℤ

instance : Repr QSpaceP where
  reprPrec := fun qs prec =>
    let H := match qs.2.2 with
      | 0 => ""
      | n => s!"⊕ H^{n}"
    match qs with
    -- The zero space
    | ⟨Witt.zero,Witt.zero, 0⟩ => s!"Z"
    | ⟨Witt.zero,Witt.zero, n⟩ => s!"H^{n}"
    | ⟨W1,Witt.zero,_⟩ => s!"{repr W1}" ++ H
    | ⟨Witt.zero,W2,_⟩ => s!"π{repr W2}" ++ H
    | ⟨W1,W2,n⟩ => s!"{repr W1} ⊕ π{repr W2}" ++ H


instance QSpaceP.inhabited : Inhabited QSpaceP where
  default := ⟨Witt.zero,Witt.zero,0⟩


/-
The quadratic space over p-adic group is
-/
abbrev qspacep_sum :QSpaceP -> QSpaceP -> QSpaceP := fun ⟨V0,V1,n⟩  ⟨W0,W1,m⟩  =>
   ⟨(V0+W0),(V1+W1),(n+m + Witt.drank V0 W0 + Witt.drank V1 W1)⟩

instance QSpaceP.hAdd : HAdd QSpaceP QSpaceP QSpaceP where
  hAdd := qspacep_sum

instance QSpaceP.Monoid: CommMonoid QSpaceP where
  mul := qspacep_sum
  mul_assoc := sorry
  one := ⟨Witt.zero,Witt.zero,0⟩
  one_mul := sorry
  mul_one := sorry
  mul_comm := sorry


instance QSpaceP.Group : CommGroup QSpaceP where
  mul_comm := QSpaceP.Monoid.mul_comm
  inv := fun ⟨V0,V1,n⟩  => ⟨-V0,-V1,(- n - V0.dim - V1.dim)⟩
  mul_left_inv := sorry

def QSpaceP.op : QSpaceP → QSpaceP := fun ⟨V0,V1,n⟩ => ⟨-V0,-V1,n⟩


def QSpaceP.dim : QSpaceP → ℤ := fun ⟨V0,V1,n⟩ => V0.dim + V1.dim + 2*n


instance QSpaceP.hNeg: Neg QSpaceP where
  neg := QSpaceP.Group.inv

instance QSpaceP.hSub: HSub QSpaceP QSpaceP QSpaceP where
  hSub := fun a b => a + (-b)


abbrev NilP := List (QSpaceP×ℕ)

/-
Regularize nilpotent oribt
-/
def NilP.reg (N : NilP) : NilP :=
  let nonZero := N.filter (fun (_, n) => n ≠ 0)
  let sorted := List.insertionSort (fun (_, n1) (_, n2) => n1 ≥ n2) nonZero
  let grouped := sorted.groupBy (fun (_, n1) (_, n2) => n1 == n2)
  let merged := grouped.map (fun group =>
    let n := (group.head!).2  -- Get the n value from the first element
    let mergedQSpace := group.foldl (fun acc (qs, _) => acc + qs) ⟨Witt.zero,Witt.zero,0⟩
    (mergedQSpace, n))
  merged.filter (fun (qs, _) => qs.dim ≠ 0)


def QSpaceP.jordanspace (R : QSpaceP) (n : ℕ) : QSpaceP:=
  match n with
  | 0 => ⟨Witt.zero,Witt.zero,0⟩
  | n+1 => R + QSpaceP.jordanspace R.op n

#eval jordanspace ⟨Witt.quad,0⟩ 17 |>.dim
#eval (jordanspace ⟨Witt.quad,1⟩ 17).dim

def NilP.space (N : NilP) : QSpaceP :=
  let jordanSpaces := N.map (fun (qs, n) => QSpaceP.jordanspace qs n)
  jordanSpaces.foldl (fun acc js => acc + js) ⟨Witt.zero,Witt.zero, 0⟩

def NilP.dim (N : NilP) := N.space.dim


def liftNilP (N : NilP) (Q : QSpaceP) : NilP :=
  match N with
  | [] => [(Q,1)]
  | (R,r)::N => (R.op,r+1)::liftNilP N (Q - QSpaceP.jordanspace R.op (r+1))

/-
The unipotent reprenentation of p-adic group
-/
def UnipP := UnipF × UnipF

def UnipP.descentSSeq (U : UnipP) : List QSpaceP :=
  let L1 := List.map UnipF.space $ UnipF.descentSeq U.1
  let L2 := List.map UnipF.space $ UnipF.descentSeq U.2
  let f : Option QSpace → Option QSpace → QSpaceP :=
    fun a b => match a,b with
    | none,none => ⟨Witt.zero,Witt.zero,0⟩
    | none,some b => ⟨Witt.zero,b.1,b.2⟩
    | some a,none => ⟨a.1,Witt.zero,a.2⟩
    | some a, some b=> ⟨a.1,b.1,a.2+b.2⟩
  List.zipWithAll f L1 L2


def computeNilP : List QSpaceP → List NilP := fun L =>
match L with
| [] => []
| [x] => [(NilP.reg [(x,1)])]
| x :: y :: xs =>
    let tail_seq := computeNilP (y :: xs)
    let head_nil := (liftNilP tail_seq.head! x).reg
    head_nil :: tail_seq


#eval computeNilP $ UnipP.descentSSeq ⟨UnipF.Oodd 8 0, UnipF.Oodd 3 0⟩

end Padic



end QuadraticSpace
