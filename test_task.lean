import Init
import Mathlib.Data.List.Basic

def t (i :ℕ ): IO Int:= do
  IO.println s!"Start task {i}"
  IO.sleep 10000
  IO.println s!"End task {i}"
  return (-i)

def ok (x : α) : Except ε α := Except.ok x

def fail (err : ε) : Except ε α := Except.error err

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x

def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x

def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x


infixl:55 " ~~> " => andThen

def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)


def add1 (x : Nat) : Nat :=
  if x%2 =0  then
    dbg_trace "add1: {x}"
    x + 1
  else
    dbg_trace "adde: {x}"
    x + 2

#eval add1 2

#eval firstThirdFifthSeventh [1,2,3,4,9]

#check StateT
#eval mapM (m:=Id) (· + 2) [1,2,3]

def main : IO Unit := do
  let mut xs := []
  for i in List.range 10 do
    let x <- IO.asTask do
      IO.println f!"begin: {i}"
      IO.sleep $ 10 * 1000
      IO.println f!"end: {i}"
    let x := Task.spawn $ fun () => x
    xs := x :: xs
  IO.sleep $ 15 * 1000
  return

/-
def main : IO UInt32:= do
  IO.println s!"Result: Here"
  let t := List.range 10 |>.map (fun i => Task.spawn <| IO.asTask <| t i)
  for x in t.reverse do
    let r ← x.get
    IO.println s!"Get result {repr r}"
  return 0
-/

/-

def tn (n : ℕ) : Task (IO Int) :=
  match n with
  | 0 => Task.spawn (fun _ => t 0)
  | n+1 =>
    let lt := (Task.spawn (fun _ => t (n+1)))
    let rt := tn n
    Task.bind lt (fun r => rt.map  fun l => do pure  ((← r) + (← l)))
-/
