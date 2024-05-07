import Init
import Mathlib.Data.List.Basic

def t (i :ℕ ): IO Int:= do
  IO.println s!"Start task {i}"
  IO.sleep 10000
  IO.println s!"End task {i}"
  return (-i)


def main : IO UInt32:= do
  IO.println s!"Result: Here"
  let t := List.range 10 |>.map (fun i => Task.spawn (fun _ => t i))
  for x in t.reverse do
    let r ← x.get
    IO.println s!"Get result {r}"
  return 0


/-

def tn (n : ℕ) : Task (IO Int) :=
  match n with
  | 0 => Task.spawn (fun _ => t 0)
  | n+1 =>
    let lt := (Task.spawn (fun _ => t (n+1)))
    let rt := tn n
    Task.bind lt (fun r => rt.map  fun l => do pure  ((← r) + (← l)))
-/
