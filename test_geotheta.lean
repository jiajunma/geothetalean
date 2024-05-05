import Unip.GeoTheta


def getnm (args : List String) (i : ℕ) : ℕ :=
  match args.get? 0 |>.bind String.toNat? with
  | none => 0
  | some n => n

unsafe def main (args: List String) : IO UInt32 := do
  let n : Nat := getnm args 1
  let m : Nat := getnm args 2

  IO.println ""
  IO.println "Test the correspondence of defects"
  IO.println ""
  let res := defectPairs n m

  return 0
