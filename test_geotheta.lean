import Unip.GeoTheta


def getnm (args : List String) (i : ℕ) : ℕ :=
  match args.get? i |>.bind String.toNat? with
  | none => 0
  | some n => n

def getstr (args : List String) (i : ℕ) : String :=
  match args.get? i with
  | none => ""
  | some s => s

unsafe def main (args: List String) : IO UInt32 := do
  let n : Nat := getnm args 0
  let m : Nat := getnm args 1
  let t : String := getstr args 2

  IO.println ""
  IO.println "Test the correspondence of defects"
  IO.println ""
  let res ← corrSymbol n m
  if t = "symbol" then
    IO.println "Symbol correspondence"
  else
    return 0
  return 0
