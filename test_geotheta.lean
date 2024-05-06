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
  let t : String := getstr args 0
  let v : Nat := getnm args 1
  let n : Nat := getnm args 2
  let m : Nat := getnm args 3

  IO.println ""
  IO.println "Test the correspondence of defects"
  IO.println "Usage : symbol/springer  verbose_level n m  "
  if t = "symbol" then
    IO.println "Symbol correspondence"
    let res ← corrSymbol n m (verb := v)
  else if t = "springer" then
    let res ← test_eqform n m
    return 0
  return 0
