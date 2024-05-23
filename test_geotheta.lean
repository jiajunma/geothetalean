import Init
import Unip.GeoTheta


/-
The function test whether the correspondence of sysmbols are independent of defects
-/
unsafe def test_eqform' (m n : ℕ) (select: Option (ℤ × ℤ):= none) (verb :ℕ:= 10): IO Unit := do
  let ⟨APairs,AllD⟩  ← corrSymbol m n (verb:=0)
  let exc := if m %2 = 0 then (0,1) else (1,1)
  let restD:= AllD.filter (·  ≠ exc)
  IO.println s!"Consider the dual pair: O({m})-Sp({n})"
  for dp in restD.1.unquot do
    IO.println <| String.replicate (40) '-'
    IO.println s!"Test defect pair: {repr dp}"
    let cc1 := Task.spawn <| fun _ => corrSymbol m n (select:= some dp) (verb:=0)
    --let ⟨subpairs1,_⟩  ← corrSymbol m n (select:= some dp) (verb:=0)
    let mm := DmodifyN m dp.1
    let nn := CmodifyN n dp.2
    -- The standard correspondence
    let cc2 := Task.spawn <| fun _ => corrSymbol mm nn  (select := some (mm%2,1)) (verb:=0)
    --let ⟨subpairs2,_⟩ ← corrSymbol mm nn  (select := some (mm%2,1)) (verb:=0)
    let ⟨subpairs1,_⟩ ←  cc1.get
    let ⟨subpairs2,_⟩ ←  cc2.get
    let toRepn := fun x : Symbol'×Symbol' => (x.1.BDSymbol_toBP.remove_zero, x.2.CSymbol_toBP.remove_zero)

    let rpairs1 := List.map toRepn subpairs1 |>.toFinset
    let rpairs2 := List.map toRepn subpairs2 |>.toFinset
    IO.println s!"The Springer model pairs: O({mm})-Sp({nn})"
    IO.println s!"|s1| = {repr rpairs1.card}, |Springer| = {repr rpairs2.card}"
    IO.println s!"s1-Springer: {repr (rpairs1 \ rpairs2)}"
    IO.println s!"Springer-s1 : {repr (rpairs2 \ rpairs1)}"

  return ()

/-
The function test whether the correspondence of Springer sysmbols
between defects
-/
unsafe def test_evenodd (m n : ℕ) : IO Unit := do
  if m %2 =1 ∨ n % 2 = 1 then
    IO.println s!"m and n must be even ({m},{n})"
    return ()
  else pure ()
  let ⟨APairsE,AllD⟩  ← corrSymbol m n (verb:=0)
  let ⟨APairsO,AllD⟩  ← corrSymbol (m+1) n (verb:=0)
  let Epairs := APairsE |>.filter (fun x => (x.1.defect, x.2.defect) = (0,1))
  let Opairs := APairsO |>.filter (fun x => (x.1.defect, x.2.defect) = (1,1))
  let toRepnES := fun x : Symbol'×Symbol' => (x.1.BDSymbol_toBP.remove_zero, x.2.CSymbol_toBP.remove_zero)
  let toRepnOS := fun x : Symbol'×Symbol' => (x.1.BDSymbol_toBP.remove_zero , x.2.CSymbol_toBP.remove_zero |> Bipartition'.swap)

  IO.println <| String.replicate (40) '-'
  let rpairs1 := List.map toRepnES Epairs |>.toFinset
  let rpairs2 := List.map toRepnOS Opairs |>.toFinset
  IO.println s!"The Even Springer model pairs: O({m})-Sp({n})"
  IO.println s!"The Odd Springer model pairs: O({m+1})-Sp({n})"
  IO.println s!"|Even| = {repr rpairs1.card}, |Odd| = {repr rpairs2.card}"
  IO.println s!"Even-Odd: {repr (rpairs1 \ rpairs2)}"
  IO.println s!"Odd-Odd: {repr (rpairs2 \ rpairs1)}"

  return ()

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
  --IO.println "Test the correspondence of defects"
  IO.println "Usage : symbol/springer/evenodd  verbose_level n m  "
  if t = "symbol" then
    IO.println "Symbol correspondence"
    let res ← corrSymbol n m (verb := v)
  else if t = "springer" then
    let res ← test_eqform' n m
  else if t = "evenodd" then
    let rest ← test_evenodd n m
  else
    pure ()

  return 0
