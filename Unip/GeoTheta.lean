import Init.Data.Ord

import Unip.Partition
import Unip.Springer

section test_functions



open Symbol'
instance : Ord (ℕ × ℕ ) := lexOrd

/-
Test the correspondence between O_n and Sp_m
-/
unsafe def testOS (m n : ℕ) : IO Unit := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  if n % 2 = 1 then
    stderr.putStrLn s!"Symplectic group is even dimension, current input is: {n}!"
    return ()
  else
    stdout.putStrLn s!"Testing the correspondence between O({m}) and Sp({n})"
    let AllOS := AllOrthoSymplectic_relevent m n
    for p in AllOS do
      let O1 := projO p
      let O2 := projSp p
      stdout.putStrLn s!"----------------------------------"
      stdout.putStrLn s!"{repr p}"
      stdout.putStrLn s!"({repr O1}) <----> ({repr O2})"
      let od ← gen_OS_od' p
      for c in od do
        stdout.putStrLn s!"[{repr c.1}] <===> [{repr c.2}]"
        let s1 :Symbol' := Springer.BD'_aux O1 c.1
        let s2 :Symbol' := Springer.C'_aux O2 c.2
        stdout.putStrLn s!"{repr s1.defect} ∼ {repr s2.defect}"

    return ()


unsafe def defectPairs (m n : ℕ) : IO <| Finset (ℤ × ℤ) := do
  if n % 2 = 1 then pure {}
  else
    let AllOS := AllOrthoSymplectic_relevent m n
    let mut res := []
    for p in AllOS do
      let O1 := projO p
      let O2 := projSp p
      let od ← gen_OS_od' p
      for c in od do
        let s1 : Symbol' := Springer.BD'_aux O1 c.1
        let s2 : Symbol' := Springer.C'_aux O2 c.2
        res := res.insert (s1.defect,s2.defect)
    let ret := res.toFinset
    IO.println s!"O({m})-Sp({n}) defect pairs: {repr ret}"
    return {}
/-
      od |> List.map (fun c =>
        let s1 :Symbol' := Springer.BD'_aux O1 c.1
        let s2 :Symbol' := Springer.C'_aux O2 c.2
        (s1.defect,s2.defect)
      ))
-/

/-
The program can select the defect pairs of the dual pair O(m)-Sp(n) and print them out.
-/
unsafe def corrSymbol (m n : ℕ) (select: Option (ℤ × ℤ):= none) (verb :ℕ:= 10): --IO <| Finset (ℤ × ℤ)
IO <| List (Symbol' × Symbol') × Finset (ℤ × ℤ)
:= do
  if n % 2 = 1 then pure ⟨[],{}⟩
  else
    let AllOS := AllOrthoSymplectic_relevent m n
    let mut AllD:= []
    let mut AllSpair:= []
    if verb >2  then
      IO.println "----------------------------------"
      IO.println s!"The dual pair O({m})-Sp({n})"
    else pure ()
    for p in AllOS do
      let O1 := projO p
      let O2 := projSp p
      let red := "\x1b[31m"
      let white:= "\x1b[0m"
      if verb >6 then
        IO.println <| red ++ s!"ab-diagram {repr p}" ++ white
        IO.println <| red ++ s!"Orbits [{repr O1}] <====> [{repr O2}]" ++ white
      else pure ()
      let od ← gen_OS_od' p
      for c in od do
        let s1 : Symbol' := Springer.BD'_aux O1 c.1
        let s2 : Symbol' := Springer.C'_aux O2 c.2
        if ¬ (select = none ∨ select = some (s1.defect, s2.defect)) then
          continue
        else
          if verb >8 then
            IO.println s!"{repr s1} ∼ {repr s2}"
          else pure ()
          AllD:= AllD.insert (s1.defect,s2.defect)
          AllSpair := AllSpair.insert (s1,s2)
    let AllD' := AllD.toFinset
    if verb >4 then
      IO.println s!"defect pairs: {repr AllD'}"
    else pure ()
    return ⟨AllSpair, AllD'⟩

/-
Type C modification of N by defect
N ↦ N - d * (d-1)
-/
def CmodifyN (N : ℕ) (d :ℤ) : ℕ := N - (d*(d-1)).toNat

/-
Type D modification of N by defect
N  ↦ N -(d * d -1)
-/
def DmodifyN (N : ℕ) (d :ℤ) : ℕ :=
  if N %2 = 0 then  N  - (d*d).toNat else N + 1 - (d*d).toNat


/-
The function test whether the correspondence of sysmbols are independent of defects
-/
unsafe def test_eqform (m n : ℕ) -- (select: Option (ℤ × ℤ):= none) (verb :ℕ:= 10)
: IO Unit := do
  let ⟨APairs,AllD⟩  ← corrSymbol m n (verb:=0)
  let restD:= AllD.filter (·  ≠ ((m:ℤ)%2,1))
  IO.println s!"Consider the dual pair: O({m})-Sp({n})"
  for dp in restD.1.unquot do
    IO.println <| String.replicate (40) '-'
    IO.println s!"Test defect pair: {repr dp}"
    let ⟨subpairs1,_⟩  ← corrSymbol m n (select:= some dp) (verb:=0)
    let mm := DmodifyN m dp.1
    let nn := CmodifyN n dp.2
    -- The standard correspondence
    let ⟨subpairs2,_⟩ ← corrSymbol mm nn  (select := some (mm%2,1)) (verb:=0)
    let toRepn := fun x : Symbol'×Symbol' => (x.1.BDSymbol_toBP.remove_zero, x.2.CSymbol_toBP.remove_zero)

    let rpairs1 := List.map toRepn subpairs1 |>.toFinset
    let rpairs2 := List.map toRepn subpairs2 |>.toFinset
    IO.println s!"The Springer model pairs: O({mm})-Sp({nn})"
    IO.println s!"|s1| = {repr rpairs1.card}, |Springer| = {repr rpairs2.card}"
    IO.println s!"s1-Springer: {repr (rpairs1 \ rpairs2)}"
    IO.println s!"Springer-s1 : {repr (rpairs2 \ rpairs1)}"

  return ()


end test_functions



section test

#eval corrSymbol 4 6

#eval corrSymbol 6 8 ((0,1):ℤ × ℤ) 5

#eval test_eqform 4 6

#eval test_eqform 14 29

/-
#eval corrSymbol 6 8 true
#eval corrSymbol 6 8
--#eval testOS 10 6
#eval defectPairs 20 16
#eval defectPairs 20 18
#eval defectPairs 18 20
#eval defectPairs 15 20
#eval defectPairs 17 20
#eval defectPairs 19 20
#eval defectPairs 19 22
#eval defectPairs 11 22
#eval defectPairs 25 22
-/

end test
