import Unip.Partition
import Unip.Springer


section test_functions

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


unsafe def corrSymbol (m n : ℕ) (prin : Bool := false): IO <| Finset (ℤ × ℤ) := do
  if n % 2 = 1 then pure {}
  else
    let AllOS := AllOrthoSymplectic_relevent m n
    let mut res := []
    IO.println "----------------------------------"
    IO.println s!"The dual pair O({m})-Sp({n})"
    for p in AllOS do
      let O1 := projO p
      let O2 := projSp p
      let red := "\x1b[31m"
      let white:= "\x1b[0m"
      IO.println <| red ++ s!"Orbits [{repr O1}] <====> [{repr O2}]" ++ white
      let od ← gen_OS_od' p
      for c in od do
        let s1 : Symbol' := Springer.BD'_aux O1 c.1
        let s2 : Symbol' := Springer.C'_aux O2 c.2
        if prin ∧ s2.defect - s1.defect != 1 then
          continue
        else
          IO.println s!"{repr s1} ∼ {repr s2}"
          res := res.insert (s1.defect,s2.defect)
    let ret := res.toFinset
    IO.println s!"defect pairs: {repr ret}"
    return {}


end test_functions



section test

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
