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


end test_functions



section test

--#eval testOS 10 6

#eval defectPairs 20 16
#eval defectPairs 20 18
#eval defectPairs 18 20
#eval defectPairs 15 20
#eval defectPairs 17 20
#eval defectPairs 19 20
#eval defectPairs 19 22
#eval defectPairs 11 22

end test
