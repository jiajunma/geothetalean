import Mathlib.Data.List.Range
import Mathlib.Data.Multiset.Range
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Multiset.Sort


-- We identify a partition as a multiset of natural number
-- Duality in Type A

def List.max (l : List ℕ ):= List.foldl Nat.max 0 l

#eval {1,2,3,4} |> List.max

def transpose (a : List ℕ) : List ℕ:=
  List.range a.max
  |> List.map (fun i => List.countP (fun x => x > i) a)
  |> List.filter (. != 0)


def l :List ℕ := [0,0,1,1,3,3,4,5]
#eval l |> transpose
#eval l |> transpose |> transpose


--def isTypeBD (a: Multiset ℕ):= ∀ i ∈ a, (i%2=0)-> Multiset.count i a %2 =0


def isTypeBD (a: List ℕ) : Option Unit:= do
  for i in a do
    if i %2 ==0 ∧ (List.count i a) % 2 != 0 then failure
  return ()


def isTypeC (a: List ℕ) : Option Unit:= do
  for i in a do
    if i %2 ==1 ∧ (List.count i a) % 2 != 0 then failure
  return ()




#eval [1,1,2,3,3] |> isTypeBD

#eval [1,1,2,3,3] |> isTypeC

