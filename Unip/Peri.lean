import Unip.Symbol
import Unip.Partition

open List

@[ext]
structure LPart where
  L : List ℕ
  le :  L.Chain' (· ≤ ·)
  deriving BEq, Hashable, Repr

-- The skipping symbols
@[ext]
structure SSymbol where
  S : List ℕ
  lt : S.Chain' (· + 1 < · )

namespace LPart
instance coe : Coe LPart (List ℕ) where
  coe := fun x => x.L


structure pre (a b : LPart) where
  eqlength : a.L.length=b.L.length
  Peri : ∀ i: Fin (a.L.length),
          let x := a.L[i]
          let y := b.L[i]
          (x ≤ y ∧ y ≤ x+1)

def toSymbol_aux (L: List ℕ ) : List ℕ := zipWith  (· +  2*·) L (List.range L.length)

#check List.chain'_cons'

def toSymbol_aux_lemma (L : List ℕ) (hL : L.Chain' (· ≤ ·)) : toSymbol_aux L |> List.Chain' (· +1 < · ) := by
    have range_one : List.range 1 = [0] := by simp [List.range,List.range.loop]
    rw [toSymbol_aux]
    induction' L with hd tail ih
    . simp
    . have H1 : (hd::tail).length = 1 + tail.length := by simp;linarith
      simp only [H1, List.range_add, range_one, List.singleton_append, List.zip_cons_cons, List.map_cons, mul_zero, add_zero]
      apply List.chain'_cons'.2
      constructor
      . match tail with
        | [] => simp
        | hh::tt =>
          have H2 : (hh::tt).length  = 1+ tt.length := by simp; linarith
          simp [H2,List.range_add,range_one]
          have : hd ≤ hh:= (chain'_cons.1 hL).1
          linarith
      . have H3 : List.Chain' (· ≤ ·) tail := (chain'_cons'.1  hL).2
        replace ih:= ih H3
        rw [zipWith_map_right]
        have H4 : zipWith (fun a b:ℕ =>  a + 2*(1+b)) tail (range tail.length)
                = (map (fun x : ℕ => x+2) $ zipWith (fun a b => a + 2 * b) tail (range tail.length))
               := by
                  rw [map_zipWith]
                  congr;ext;linarith
        rw [H4,chain'_map]
        have H5 : fun a b => a+2 +1< b+2 = fun a b => a +1 < b
          := by ext;constructor <;> (intro;linarith)
        rw [H5]
        exact ih

/-
    . match tail with
      | [] =>
        simp [List.length_singleton,range_one]
      | hh::tt =>
        have H1 : (hd::(hh::tt)).length = 2 + tt.length := by simp;linarith
        simp [List.chain'_map,List.range_add,H1,range_two]
        have H2 := List.chain'_cons.1 hL
        constructor
        . linarith [H2.1]
        . have : (hh + 2) :: List.map (fun a ↦ a.1 + 2 * a.2) (List.zip tt (List.map (fun x ↦ 2 + x) (List.range (List.length tt))  = List.map (· + 2) <|
          List.map (fun a => a.1 + 2* a.2) List.zip (hh::tt)
-/


def toSymbol (a : LPart) : SSymbol where
  S :=  List.zip a.L (List.range a.L.length) |> List.map (fun a => a.1 + 2*a.2)
  lt := by
    let L := a.L
    have cL := a.le
    have range_one : List.range 1 = [0] := by simp [List.range,List.range.loop]
    have range_two : List.range 2 = 0::1::[] := by simp [List.range,List.range.loop]
    induction' a.L with hd tail ih
    . simp
    . match tail with
      | [] =>
        simp [List.length_singleton,range_one]
      | hh::tt =>
        have H1 : (hd::(hh::tt)).length = 2 + tt.length := by simp;linarith
        simp [List.chain'_map,List.range_add,H1,range_two]
        simp at cL





end LPart
