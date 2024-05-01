import Lean
import Qq
import Mathlib.Tactic

open Lean Elab Command Term Meta

syntax (name := colortext) "#colortext" : command -- declare the syntax

@[command_elab colortext]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  let color := "red"
  let text := "hahaha"
  let html := s!"\x9b\x90\x10 <div style='color: {color};'>{text}</div>"
  logInfo s!"{html}"

elab "debug!" x:term : term => do
  let xs <- elabTermAndSynthesize x .none
  logInfo s!"{x}"
  IO.println s!"{repr x}"
  return xs

def test : ℕ :=
  let x := 42 + 21
  let y:= debug! x
  x

#eval test

#colortext
