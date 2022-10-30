import Lean
import Lurk.Syntax2.AST

namespace Lurk.Syntax

open Lean Elab Meta Term

scoped syntax "~[" withoutPosition(term,*) "]"  : term

macro_rules
  | `(~[ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(AST.cons $(⟨elems.elemsAndSeps.get! i⟩) $result))
    expandListLit elems.elemsAndSeps.size false (← ``(AST.nil))

end Lurk.Syntax
