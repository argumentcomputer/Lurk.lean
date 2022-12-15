import Lurk.Frontend.Parser
import Lurk.Frontend.ToExpr
import Lurk.Backend.Eval

def eval (code : String) : String :=
  match Lurk.Frontend.Parser.parse code with
  | .error err => s!"Parsing error:\n{err}"
  | .ok x => match x.toExpr with
    | .error err => s!"Formatting error:\n{err}"
    | .ok e => match e.eval with
      | .error err => s!"Evaluation error:\n{err}"
      | .ok v => v.toString

def main : List String → IO UInt32
  | [] => do IO.eprintln "REPL TODO"; return 1
  | [file] => do
    let code ← IO.FS.readFile ⟨file⟩
    IO.println $ eval code
    return 0
  | _ => do IO.eprintln "Only one input file is accepted"; return 1
