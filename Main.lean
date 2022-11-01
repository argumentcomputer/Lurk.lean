import Lurk.Syntax.Parser
import Lurk.Syntax.DSL
import Lurk.Evaluation.FromAST
import Lurk.Evaluation.Eval

def eval (code : String) : String :=
  match Lurk.Syntax.parse code with
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

open Lurk.Syntax.DSL in
def expr := ⟦(letrec ((exp (lambda (base)
                (lambda (exponent)
                  (if (= 0 exponent)
                      1
                      (* base ((exp base) (- exponent 1))))))))
        ((exp 5) 3))⟧

def evaluate (code : Lurk.Syntax.AST) : IO Unit :=
  match code.toExpr with
  | .ok e => match e.eval with
    | .ok v => IO.println v.toString
    | .error err => IO.println err
  | .error err => IO.println err

#eval evaluate expr