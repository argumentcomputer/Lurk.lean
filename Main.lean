import Lurk.Parser
import Lurk.Eval
import Lurk.LightData

def eval (code : String) (store : Lurk.Scalar.Store) : String :=
  match Lurk.Parser.parse code with
  | .error err => s!"Parsing error:\n{err}"
  | .ok x => match x.toExpr with
    | .error err => s!"Formatting error:\n{err}"
    | .ok e => match e.eval store with
      | .error err => s!"Evaluation error:\n{err}"
      | .ok (v, n) => s!"[{n} iterations] => {v}"

def main : List String → IO UInt32
  | [file] => do
    let code ← IO.FS.readFile ⟨file⟩
    IO.println $ eval code default
    return 0
  | [file, store] => do
    let code ← IO.FS.readFile ⟨file⟩
    let store ← IO.FS.readBinFile ⟨store⟩
    let store : LightData ← match Encodable.decode store with
      | .ok (store : LightData) => pure store
      | .error err => IO.eprintln err; return 1
    let store : Lurk.Scalar.Store ← match Encodable.decode store with
      | .ok store => pure store
      | .error err => IO.eprintln err; return 1
    IO.println $ eval code store
    return 0
  | _ => do IO.eprintln "Arguments: <source> or <source store>"; return 1
