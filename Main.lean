import Lurk.Parser
import Lurk.Eval
import Lurk.LightData

def eval (code : String) (store : Lurk.Scalar.Store) : IO UInt32 :=
  match Lurk.Parser.parse code with
  | .error err => do IO.eprintln s!"Parsing error:\n{err}"; return 1
  | .ok x => match x.toExpr with
    | .error err => do IO.eprintln s!"Formatting error:\n{err}"; return 1
    | .ok e => match e.evaluate store with
      | .ok (v, n) => do IO.println s!"[{n} iterations] => {v}"; return 0
      | .error (err, frames) => do
        IO.eprintln s!"Evaluation error:\n{err}"
        IO.FS.writeFile ⟨"frames"⟩ (frames.pprint 5)
        return 1

def main : List String → IO UInt32
  | [file] => do
    let code ← IO.FS.readFile ⟨file⟩
    eval code default
  | [file, store] => do
    let code ← IO.FS.readFile ⟨file⟩
    let store ← IO.FS.readBinFile ⟨store⟩
    let store : LightData ← match Encodable.decode store with
      | .ok (store : LightData) => pure store
      | .error err => IO.eprintln err; return 1
    let store : Lurk.Scalar.Store ← match Encodable.decode store with
      | .ok store => pure store
      | .error err => IO.eprintln err; return 1
    eval code store
  | _ => do IO.eprintln "Arguments: <source> or <source store>"; return 1
