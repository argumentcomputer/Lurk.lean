import Lurk.Evaluation2.Expr

namespace Lurk.Evaluation

instance : ToString Op₁ where toString
  | .atom => "atom"
  | .car => "car"
  | .cdr => "cdr"
  | .emit => "emit"
  | .commit => "commit"
  | .comm => "comm"
  | .open => "open"
  | .num => "num"
  | .char => "char"

instance : ToString Op₂ where toString
  | .cons => "cons"
  | .strcons => "strcons"
  | .begin => "begin"
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .numEq => "="
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .eq => "eq"
  | .hide => "hide"

open Std.Format Std.ToFormat

-- def escName (name : Name) (pipes : Bool) : Format :=
--   if pipes then bracket "|" (validate name) "|" else validate name

partial def pprint (e : Expr) (pretty := true) (pipes := true) : Std.Format :=
  match e with
  | .lit l => format l
  | .sym s => format s -- escName n pipes
  | .if test con alt =>
    paren <| group ("if" ++ line ++ pprint test pretty pipes) ++ line ++
      pprint con pretty pipes ++ line ++ pprint alt pretty pipes
  | .lambda formals body =>
    paren <| "lambda" ++ line ++ paren (fmtNames formals) ++ indentD (pprint body pretty pipes)
  | .let n e body =>
    paren <| "let" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty pipes
  | .letrec n e body =>
    paren <| "letrec" ++ line ++ paren (fmtBinds bindings) ++ line ++ pprint body pretty pipes
  | e@(.app ..) =>
    let (fn, args) := telescopeApp e []
    let args := if args.length == 0 then .nil else indentD (fmtList args)
    paren <| pprint fn pretty pipes ++ args
  | .quote datum =>
    paren <| "quote" ++ line ++ datum.pprint pretty
  | .binaryOp op expr₁ expr₂ =>
    paren <| format op ++ line ++ pprint expr₁ pretty pipes ++ line ++ pprint expr₂ pretty pipes
  | .atom expr => paren <| "atom" ++ line ++ pprint expr pretty pipes
  | .cdr expr => paren <| "cdr" ++ line ++ pprint expr pretty pipes
  | .car expr => paren <| "car" ++ line ++ pprint expr pretty pipes
  | .emit expr => paren <| "emit" ++ line ++ pprint expr pretty pipes
  | .cons e₁ e₂ =>
    paren <| group ("cons" ++ line ++ pprint e₁ pretty pipes) ++ line ++ pprint e₂ pretty pipes
  | .strcons e₁ e₂ =>
    paren <| group ("strcons" ++ line ++ pprint e₁ pretty pipes) ++ line ++ pprint e₂ pretty pipes
  | .begin e₁ e₂ =>
    paren <| group ("begin" ++ line ++ pprint e₁ pretty pipes) ++ line ++ pprint e₂ pretty pipes
  | .currEnv => "current-env"
  | .hide e₁ e₂ =>
    paren <| group ("hide" ++ line ++ pprint e₁ pretty pipes) ++ line ++ pprint e₂ pretty pipes
  | .commit e => paren $ "commit" ++ line ++ (pprint e pretty pipes)
  | .comm e => paren $ "comm" ++ line ++ (pprint e pretty pipes)
where
  fmtNames (xs : List Name) := match xs with
    | [] => Format.nil
    | [n]  => escName n pipes
    | n::ns => escName n pipes ++ line ++ fmtNames ns
  fmtList (xs : List Expr) := match xs with
    | [] => Format.nil
    | [e]  => pprint e pretty pipes
    | e::es => pprint e pretty pipes ++ line ++ fmtList es
  fmtBinds (xs : List (Name × Expr)) := match xs with
    | [] => Format.nil
    | [(n, e)]  => paren <| escName n pipes ++ line ++ pprint e pretty
    | (n, e)::xs =>
      (paren $ escName n pipes ++ line ++ pprint e pretty) ++ line ++ fmtBinds xs
  telescopeApp (e : Expr) (args : List Expr) := match e with 
    | .app fn arg? => match arg? with
      | some arg => telescopeApp fn <| arg :: args
      | none => (fn, args)
    | _ => (e, args)

instance : ToFormat Expr where
  format := pprint

end Lurk.Evaluation
