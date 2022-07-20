import Lurk.AST

open Lurk

instance : ToString Num where
  toString num := toString num.data

instance : ToString Name where
  toString name := name.data

instance : ToString ConsOp where toString
  | .car  => "car"
  | .cdr  => "cdr"
  | .atom => "atom"
  | .emit => "emit"

instance : ToString NumOp where toString
  | .sum  => "+"
  | .diff => "-"
  | .prod => "*"
  | .quot => "/"

instance : ToString RelOp where toString
  | .eq  => "="
  | .nEq => "eq" -- NOTE: This was an unfortunate choice, maybe swap definitions in the AST?

instance : ToString Literal where toString
  | .nil => "nil"
  | .t => "t"
  | .num n  => toString n
  | .str s  => s!"\"{s}\""
  | .char c => s!"\\{c}"

partial def print : Expr → String
  | .lit l => toString l
  | .sym n => toString n
  | .ifE test cons alt => s!"(if {print test} {print cons} {print alt})"
  | .lam formals body => 
    let formals_text := " ".intercalate (formals.map toString)
    s!"(lambda ({formals_text}) {print body})"
  | .letE bindings body => s!"(let {print bindings} {print body})"
  | .letRecE bindings body => s!"(let {print bindings} {print body})"
  | .quote datum => s!"(quote {datum})"
  | .cons a d => s!"(cons {print a} {print d})"
  | .strcons a d => s!"(strcons {print a} {print d})"
  | .consOp op expr => s!"({op} {print expr})"
  | .numOp op expr₁ expr₂ => s!"({op} {print expr₁} {print expr₂})"
  | .relOp op expr₁ expr₂ => s!"({op} {print expr₁} {print expr₂})"
  | .emit expr => s!"(emit {print expr})"
  | .begin exprs => 
    let exprs_text := " ".intercalate (exprs.map print)
    s!"(begin {exprs_text})"
  | .currEnv => "(current-env)"
  | .eval expr₁ expr₂? => match expr₂? with 
    | some expr₂ => s!"(eval {print expr₁} {print expr₂})"
    | none => s!"(eval {print expr₁})"

instance : Repr Expr where 
  reprPrec := fun e _ => print e
