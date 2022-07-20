import Lurk.AST

namespace Lurk

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
  | .nil    => "nil"
  | .t      => "t"
  | .num  n => toString n
  | .str  s => s!"\"{s}\""
  | .char c => s!"\\{c}"

partial def SExpr.print : SExpr → String
  | .atom s     => s
  | .num  n     => s!"{n}"
  | .str  s     => s!"\"{s}\""
  | .char c     => s!"\'{c}\'"
  | .list es    => "(" ++ " ".intercalate (es.map SExpr.print) ++ ")"
  | .cons e1 e2 => e1.print ++ " . " ++ e2.print

partial def Expr.print : Expr → String
  | .lit l => toString l
  | .sym n => toString n
  | .ifE test c alt => s!"(if {test.print} {c.print} {alt.print})"
  | .lam formals body => 
    let formals_text := " ".intercalate (formals.map toString)
    s!"(lambda ({formals_text}) {body.print})"
  | .letE bindings body => s!"(let {bindings.print} {body.print})"
  | .letRecE bindings body => s!"(let {bindings.print} {body.print})"
  | .quote datum => s!"(quote {datum.print})"
  | .cons a d => s!"(cons {a.print} {d.print})"
  | .strcons a d => s!"(strcons {a.print} {d.print})"
  | .consOp op expr => s!"({op} {expr.print})"
  | .numOp op expr₁ expr₂ => s!"({op} {expr₁.print} {expr₂.print})"
  | .relOp op expr₁ expr₂ => s!"({op} {expr₁.print} {expr₂.print})"
  | .emit expr => s!"(emit {expr.print})"
  | .begin exprs => 
    let exprs_text := " ".intercalate (exprs.map print)
    s!"(begin {exprs_text})"
  | .currEnv => "(current-env)"
  | .eval expr₁ expr₂? => match expr₂? with 
    | some expr₂ => s!"(eval {expr₁.print} {expr₂.print})"
    | none => s!"(eval {expr₁.print})"

