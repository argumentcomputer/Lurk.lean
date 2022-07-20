import Lean
open Lean Elab Meta

inductive SExpr where 
  | atom : String → SExpr 
  | num  : Int → SExpr 
  | str  : String → SExpr
  | char : Char → SExpr
  | list : List SExpr → SExpr 
  | cons : SExpr → SExpr → SExpr 
  deriving Repr

namespace SExpr

declare_syntax_cat sexpr  
syntax "-" noWs num        : sexpr
syntax num                 : sexpr
syntax ident               : sexpr
syntax str                 : sexpr
syntax char                : sexpr
syntax "(" sexpr+ ")"      : sexpr
syntax sexpr " . " sexpr   : sexpr

partial def elabSExpr : Syntax → MetaM Expr
  | `(sexpr| -$n:num) => match n.getNat with 
    | 0     => do 
      let n ← mkAppM ``Int.ofNat #[mkConst ``Nat.zero]
      mkAppM ``SExpr.num #[n]
    | n + 1 => do
      let n ← mkAppM ``Int.negSucc #[mkNatLit n]
      mkAppM ``SExpr.num #[n]
  | `(sexpr| $n:num) => do 
    let n ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
    mkAppM ``SExpr.num #[n]
  | `(sexpr| $i:ident) => do 
    mkAppM ``SExpr.atom #[mkStrLit i.getId.toString]
  | `(sexpr| $s:str) => do 
    mkAppM ``SExpr.str #[mkStrLit s.getString]
  | `(sexpr| $c:char)  => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``SExpr.char #[c]
  | `(sexpr| ($es*)) => do 
    let es ← (es.mapM fun e => elabSExpr e)
    mkAppM ``SExpr.list #[← mkListLit (mkConst ``SExpr) es.toList]
  | `(sexpr| $e1 . $e2) => do
    mkAppM ``SExpr.cons #[← elabSExpr e1, ← elabSExpr e2]
  | _ => throwUnsupportedSyntax

partial def toString : SExpr → String 
  | .atom s     => s
  | .num n      => s!"{n}"
  | .str s      => s!"\"{s}\""
  | .char c     => s!"\'{c}\'"
  | .list es    => "(" ++ " ".intercalate (es.map toString) ++ ")"
  | .cons e1 e2 => toString e1 ++ " . " ++ toString e2

instance : ToString SExpr := ⟨toString⟩

elab "[SExpr| " e:sexpr "]" : term =>
  elabSExpr e

#eval [SExpr| 
 (a . b . c)
]

end SExpr 
