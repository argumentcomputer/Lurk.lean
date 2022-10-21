import Lean
import Lurk.Syntax.Literal

open Std 

namespace Lurk.Syntax

inductive SExpr where
  | lit : Literal → SExpr
  | cons : SExpr → SExpr → SExpr
  deriving Repr, BEq, Inhabited

namespace SExpr

open Format ToFormat in 
partial def pprint (e : SExpr) (pretty := true) : Format :=
  match e with
  | .lit l     => format l
  | e@(.cons ..) => 
    let (es, tail) := telescopeCons [] e
      let tail := match tail with
      | .lit Literal.nil => Format.nil
      | _ => line ++ "." ++ line ++ pprint tail pretty
      paren <| fmtList es ++ tail
where 
  telescopeCons (acc : List SExpr) (e : SExpr) := match e with
    | .cons e₁ e₂ => telescopeCons (e₁ :: acc) e₂
    | _ => (acc.reverse, e)
  fmtList (xs : List SExpr) := match xs with
    | [ ]   => Format.nil
    | [n]   => format (pprint n pretty)
    | n::ns => format (pprint n pretty) ++ line ++ fmtList ns

def mkListWith (es : List SExpr) (tail : SExpr) : SExpr := 
  es.foldr (fun e acc => .cons e acc) tail

def mkList (es : List SExpr) := mkListWith es (.lit .nil)

instance : ToFormat SExpr where 
  format := pprint

class ToSExpr (α : Type u) where 
  toSExpr : α → SExpr

instance : ToSExpr Nat where 
  toSExpr n := .lit $ .num $ Fin.ofNat n

instance : ToSExpr String where 
  toSExpr s := .lit $ .str s

instance : ToSExpr Char where 
  toSExpr c := .lit $ .char c

instance [ToSExpr α] : ToSExpr (List α) where 
  toSExpr as := mkList (as.map ToSExpr.toSExpr)

instance [ToSExpr α] : ToSExpr (Array α) where 
  toSExpr as := mkList (as.toList.map ToSExpr.toSExpr)

instance : ToSExpr SExpr where 
  toSExpr s := s

end SExpr

end Lurk.Syntax
