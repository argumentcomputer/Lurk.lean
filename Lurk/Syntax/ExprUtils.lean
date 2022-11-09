import Lurk.Syntax.AST
import Lurk.Syntax.DSL
import YatimaStdLib.Lean
import Std.Data.RBMap

namespace Lurk.Syntax.AST

def asArgs : AST → Except String (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← xs.asArgs)
  | x => throw s!"expected list of symbols but got {x}"

def asBindings : AST → Except String (List (String × AST))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← xs.asBindings)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

open Lurk.Syntax.DSL
open Lean (Name)

mutual

partial def replaceBindersFreeVars
  (map : Std.RBMap Name AST compare)
  (bindings : List $ Name × AST)
  (rec : Bool) :
    List $ Name × AST := Id.run do
  let mut ret := #[]
  -- `map'` will keep track of the free vars that will be replaced if found.
  let mut map' := map
  -- as we iterate on binders, occurrences of what looked like a free variable
  -- gradually turn into bound variables with local semantics. we erase them
  -- from `map'` because we don't want to replace them
  for (n, e) in bindings do
    if rec then
      -- an occurrence of `n` in `e` can be a recursion, so we can't replace it
      -- right away
      map' := map'.erase n
      ret := ret.push (n, replaceFreeVars map' e)
    else
      -- any occurrence of `n` in `e` is definitely a free variable, so we first
      -- try to replace it
      ret := ret.push (n, replaceFreeVars map' e)
      map' := map'.erase n
  return ret.data

partial def replaceFreeVars (map : Std.RBMap Name AST compare) : AST → AST
  | x@(num _)
  | x@(char _)
  | x@(str _) => x
  | sym n => match map.find? n with
    | some x => x
    | none => sym n
  -- todo
  | cons a b => cons (a.replaceFreeVars map) (b.replaceFreeVars map)

end

def mkIfElses (ifThens : List (AST × AST)) (finalElse : AST) : AST :=
  match ifThens with
  | [] => .nil
  | [(cond, body)] => ⟦(if $cond $body $finalElse)⟧
  | (cond, body) :: es => ⟦(if $cond $body $(mkIfElses es finalElse))⟧

def mkMutualBlock (mutuals : List (Name × AST)) : List (Name × AST) :=
  match mutuals with
  | [_] => mutuals
  | _ =>
    let names := mutuals.map Prod.fst
    let mutualName := names.foldl (init := `__mutual__) fun acc n => acc ++ n
    let fnProjs := names.enum.map fun (i, (n : Name)) => (n, ⟦($mutualName $i)⟧)
    let map := fnProjs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let mutualBlock := mkIfElses (mutuals.enum.map fun (i, _, e) =>
        (⟦(= mutidx $i)⟧, replaceFreeVars map e)
      ) ⟦nil⟧
    (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs


end Lurk.Syntax.AST
