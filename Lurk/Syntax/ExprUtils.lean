import Lurk.Syntax.AST
import Lurk.Syntax.DSL
import Std.Data.RBMap

namespace Lurk.Syntax.AST

def reservedSyms : Std.RBSet String compare := .ofList [
  "NIL",
  "T",
  "CURRENT-ENV",
  "BEGIN",
  "IF",
  "LAMBDA",
  "LET",
  "LETREC",
  "QUOTE",
  "ATOM",
  "CAR",
  "CDR",
  "EMIT",
  "COMMIT",
  "COMM",
  "OPEN",
  "NUM",
  "CHAR",
  "CONS",
  "STRCONS",
  "+" ,
  "-" ,
  "*" ,
  "/" ,
  "=" ,
  "<" ,
  ">" ,
  "<=" ,
  ">=" ,
  "EQ",
  "HIDE"
] _

def escapeSyms : AST → AST
  | sym s => if reservedSyms.contains s then sym s else sym s!"|{s}|"
  | cons x y => cons x.escapeSyms y.escapeSyms
  | x => x

def mkLambda (args : List String) (body : AST) : AST :=
  ~[sym "LAMBDA", consWith (args.map sym) nil, body]

def mkBindings (binders : List $ String × AST) : AST :=
  consWith (binders.map fun (s, v) => ~[sym s, v]) nil

def mkBlock (kind : String) (binders : List $ String × AST) (body : AST) : AST :=
  ~[sym kind, mkBindings binders, body]

def mkLet (binders : List $ String × AST) (body : AST) : AST :=
  mkBlock "LET" binders body

def mkLetrec (binders : List $ String × AST) (body : AST) : AST :=
  mkBlock "LETREC" binders body

def asArgs : AST → Except String (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← xs.asArgs)
  | x => throw s!"expected list of symbols but got {x}"

def asBindings : AST → Except String (List (String × AST))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← xs.asBindings)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

open Lurk.Syntax.DSL

mutual

partial def replaceBindersFreeVars
  (map : Std.RBMap String AST compare)
  (bindings : List $ String × AST)
  (rec : Bool) :
    List $ String × AST := Id.run do
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

partial def replaceFreeVars (map : Std.RBMap String AST compare) : AST → AST
  | x@(num _)
  | x@(char _)
  | x@(str _) => x
  | sym n => if reservedSyms.contains n then sym n else match map.find? n with
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

/--
Transforms a list of named expressions that were mutually defined into a
"switch" function `S` and a set of projections (named after the original names)
that call `S` with their respective indices.

Important: the resulting expressions must be bound in a `letrec`.
-/
def mkMutualBlock (mutuals : List (String × AST)) : List (String × AST) :=
  match mutuals with
  | [_] => mutuals
  | _ =>
    let names := mutuals.map Prod.fst
    let mutualName := names.foldl (fun acc n => s!"{acc}.{n}") "__mutual__"
    let fnProjs := names.enum.map fun (i, n) => (n, ~[.sym mutualName, .num i])
    let map := fnProjs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let mutualBlock := mkIfElses (mutuals.enum.map fun (i, _, e) =>
        (⟦(= mutidx $i)⟧, replaceFreeVars map e)
      ) ⟦nil⟧
    (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs


end Lurk.Syntax.AST
