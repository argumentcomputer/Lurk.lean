import Lurk.Scalar.Datatypes

namespace Lurk.Evaluation

open Lean

abbrev PoseidonCache := HashMap (Array F) F

structure Ptr where
  tag : Tag
  val : USize
  deriving BEq, Hashable

structure ContPtr where
  tag : ContTag
  val : USize
  deriving BEq, Hashable

structure ConsData where 
  car : Ptr
  cdr : Ptr
  deriving BEq, Hashable

structure CommData where 
  hash : F
  val  : Ptr
  deriving BEq, Hashable

structure FunData where 
  arg  : Ptr
  body : Ptr
  env  : Ptr
  deriving BEq, Hashable

structure ThunkData where 
  val  : Ptr
  cont : ContPtr
  deriving BEq, Hashable

structure Call₀Data where 
  env   : Ptr
  cont  : ContPtr
  deriving BEq, Hashable

structure CallData where 
  unevaled : Ptr
  env      : Ptr
  cont     : ContPtr
  deriving BEq, Hashable

structure CallNextData where 
  function : Ptr
  env      : Ptr
  cont     : ContPtr
  deriving BEq, Hashable

structure TailData where 
  env  : Ptr
  cont : ContPtr
  deriving BEq, Hashable

structure LookupData where 
  env  : Ptr
  cont : ContPtr
  deriving BEq, Hashable

structure Op₁Data where 
  op   : Ptr
  cont : ContPtr
  deriving BEq, Hashable

structure Op₂Data where 
  op       : Ptr
  unevaled : Ptr
  env      : Ptr
  cont     : ContPtr
  deriving BEq, Hashable

structure Op₂NextData where 
  op     : Ptr
  evaled : Ptr
  cont   : ContPtr
  deriving BEq, Hashable

structure IfData where 
  unevaled : Ptr
  cont     : ContPtr
  deriving BEq, Hashable

structure LetTypeData where 
  var  : Ptr
  body : Ptr
  env  : Ptr
  cont : ContPtr
  deriving BEq, Hashable

structure EmitData where
  cont : ContPtr
  deriving BEq, Hashable

structure Store where
  consStore : HashSet ConsData
  commStore : HashSet CommData
  funStore : HashSet FunData
  symStore : HashSet String
  strStore : HashSet String
  thunkStore : HashSet ThunkData
  call₀Store : HashSet Call₀Data
  callStore : HashSet CallData
  callnextStore : HashSet CallNextData
  tailStore : HashSet TailData
  lookupStore : HashSet LookupData
  op₁Store : HashSet Op₁Data
  op₂Store : HashSet Op₂Data
  op₂nextStore : HashSet Op₂NextData
  ifStore : HashSet IfData
  letStore : HashSet LetTypeData
  letrecStore : HashSet LetTypeData
  emitStore : HashSet EmitData

  opaques : HashMap Ptr Scalar.ScalarPtr
  scalars : HashMap Scalar.ScalarPtr Ptr
  -- conts : HashMap Scalar.ScalarContPtr Ptr

  poseidonCache : PoseidonCache

  dehyrated : Array Ptr
  dehyratedConts : Array ContPtr
  opaqueCount : USize

inductive Expr where
  | nil : Expr
  | num : F → Expr
  | sym : String → Expr
  | str : String → Expr
  | char : Char → Expr
  | opaque : Ptr → Expr
  | cons : ConsData → Expr
  | comm : CommData → Expr
  | «fun» : FunData → Expr
  | thunk : ThunkData → Expr

inductive Continuation where
  | outermost : Continuation
  | call₀ : Call₀Data → Continuation
  | call : CallData → Continuation
  | callnext : CallNextData → Continuation
  | tail : TailData → Continuation
  | error : Continuation
  | lookup : LookupData → Continuation
  | op₁ : Op₁Data → Continuation
  | op₂ : Op₂Data → Continuation
  | op₂next : Op₂NextData → Continuation
  | «if» : IfData → Continuation
  | «let» : LetTypeData → Continuation
  | letrec : LetTypeData → Continuation
  | emit : EmitData → Continuation
  | dummy : Continuation
  | terminal : Continuation 

end Lurk.Evaluation
