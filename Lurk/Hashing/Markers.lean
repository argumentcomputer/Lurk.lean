import Lurk.Syntax.Literal

namespace Lurk.Hashing

abbrev F := Fin Lurk.Syntax.N

instance : Inhabited F := ⟨.ofNat 0⟩

def F.zero : F :=
  .ofNat 0

inductive Tag
  | nil
  | cons
  | sym
  | «fun»
  | num
  | thunk
  | str
  | char
  | comm
  deriving Ord, Inhabited, BEq, Repr

def Tag.toString : Tag → String
  | nil   => "nil"
  | cons  => "cons"
  | sym   => "sym"
  | .fun  => "fun"
  | num   => "num"
  | thunk => "thunk"
  | str   => "str"
  | char  => "char"
  | comm  => "comm"

def Tag.repr : Tag → String 
  | nil   => ".nil"
  | cons  => ".cons"
  | sym   => ".sym"
  | .fun  => ".fun"
  | num   => ".num"
  | thunk => ".thunk"
  | str   => ".str"
  | char  => ".char"
  | comm  => ".comm"

instance : ToString Tag := ⟨Tag.toString⟩

inductive ContTag
  | outermost
  | call0
  | call
  | call2
  | tail
  | error
  | lookup
  | unop
  | binop
  | binop2
  | «if»
  | «let»
  | letrec
  | dummy
  | terminal
  | emit

inductive Op1
  | car
  | cdr
  | atom
  | emit
  | «open»
  | secret
  | commit
  | num
  | comm
  | char

inductive Op2
  | sum
  | diff
  | product
  | quotient
  | equal
  | numEqual
  | less
  | greater
  | lessEqual
  | greaterEqual
  | cons
  | strcons
  | begin
  | hide

def Tag.toF : Tag → F
  | .nil   => .ofNat 0
  | .cons  => .ofNat 1
  | .sym   => .ofNat 2
  | .fun   => .ofNat 3
  | .num   => .ofNat 4
  | .thunk => .ofNat 5
  | .str   => .ofNat 6
  | .char  => .ofNat 7
  | .comm  => .ofNat 8

def ContTag.toF : ContTag → F
  | .outermost => .ofNat 4096
  | .call0     => .ofNat 4097
  | .call      => .ofNat 4098
  | .call2     => .ofNat 4099
  | .tail      => .ofNat 4100
  | .error     => .ofNat 4101
  | .lookup    => .ofNat 4102
  | .unop      => .ofNat 4103
  | .binop     => .ofNat 4104
  | .binop2    => .ofNat 4105
  | .if        => .ofNat 4106
  | .let       => .ofNat 4107
  | .letrec    => .ofNat 4108
  | .dummy     => .ofNat 4109
  | .terminal  => .ofNat 4110
  | .emit      => .ofNat 4111

def Op1.toF : Op1 → F
  | .car    => .ofNat 8192
  | .cdr    => .ofNat 8193
  | .atom   => .ofNat 8194
  | .emit   => .ofNat 8195
  | .open   => .ofNat 8196
  | .secret => .ofNat 8197
  | .commit => .ofNat 8198
  | .num    => .ofNat 8199
  | .comm   => .ofNat 8200
  | .char   => .ofNat 8201

def Op2.toF : Op2 → F
  | .sum          => .ofNat 12288
  | .diff         => .ofNat 12289
  | .product      => .ofNat 12290
  | .quotient     => .ofNat 12291
  | .equal        => .ofNat 12292
  | .numEqual     => .ofNat 12293
  | .less         => .ofNat 12294
  | .greater      => .ofNat 12295
  | .lessEqual    => .ofNat 12296
  | .greaterEqual => .ofNat 12297
  | .cons         => .ofNat 12298
  | .strcons      => .ofNat 12299
  | .begin        => .ofNat 12300
  | .hide         => .ofNat 12301

instance : Coe Tag     F := ⟨Tag.toF⟩
instance : Coe ContTag F := ⟨ContTag.toF⟩
instance : Coe Op1     F := ⟨Op1.toF⟩
instance : Coe Op2     F := ⟨Op2.toF⟩

end Lurk.Hashing
