import YatimaStdLib.Nat
import YatimaStdLib.ByteArray

namespace Lurk

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fin N

def F.ofNat (n : Nat) : F :=
  .ofNat n

def F.asHex (n : F) : String :=
  n.val.asHex 64

instance : Inhabited F := ⟨.ofNat 0⟩

@[match_pattern] def F.zero : F :=
  .ofNat 0

@[inline] def F.toBytes (n : F) : ByteArray :=
  let bytes := n.val.toByteArrayLE
  bytes.pushZeros $ 32 - bytes.size

@[inline] def F.ofBytes (bytes : ByteArray) : F :=
  .ofNat bytes.asLEtoNat

inductive Num where
  | nat : Nat → Num
  | num : F → Num
  | u8 : UInt8 → Num
  | u16 : UInt16 → Num
  | u32 : UInt32 → Num
  | u64 : UInt64 → Num
  | usize : USize → Num
  deriving Ord, BEq, Repr, Inhabited

open Std Format in
instance : ToFormat Num where format
  | .nat x => format x
  | .num x => format x.asHex
  | .u8 x => format x ++ "u8"
  | .u16 x => format x ++ "u16"
  | .u32 x => format x ++ "u32"
  | .u64 x => format x ++ "u64"
  | .usize x => format x

open Std Format in
instance : ToString Num where
  toString := ToString.toString ∘ format

def Num.toNat : Num → Nat
  | .nat x => x
  | .num x => x.val 
  | .u8 x | .u16 x | .u32 x | .u64 x | .usize x => x.toNat

@[inline] def Num.toF : Num → F
  | x => Fin.ofNat x.toNat

@[inline] def Num.toU8 : Num → UInt8
  | x => .ofNat x.toNat

@[inline] def Num.toU16 : Num → UInt16
  | x => .ofNat x.toNat

@[inline] def Num.toU32 : Num → UInt32
  | x => .ofNat x.toNat

@[inline] def Num.toU64 : Num → UInt64
  | x => .ofNat x.toNat

@[inline] def Num.toUSize : Num → USize
  | x => .ofNat x.toNat

def Num.type : Num → String
  | .nat _ => "nat" 
  | .num _ => "num" 
  | .u8 _ => "u8" 
  | .u16 _ => "u16" 
  | .u32 _ => "u32" 
  | .u64 _ => "u64" 
  | .usize _ => "usize" 

def Num.add : Num → Num → Except String Num
  | .nat x, .nat y     => pure $ .nat   $ x + y
  | .num x, .num y     => pure $ .num   $ x + y
  | .u8 x, .u8 y       => pure $ .u8    $ x + y
  | .u16 x, .u16 y     => pure $ .u16   $ x + y
  | .u32 x, .u32 y     => pure $ .u32   $ x + y
  | .u64 x, .u64 y     => pure $ .u64   $ x + y
  | .usize x, .usize y => pure $ .usize $ x + y
  | x, y => throw s!"cannot add mismatched data types {x.type} and {y.type}"

def Num.sub : Num → Num → Except String Num
  | .nat x, .nat y     => pure $ .nat   $ x - y
  | .num x, .num y     => pure $ .num   $ x - y
  | .u8 x, .u8 y       => pure $ .u8    $ x - y
  | .u16 x, .u16 y     => pure $ .u16   $ x - y
  | .u32 x, .u32 y     => pure $ .u32   $ x - y
  | .u64 x, .u64 y     => pure $ .u64   $ x - y
  | .usize x, .usize y => pure $ .usize $ x - y
  | x, y => throw s!"cannot subtract mismatched data types {x.type} and {y.type}"

def Num.mul : Num → Num → Except String Num
  | .nat x, .nat y     => pure $ .nat   $ x * y
  | .num x, .num y     => pure $ .num   $ x * y
  | .u8 x, .u8 y       => pure $ .u8    $ x * y
  | .u16 x, .u16 y     => pure $ .u16   $ x * y
  | .u32 x, .u32 y     => pure $ .u32   $ x * y
  | .u64 x, .u64 y     => pure $ .u64   $ x * y
  | .usize x, .usize y => pure $ .usize $ x * y
  | x, y => throw s!"cannot multiply mismatched data types {x.type} and {y.type}"

def Num.div : Num → Num → Except String Num
  | .nat x, .nat y     => pure $ .nat   $ x / y
  | .num x, .num y     => pure $ .num   $ x / y
  | .u8 x, .u8 y       => pure $ .u8    $ x / y
  | .u16 x, .u16 y     => pure $ .u16   $ x / y
  | .u32 x, .u32 y     => pure $ .u32   $ x / y
  | .u64 x, .u64 y     => pure $ .u64   $ x / y
  | .usize x, .usize y => pure $ .usize $ x / y
  | x, y => throw s!"cannot divide mismatched data types {x.type} and {y.type}"

def Num.lt : Num → Num → Except String Bool
  | .nat x, .nat y     => pure $ x < y
  | .num x, .num y     => pure $ x < y
  | .u8 x, .u8 y       => pure $ x < y
  | .u16 x, .u16 y     => pure $ x < y
  | .u32 x, .u32 y     => pure $ x < y
  | .u64 x, .u64 y     => pure $ x < y
  | .usize x, .usize y => pure $ x < y
  | x, y => throw s!"cannot compare mismatched data types {x.type} and {y.type}"

def Num.le : Num → Num → Except String Bool
  | .nat x, .nat y     => pure $ x ≤ y
  | .num x, .num y     => pure $ x ≤ y
  | .u8 x, .u8 y       => pure $ x ≤ y
  | .u16 x, .u16 y     => pure $ x ≤ y
  | .u32 x, .u32 y     => pure $ x ≤ y
  | .u64 x, .u64 y     => pure $ x ≤ y
  | .usize x, .usize y => pure $ x ≤ y
  | x, y => throw s!"cannot compare mismatched data types {x.type} and {y.type}"

def Num.gt : Num → Num → Except String Bool
  | x, y => Num.lt y x

def Num.ge : Num → Num → Except String Bool
  | x, y => Num.le y x

end Lurk
