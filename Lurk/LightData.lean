import LightData
import Lurk.Scalar

namespace Lurk.LightData

open Scalar

scoped notation "dec" x => Encodable.decode x

instance : Encodable F LightData where
  encode x := x.val
  decode x := return (.ofNat $ ← dec x)

instance : Encodable Tag LightData where
  encode x := x.toF
  decode x := do match Tag.ofF (← dec x) with
    | some t => return t
    | none => throw s!"Invalid encoding for Tag: {x}"

instance : Encodable ScalarPtr LightData where
  encode | ⟨x, y⟩ => .cell #[x, y]
  decode
    | .cell #[x, y] => return ⟨← dec x, ← dec y⟩
    | x => throw s!"Invalid encoding for ScalarPtr: {x}"

instance : Encodable ScalarExpr LightData where
  encode
    | .nil    => 0
    | .strNil => 1
    | .symNil => 2
    | .num  x => .cell #[false, x]
    | .char x => .cell #[true,  x]
    | .cons    x y => .cell #[0, x, y]
    | .strCons x y => .cell #[1, x, y]
    | .symCons x y => .cell #[2, x, y]
    | .comm    x y => .cell #[3, x, y]
  decode
    | 0 => return .nil
    | 1 => return .strNil
    | 2 => return .symNil
    | .cell #[false, x] => return .num  (← dec x)
    | .cell #[true,  x] => return .char (← dec x)
    | .cell #[0, x, y] => return .cons    (← dec x) (← dec y)
    | .cell #[1, x, y] => return .strCons (← dec x) (← dec y)
    | .cell #[2, x, y] => return .symCons (← dec x) (← dec y)
    | .cell #[3, x, y] => return .comm    (← dec x) (← dec y)
    | x => throw s!"Invalid encoding for ScalarExpr: {x}"

-- def LDONToLightData : LDON → LightData
--   | .nil => false
--   | .sym  x => .cell #[.atom ⟨#[ ]⟩, x] -- the most frequent
--   | .num  x => .cell #[.cell  #[ ] , x]
--   | .str  x => .cell #[.atom ⟨#[0]⟩, x]
--   | .char x => .cell #[.atom ⟨#[1]⟩, x]
--   | .u64  x => .cell #[.atom ⟨#[2]⟩, x]
--   | .cons x y => .cell #[false, LDONToLightData x, LDONToLightData y]

-- partial def lightDataToLDON : LightData → Except String LDON
--   | false => return .nil
--   | .cell #[.atom ⟨#[ ]⟩, x] => return .sym  (← dec x)
--   | .cell #[.cell  #[ ] , x] => return .num  (← dec x)
--   | .cell #[.atom ⟨#[0]⟩, x] => return .str  (← dec x)
--   | .cell #[.atom ⟨#[1]⟩, x] => return .char (← dec x)
--   | .cell #[.atom ⟨#[2]⟩, x] => return .u64  (← dec x)
--   | .cell #[false, x, y] => return .cons (← lightDataToLDON x) (← lightDataToLDON y)
--   | x => throw s!"Invalid encoding for LDON: {x}"

-- instance : Encodable LDON LightData where
--   encode := LDONToLightData
--   decode := lightDataToLDON

instance [Encodable (Array (α × β)) LightData] [Ord α] :
    Encodable (Std.RBMap α β compare) LightData where
  encode x := (x.foldl (·.push (·, ·)) #[] : Array (α × β))
  decode x := return .ofArray (← dec x) _

instance : Encodable LDONHashState LightData where
  encode
    | ⟨store, chars, _⟩ => .cell #[store, chars.mapKeys String.mk]
  decode
    | .cell #[store, chars] => do
      let chars : Std.RBMap String ScalarPtr compare ← dec chars
      return ⟨← dec store, chars.mapKeys String.data, default⟩
    | x => throw s!"Invalid encoding for LDONHashState: {x}"
