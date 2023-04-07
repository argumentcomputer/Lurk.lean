import Lurk.Field

inductive LDON
  | num : Lurk.F → LDON
  | u64 : UInt64 → LDON
  | char : Char → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Ord, BEq, Repr, Inhabited
