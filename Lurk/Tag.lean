import Lurk.Literal

namespace Lurk

inductive Tag where
  | nil
  | cons
  | sym
  | «fun»
  | num
  | thunk
  | str
  | char
  | comm
  deriving Ord

def Tag.hash : Tag → F
  | .nil   => .ofNat 0
  | .cons  => .ofNat 1
  | .sym   => .ofNat 2
  | .fun   => .ofNat 3
  | .num   => .ofNat 4
  | .thunk => .ofNat 5
  | .str   => .ofNat 6
  | .char  => .ofNat 7
  | .comm  => .ofNat 8