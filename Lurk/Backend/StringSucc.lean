def Char.zero := Char.ofNat 48
def Char.succ (c : Char) : Char × Bool :=
  let n := c.val.toNat
  if n < 48 then (.ofNat 48, false)            -- before 0
  else if n < 57  then (.ofNat (n + 1), false) -- before 8
  else if n < 65  then (.ofNat 65, false)      -- before A
  else if n < 90  then (.ofNat (n + 1), false) -- before Z
  else if n < 97  then (.ofNat 97, false)      -- before a
  else if n < 122 then (.ofNat (n + 1), false) -- before z
  else (Char.zero, true)                       -- overflow

abbrev CharList := List Char

def CharList.zero : CharList := [Char.zero]
def CharList.succ : CharList → CharList
  | [] => .zero
  | c :: (cs : CharList) => match c.succ with
    | (c, false) => c :: cs
    | (c, true)  => c :: cs.succ

def String.zero : String := ⟨CharList.zero⟩
def String.succ (s : String) : String :=
  ⟨CharList.succ s.data⟩

def String.lt (a b : String) : Bool :=
  let (aLength, bLength) := (a.length, b.length)
  if aLength != bLength then aLength < bLength
  else a.data.reverse < b.data.reverse
