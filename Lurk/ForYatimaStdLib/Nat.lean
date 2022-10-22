def Nat.asHex (n : Nat) (length : Nat) : String := 
  if n < USize.size then 
    toString n 
  else 
    let tail := Nat.toDigits 16 n
    let pad := List.replicate (length - tail.length) '0'
    "0x" ++  List.asString (pad ++ tail)
