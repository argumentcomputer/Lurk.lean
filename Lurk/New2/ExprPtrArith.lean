import Lurk.New2.Pointers

def ExprPtr.add : ExprPtr → ExprPtr → Except String ExprPtr
  | ⟨.num, x⟩, ⟨.num, y⟩
  | ⟨.u64, x⟩, ⟨.num, y⟩
  | ⟨.num, x⟩, ⟨.u64, y⟩ => return ⟨.num, x + y⟩
  | ⟨.u64, x⟩, ⟨.u64, y⟩ => return ⟨.u64, .ofNat $ (x + y).val.toUInt64.toNat⟩
  | _, _ => throw ""

def ExprPtr.numEq : ExprPtr → ExprPtr → Except String Bool
  | ⟨.num, x⟩, ⟨.num, y⟩
  | ⟨.u64, x⟩, ⟨.num, y⟩
  | ⟨.num, x⟩, ⟨.u64, y⟩
  | ⟨.u64, x⟩, ⟨.u64, y⟩ => return x == y
  | _, _ => throw ""
