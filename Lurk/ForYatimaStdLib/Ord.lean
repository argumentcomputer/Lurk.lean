namespace Ord

instance [Ord α] [Ord β] : Ord (α × β) where compare
  | (a₁, b₁), (a₂, b₂) =>
    let a := compare a₁ a₂
    if a == .eq then compare b₁ b₂ else a

instance [Ord α] : Ord (Option α) where compare
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some a, some b => compare a b

end Ord
