import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.Scalar

def got := ⟦(cons (+ 1 (* 3 4)) "aa")⟧.hash.1
/-
scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x55eaf4c4ba094aa435a00252581737799a46f3fb500ae00d9bae8a68cdb5102a)): Cons((str, Scalar(0x305e2e1c649a9aa8fd9d58a5655afefe9d5fe4df9549ca0542e6dc9442dc3e52)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x10ad0e5adbdf4bedddb171070b61a75118a1ce4488e320c0b0cb6598f5b01c48)): Cons((sym, Scalar(0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617)), (cons, Scalar(0x71b048dad43fca8b8d611f29b18cb5165c2ecbd76f6a1f5a45ed8d200dbeaf8e))),
  (cons, Scalar(0x08feb0bdb06b3db06daa4fd84fe73943eb805be043fc8c704ea83fa79d4de151)): Cons((num, 1), (cons, Scalar(0x11e4e7290e8fa5c27b35bb0be398fd3e024eee3a8de84379224fbb327081fe99))),
  (cons, Scalar(0x3149ace43d4e562921ca294754a7b3a5b8341b698bd13c7b8407a26f9cf65e88)): Cons((sym, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)), (cons, Scalar(0x473253d62369309dd368fa761f523fa8bdb14e5ed638f9392940046922b285a1))),
  (cons, Scalar(0x71b048dad43fca8b8d611f29b18cb5165c2ecbd76f6a1f5a45ed8d200dbeaf8e)): Cons((num, 3), (cons, Scalar(0x526e51e2d54cd3ab850e06aab19873b272c03632c1449a7974588dd47ca8c1fa))),
  (cons, Scalar(0x11e4e7290e8fa5c27b35bb0be398fd3e024eee3a8de84379224fbb327081fe99)): Cons((cons, Scalar(0x10ad0e5adbdf4bedddb171070b61a75118a1ce4488e320c0b0cb6598f5b01c48)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x473253d62369309dd368fa761f523fa8bdb14e5ed638f9392940046922b285a1)): Cons((cons, Scalar(0x0652843c3af329c390f29ded051f259cffb490fffdf3825d085b412a76b5a4a7)), (cons, Scalar(0x55eaf4c4ba094aa435a00252581737799a46f3fb500ae00d9bae8a68cdb5102a))),
  (cons, Scalar(0x0652843c3af329c390f29ded051f259cffb490fffdf3825d085b412a76b5a4a7)): Cons((sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)), (cons, Scalar(0x08feb0bdb06b3db06daa4fd84fe73943eb805be043fc8c704ea83fa79d4de151))),
  (cons, Scalar(0x526e51e2d54cd3ab850e06aab19873b272c03632c1449a7974588dd47ca8c1fa)): Cons((num, 4), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (sym, Scalar(0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617)): Sym((str, Scalar(0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617))),
  (sym, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)): Sym((str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e))),
  (sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): Sym((str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc))),
  (num, 1): Num(1),
  (num, 3): Num(3),
  (num, 4): Num(4),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, I), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617)): StrCons((char, *), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)): StrCons((char, C), (str, Scalar(0x73b070801a151f5d7aedac8c66babb4ebef568b8b3c54eee50f2effea84cdfaf))),
  (str, Scalar(0x305e2e1c649a9aa8fd9d58a5655afefe9d5fe4df9549ca0542e6dc9442dc3e52)): StrCons((char, a), (str, Scalar(0x3d99599a501448d12695ad23f7e36a8eb17fef304a619c5ae8015755fae9b79b))),
  (str, Scalar(0x4074aab25ec2c5432d7f348b21c8aa8ea180e6bfbbd30ed2903261e9cadc9a6b)): StrCons((char, S), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, L), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x3d99599a501448d12695ad23f7e36a8eb17fef304a619c5ae8015755fae9b79b)): StrCons((char, a), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x73b070801a151f5d7aedac8c66babb4ebef568b8b3c54eee50f2effea84cdfaf)): StrCons((char, O), (str, Scalar(0x30bf0575b3a82eeab92a65acefb630cd01853be3b2183f400009ab3e0b735ac4))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, N), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x30bf0575b3a82eeab92a65acefb630cd01853be3b2183f400009ab3e0b735ac4)): StrCons((char, N), (str, Scalar(0x4074aab25ec2c5432d7f348b21c8aa8ea180e6bfbbd30ed2903261e9cadc9a6b))),
  (str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): StrCons((char, +), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
}
-/

open Lurk.Hashing

def expected : Std.RBMap ScalarPtr ScalarExpr compare := .ofList [
  (⟨Tag.num, .ofNat 1⟩, .num (.ofNat 1)),
  (⟨Tag.num, .ofNat 3⟩, .num (.ofNat 3)),
  (⟨Tag.num, .ofNat 4⟩, .num (.ofNat 4)),
  (⟨Tag.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩,
    .sym ⟨Tag.str, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩)
]

open LSpec in
def main := do
  -- this should be replaced by a complete equality of RBMaps
  let tSeq : TestSeq := expected.fold (init := .done) fun tSeq ptr expectedExpr =>
    withOptionSome s!"{ptr} is found" (got.exprs.find? ptr) fun gotExpr =>
      tSeq ++ test s!"Expected ({expectedExpr}) equals resulting expression ({gotExpr})"
        (expectedExpr == gotExpr)
  lspecIO tSeq

#eval got
#eval ⟦(let ((a 1) (b 2)) a)⟧.hash.1
