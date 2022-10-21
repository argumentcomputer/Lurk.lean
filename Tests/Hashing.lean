import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.StoreDSL

open Lurk Hashing Syntax

def got := ⟦(lambda (x) (+ x x))⟧.hash.1

#eval got
open DSL in
def LEAN_actual := [store|

scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x29d35699bca46ab37ce4927a46657283ef41bc8502520e7ba82d05d45caf295d)): Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)), (cons, Scalar(0x3c8f93d8d851fe3d1e82eb38ca89215b2857d320bc720f0d66f0b5518aa1f408))),
  (cons, Scalar(0x350a36ba3d46e278ca108cd94008ffe38d47a1665eb137bd7e724e9f4560e0f1)): Cons((cons, Scalar(0x6235f2d4900b2a1ab2cbcfa6a38c4f5768516220c51f7a83158919f67b9c27cf)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x3c8f93d8d851fe3d1e82eb38ca89215b2857d320bc720f0d66f0b5518aa1f408)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x4164785a1aff4692994c80e74decca94552c243b8dbc5457be380ada8e02ecfb))),
  (cons, Scalar(0x4164785a1aff4692994c80e74decca94552c243b8dbc5457be380ada8e02ecfb)): Cons((nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)), (cons, Scalar(0x350a36ba3d46e278ca108cd94008ffe38d47a1665eb137bd7e724e9f4560e0f1))),
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x49b8f1a3ab095e3f85518e41aaf4cba9990ea6c9a11d1c4fbdad741ebb2dc7ed)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  (cons, Scalar(0x6235f2d4900b2a1ab2cbcfa6a38c4f5768516220c51f7a83158919f67b9c27cf)): Cons((sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)), (cons, Scalar(0x49b8f1a3ab095e3f85518e41aaf4cba9990ea6c9a11d1c4fbdad741ebb2dc7ed))),
  (sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): Sym((str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc))),
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (str, Scalar(0)): StrNil,
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): StrCons((char, '+'), (str, Scalar(0))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)): StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)): StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): StrCons((char, 'A'), (str, Scalar(0))),
  (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)): StrCons((char, 'D'), (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0))),
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)): StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)))
}

]

open DSL in
def expected := [store| 
-- BEGIN INPUT BELOW 
scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x260d89d830ea48cdc7314a9f9c1181381cabdd1db21002d3b929219553382c17)): Cons((cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)), (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  (cons, Scalar(0x19a091e5857edb8313fbfbb79694df57e2861b41738c02fb9ae31915aca7cac5)): Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)), (cons, Scalar(0x260d89d830ea48cdc7314a9f9c1181381cabdd1db21002d3b929219553382c17))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): StrCons((char, 'A'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)): StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)): StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)): StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe))),
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)): StrCons((char, 'D'), (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
}
-- END OF INPUT
].exprs

open LSpec in
#lspec
  let tSeq := test "Stores have the same size" (got.exprs.size == expected.size)
  expected.fold (init := tSeq) fun tSeq ptr expectedExpr =>
    withOptionSome s!"{ptr} is found" (got.exprs.find? ptr) fun gotExpr =>
      tSeq ++ test s!"Expression for key {ptr} matches"
        (expectedExpr == gotExpr)
