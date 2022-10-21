import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.StoreDSL

open Lurk Hashing Syntax

def got := ⟦(lambda (x) x)⟧.hash.1

#eval got
open DSL in
def LEAN_actual := [store|

scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x1614c0472b21795fb6e510fe9925d14c4dcc6059975a82179a9730c2520af4ce)): Cons((cons, Scalar(0x5b65137fe7079e2274099ecdbc12aa209b0a1005f55ece636c1c692dd7e13b83)), (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  (cons, Scalar(0x3ec762f69bbabab682911c4c5931d62cc94733445daba490fa69d86fe759b939)): Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)), (cons, Scalar(0x1614c0472b21795fb6e510fe9925d14c4dcc6059975a82179a9730c2520af4ce))),
  (cons, Scalar(0x42570206e353787d3b347f3f169a8a985214d6745648a715ecb6f48822d8ce6e)): Cons((nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x5b65137fe7079e2274099ecdbc12aa209b0a1005f55ece636c1c692dd7e13b83)): Cons((sym, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)), (cons, Scalar(0x70383d784f29214ec93bf685adea00f830ebe5ae32c0c84a2c1fab9e4c9029f2))),
  (cons, Scalar(0x70383d784f29214ec93bf685adea00f830ebe5ae32c0c84a2c1fab9e4c9029f2)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x42570206e353787d3b347f3f169a8a985214d6745648a715ecb6f48822d8ce6e))),
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  (sym, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)): Sym((str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (str, Scalar(0)): StrNil,
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x30bf0575b3a82eeab92a65acefb630cd01853be3b2183f400009ab3e0b735ac4)): StrCons((char, 'N'), (str, Scalar(0x4074aab25ec2c5432d7f348b21c8aa8ea180e6bfbbd30ed2903261e9cadc9a6b))),
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  (str, Scalar(0x4074aab25ec2c5432d7f348b21c8aa8ea180e6bfbbd30ed2903261e9cadc9a6b)): StrCons((char, 'S'), (str, Scalar(0))),
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)): StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)): StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): StrCons((char, 'A'), (str, Scalar(0))),
  (str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)): StrCons((char, 'C'), (str, Scalar(0x73b070801a151f5d7aedac8c66babb4ebef568b8b3c54eee50f2effea84cdfaf))),
  (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)): StrCons((char, 'D'), (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0))),
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)): StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe))),
  (str, Scalar(0x73b070801a151f5d7aedac8c66babb4ebef568b8b3c54eee50f2effea84cdfaf)): StrCons((char, 'O'), (str, Scalar(0x30bf0575b3a82eeab92a65acefb630cd01853be3b2183f400009ab3e0b735ac4)))
}

]

open DSL in
def expected := [store| 
-- BEGIN INPUT BELOW 
scalar_store: {
  -- nil
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  -- cons x nil
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  -- cons (x) nil
  (cons, Scalar(0x260d89d830ea48cdc7314a9f9c1181381cabdd1db21002d3b929219553382c17)): Cons((cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)), (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  -- (lambda (x) 
  (cons, Scalar(0x19a091e5857edb8313fbfbb79694df57e2861b41738c02fb9ae31915aca7cac5)): Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)), (cons, Scalar(0x260d89d830ea48cdc7314a9f9c1181381cabdd1db21002d3b929219553382c17))),
  -- sym `x
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  -- sym lambda
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  -- str ""
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  -- str "x"
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  -- str "IL"
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  -- str "A"
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): StrCons((char, 'A'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  -- str "L"
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  -- str "NIL"
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  -- str "AMBDA"
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)): StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  -- str "MBDA"
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)): StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  -- str "BDA"
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)): StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe))),
  -- str "LAMBDA"
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  -- str "DA"
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
