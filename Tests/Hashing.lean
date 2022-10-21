import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.Scalar

def got := ⟦
  (letrec (
      (f (lambda (x)
        (if (= x 140)
          123
          (f (+ x 1))))))
    (f 0))⟧.hash.1

open Lurk Hashing Syntax

def doesthiswork : ScalarStore := ⟨Std.RBMap.ofList [
  (⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩, .sym ⟨.str, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.str, mkF 0⟩, .strNil),
  (⟨.str, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩, .strCons ⟨.char, 'N'⟩ ⟨.str, mkF 0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09⟩),
  (⟨.str, mkF 0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570⟩, .strCons ⟨.char, 'L'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09⟩, .strCons ⟨.char, 'I'⟩ ⟨.str, mkF 0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570⟩)
]⟩

def expected : Std.RBMap ScalarPtr ScalarExpr compare := Std.RBMap.ofList [
  (⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩, .sym ⟨.str, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x00c832b869f99c9471fba9ed4e78d4ddcf991fa2ddfce3cc4674bd9bc708ac0d⟩, .cons ⟨.num, mkF 140⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x01eba203e932a427d14ec047f99c4638fc2d5d48b6c6151cb1cdfc8e5b3ee917⟩, .cons ⟨.sym, mkF 0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa⟩ ⟨.cons, mkF 0x40524a50b2af5e53b6a445907f5446df6887c032d93ffa8ca1de6c11892bfc8b⟩),
  (⟨.cons, mkF 0x0dc9d3eafdb06aabc1bcec843de58d1160756de429900967eda4bd7dd28b4f73⟩, .cons ⟨.cons, mkF 0x259eab0d659a366e7dc48e17adb7e6353a7f2990fe4dbb9536de4147d8951880⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x1085b34caf96ad1f09fb0b96a94e162e5faa5311de0436731441a151fe61ef84⟩, .cons ⟨.num, mkF 1⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x164704591ff0301ca33c06310cb9125bf90327e58b33422f41cae5653db6c3f4⟩, .cons ⟨.num, mkF 0⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x167c01e67ac98134f69d39b28edb48fe025a9e8768ebdd27c64258da8ee31b23⟩, .cons ⟨.cons, mkF 0x296fda907f44d2a9620ba9699e18002c3e6fd93decd5297d07699154a201bc21⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x19a3b094086e444c40caeab4a44118c10f3e23fe2724b93b377b689783c9032a⟩, .cons ⟨.cons, mkF 0x666902b83c2908c30b051b2df8fb34d2428106ce032969441e49a18a1343684a⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x20f08930f3993ed1975531f9deb52fd07b591a902ad525089d10559c164e5745⟩, .cons ⟨.cons, mkF 0x492a6d8b9cb29ccbb533877c307f96635d92bb2b9e9c5636bba567b84f510db4⟩ ⟨.cons, mkF 0x3164a4c50681c880940b73bd17973017e2cb5e4af3b510649912b1a7d8351bf9⟩),
  (⟨.cons, mkF 0x259eab0d659a366e7dc48e17adb7e6353a7f2990fe4dbb9536de4147d8951880⟩, .cons ⟨.sym, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩ ⟨.cons, mkF 0x164704591ff0301ca33c06310cb9125bf90327e58b33422f41cae5653db6c3f4⟩),
  (⟨.cons, mkF 0x296fda907f44d2a9620ba9699e18002c3e6fd93decd5297d07699154a201bc21⟩, .cons ⟨.sym, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩ ⟨.cons, mkF 0x518e64eb92ace8566d4c3e8c5ce0287a87a7eb66db6c3ecf5ed2629489a0b76c⟩),
  (⟨.cons, mkF 0x2d7a1f791793eef9dab1e8b58ea8095ca7b2c9bcf86257fd072eed0a47070a6a⟩, .cons ⟨.sym, mkF 0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600⟩ ⟨.cons, mkF 0x1085b34caf96ad1f09fb0b96a94e162e5faa5311de0436731441a151fe61ef84⟩),
  (⟨.cons, mkF 0x3164a4c50681c880940b73bd17973017e2cb5e4af3b510649912b1a7d8351bf9⟩, .cons ⟨.num, mkF 123⟩ ⟨.cons, mkF 0x606ca42c09873a0204969f02c9c589a219eb8660d0ce64f56e29e9f586dfcef1⟩),
  (⟨.cons, mkF 0x40524a50b2af5e53b6a445907f5446df6887c032d93ffa8ca1de6c11892bfc8b⟩, .cons ⟨.cons, mkF 0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110⟩ ⟨.cons, mkF 0x5ae50ac92ff211857e9564c2ffebfe27a308b2d08f74aa9cfdd0376696649015⟩),
  (⟨.cons, mkF 0x421a5703e5f207abb53952fe1fca08665871356caa6cb90281071ef2fa20ed17⟩, .cons ⟨.sym, mkF 0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600⟩ ⟨.cons, mkF 0x00c832b869f99c9471fba9ed4e78d4ddcf991fa2ddfce3cc4674bd9bc708ac0d⟩),
  (⟨.cons, mkF 0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110⟩, .cons ⟨.sym, mkF 0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x492a6d8b9cb29ccbb533877c307f96635d92bb2b9e9c5636bba567b84f510db4⟩, .cons ⟨.sym, mkF 0x63f54baca36ac31205e11d1bcd336891c40ae48b9a29b3683a7eb9f430fd4a4b⟩ ⟨.cons, mkF 0x421a5703e5f207abb53952fe1fca08665871356caa6cb90281071ef2fa20ed17⟩),
  (⟨.cons, mkF 0x518e64eb92ace8566d4c3e8c5ce0287a87a7eb66db6c3ecf5ed2629489a0b76c⟩, .cons ⟨.cons, mkF 0x01eba203e932a427d14ec047f99c4638fc2d5d48b6c6151cb1cdfc8e5b3ee917⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x5ae50ac92ff211857e9564c2ffebfe27a308b2d08f74aa9cfdd0376696649015⟩, .cons ⟨.cons, mkF 0x7313319db660bd6107aa994c031398b3d1e657fae23aaf2f023efcccb3aea3f6⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x5c34f91a21d63c1686ea1bb5c6ba964977e7434572b8655bd35bb9319747d732⟩, .cons ⟨.sym, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩ ⟨.cons, mkF 0x19a3b094086e444c40caeab4a44118c10f3e23fe2724b93b377b689783c9032a⟩),
  (⟨.cons, mkF 0x606ca42c09873a0204969f02c9c589a219eb8660d0ce64f56e29e9f586dfcef1⟩, .cons ⟨.cons, mkF 0x5c34f91a21d63c1686ea1bb5c6ba964977e7434572b8655bd35bb9319747d732⟩ ⟨.nil, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),
  (⟨.cons, mkF 0x61d8245eb697e1b7527cd6a4d2ffb3e7a4ff3a4860a9d752f2be8be590c589e9⟩, .cons ⟨.cons, mkF 0x167c01e67ac98134f69d39b28edb48fe025a9e8768ebdd27c64258da8ee31b23⟩ ⟨.cons, mkF 0x0dc9d3eafdb06aabc1bcec843de58d1160756de429900967eda4bd7dd28b4f73⟩),
  (⟨.cons, mkF 0x62e0d6adecd830820d4dd14ccf8824e741ece8e19bd6f769a6fbdd3e6be94c00⟩, .cons ⟨.sym, mkF 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩ ⟨.cons, mkF 0x61d8245eb697e1b7527cd6a4d2ffb3e7a4ff3a4860a9d752f2be8be590c589e9⟩),
  (⟨.cons, mkF 0x666902b83c2908c30b051b2df8fb34d2428106ce032969441e49a18a1343684a⟩, .cons ⟨.sym, mkF 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩ ⟨.cons, mkF 0x2d7a1f791793eef9dab1e8b58ea8095ca7b2c9bcf86257fd072eed0a47070a6a⟩),
  (⟨.cons, mkF 0x7313319db660bd6107aa994c031398b3d1e657fae23aaf2f023efcccb3aea3f6⟩, .cons ⟨.sym, mkF 0x5b99c690e9124338f91704cc89d273e470462ba12d8b436f5798387b1dacbe58⟩ ⟨.cons, mkF 0x20f08930f3993ed1975531f9deb52fd07b591a902ad525089d10559c164e5745⟩),
  (⟨.sym, mkF 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩, .sym ⟨.str, mkF 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩),
  (⟨.sym, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩, .sym ⟨.str, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩),
  (⟨.sym, mkF 0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa⟩, .sym ⟨.str, mkF 0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa⟩),
  (⟨.sym, mkF 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩, .sym ⟨.str, mkF 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩),
  (⟨.sym, mkF 0x5b99c690e9124338f91704cc89d273e470462ba12d8b436f5798387b1dacbe58⟩, .sym ⟨.str, mkF 0x5b99c690e9124338f91704cc89d273e470462ba12d8b436f5798387b1dacbe58⟩),
  (⟨.sym, mkF 0x63f54baca36ac31205e11d1bcd336891c40ae48b9a29b3683a7eb9f430fd4a4b⟩, .sym ⟨.str, mkF 0x63f54baca36ac31205e11d1bcd336891c40ae48b9a29b3683a7eb9f430fd4a4b⟩),
  (⟨.sym, mkF 0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600⟩, .sym ⟨.str, mkF 0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600⟩),
  (⟨.num, mkF 0⟩, .num (mkF 0)),
  (⟨.num, mkF 1⟩, .num (mkF 1)),
  (⟨.num, mkF 123⟩, .num (mkF 123)),
  (⟨.num, mkF 140⟩, .num (mkF 140)),
  (⟨.str, mkF 0⟩, .strNil),
  (⟨.str, mkF 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩, .strCons ⟨.char, 'N'⟩ ⟨.str, mkF 0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09⟩),
  (⟨.str, mkF 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩, .strCons ⟨.char, '+'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x1124e756c270500ff7dd307e51fd6ac22eecaab01bacf95ef21b20c1cb46388e⟩, .strCons ⟨.char, 'T'⟩ ⟨.str, mkF 0x2d86d91f2b22fde48a63157f54d012e1954235730e1da807f2f544c2bffdf359⟩),
  (⟨.str, mkF 0x177fbe789b31448e1e8018fcbe27664935c886b055de30d5f8a35c09982823f1⟩, .strCons ⟨.char, 'E'⟩ ⟨.str, mkF 0x278e640a53d1f53b2f51c80bb72724943bdaec2e33f0feddd1e44a078cb3bc10⟩),
  (⟨.str, mkF 0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570⟩, .strCons ⟨.char, 'L'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x278e640a53d1f53b2f51c80bb72724943bdaec2e33f0feddd1e44a078cb3bc10⟩, .strCons ⟨.char, 'C'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09⟩, .strCons ⟨.char, 'I'⟩ ⟨.str, mkF 0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570⟩),
  (⟨.str, mkF 0x2d86d91f2b22fde48a63157f54d012e1954235730e1da807f2f544c2bffdf359⟩, .strCons ⟨.char, 'R'⟩ ⟨.str, mkF 0x177fbe789b31448e1e8018fcbe27664935c886b055de30d5f8a35c09982823f1⟩),
  (⟨.str, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩, .strCons ⟨.char, 'F'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa⟩, .strCons ⟨.char, 'L'⟩ ⟨.str, mkF 0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9⟩),
  (⟨.str, mkF 0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9⟩, .strCons ⟨.char, 'A'⟩ ⟨.str, mkF 0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1⟩),
  (⟨.str, mkF 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩, .strCons ⟨.char, 'L'⟩ ⟨.str, mkF 0x73d60464d5bb6c21f252d1669bb6c392437999d8a9e2c8daba4d78718d0f7279⟩),
  (⟨.str, mkF 0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1⟩, .strCons ⟨.char, 'M'⟩ ⟨.str, mkF 0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da⟩),
  (⟨.str, mkF 0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36⟩, .strCons ⟨.char, 'A'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x5b99c690e9124338f91704cc89d273e470462ba12d8b436f5798387b1dacbe58⟩, .strCons ⟨.char, 'I'⟩ ⟨.str, mkF 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩),
  (⟨.str, mkF 0x63f54baca36ac31205e11d1bcd336891c40ae48b9a29b3683a7eb9f430fd4a4b⟩, .strCons ⟨.char, '='⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe⟩, .strCons ⟨.char, 'D'⟩ ⟨.str, mkF 0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36⟩),
  (⟨.str, mkF 0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600⟩, .strCons ⟨.char, 'X'⟩ ⟨.str, mkF 0⟩),
  (⟨.str, mkF 0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da⟩, .strCons ⟨.char, 'B'⟩ ⟨.str, mkF 0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe⟩),
  (⟨.str, mkF 0x73d60464d5bb6c21f252d1669bb6c392437999d8a9e2c8daba4d78718d0f7279⟩, .strCons ⟨.char, 'E'⟩ ⟨.str, mkF 0x1124e756c270500ff7dd307e51fd6ac22eecaab01bacf95ef21b20c1cb46388e⟩)
]

open LSpec in
def main := do
  let tSeq := test "Stores have the same size" (got.exprs.size == expected.size)
  lspecIO $ expected.fold (init := tSeq) fun tSeq ptr expectedExpr =>
    withOptionSome s!"{ptr} is found" (got.exprs.find? ptr) fun gotExpr =>
      tSeq ++ test s!"Expression for key {ptr} matches"
        (expectedExpr == gotExpr)

-- def got' := ⟦(f a)⟧.hash.1

-- def expected' : Std.RBMap ScalarPtr ScalarExpr compare := .ofList [
--   (⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩,
--     .sym ⟨.str, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

--   (⟨.cons, .ofNat 0x2fdd37cb19ebaca2fbce69de18c7369d42040034079af6c69a346f9a8a893028⟩, .cons
--     ⟨.sym, .ofNat 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩
--     ⟨.cons, .ofNat 0x6774a9faca6980bb8766e64b450c912c7387b40ee23c293a0f3bc3d6e1394554⟩),

--   (⟨.cons, .ofNat 0x6774a9faca6980bb8766e64b450c912c7387b40ee23c293a0f3bc3d6e1394554⟩, .cons
--     ⟨.sym, .ofNat 0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36⟩
--     ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

--   (⟨.sym, .ofNat 0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36⟩, .sym
--     ⟨.str,.ofNat 0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36⟩),

--   (⟨.sym, .ofNat 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩, .sym
--     ⟨.str,.ofNat 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩),

--   (⟨.str, .ofNat 0⟩, .strNil),

--   (⟨.str, .ofNat 0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36⟩, .strCons
--     'A' ⟨.str, .ofNat 0x0000000000000000000000000000000000000000000000000000000000000000⟩),

--   (⟨.str, .ofNat 0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc⟩, .strCons
--     'F' ⟨.str, .ofNat 0x0000000000000000000000000000000000000000000000000000000000000000⟩),

--   (⟨.str, .ofNat 0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570⟩, .strCons
--     'L' ⟨.str, .ofNat 0x0000000000000000000000000000000000000000000000000000000000000000⟩),

--   (⟨.str, .ofNat 0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09⟩, .strCons
--     'I' ⟨.str, .ofNat 0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570⟩),

--   (⟨.str, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩, .strCons
--     'N' ⟨.str, .ofNat 0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09⟩)

-- ]

-- open LSpec in
-- #lspec
--   let tSeq := test "Stores have the same size" (got'.exprs.size == expected'.size)
--   expected'.fold (init := tSeq) fun tSeq ptr expectedExpr =>
--     withOptionSome s!"{ptr} is found" (got'.exprs.find? ptr) fun gotExpr =>
--       tSeq ++ test s!"Expression for key {ptr} matches"
--         (expectedExpr == gotExpr)
