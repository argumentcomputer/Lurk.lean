import LSpec
import Lurk.Syntax.DSL
import Lurk.Syntax.Printing
import Lurk.Hashing.StoreDSL
import Lurk.Hashing.Hashing

open Lurk Hashing Syntax

def expression := ⟦
  (begin
    (lambda (x y) (+ x y))
    (cons 1 2)
    (strcons a b)
    (f)
    (g x y)
    (let (
        (n1 nil)
        (n2 (quote (nil)))
        (n3 (begin)))
      (current-env)))
⟧

open DSL in def expectedStore := [store| scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x506fcc2065b81603f7cb2ee5cb6f8f965a060585599cad71fdf489b49318650a)): Cons((cons, Scalar(0x473fb2207c277b2d682454f26c9acc67c51476d7e8c3c97dd79cc3c3410cb365)), (cons, Scalar(0x56384e51ef312c9c17e03f20187299b7ebed89469018c7feee7f969755d3b7c7))),
  (cons, Scalar(0x72c45f2dc94b8f4e9508f8375ac423fa6b75d2230498d79b4240c072c319d711)): Cons((sym, Scalar(0x68200f6adcca84aba50d43afe7d34b1d9424efadee7702f37734f460b833fd57)), (cons, Scalar(0x7395bf2464ad008016e56384226a6c7f568f5f16d30312277c2cb1b504848a6f))),
  (cons, Scalar(0x3ac4a3fe8bd13db2228cf10d427b5d5bc3e4e953459aa9f42d6013ee979a9d1f)): Cons((cons, Scalar(0x3a2818d13220fa5855a19c684ecd963dc9b60ce7eaf1cde66c76a3928801e025)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x18fabc72e3896162b1d0197ba526555a2a5a614f9a8b2f3fc2752c1d9e6cd81f)): Cons((sym, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)), (cons, Scalar(0x52c45eab223ac2602751babb2ddc680a1693c747a44d2e9a82e22543290299ba))),
  (cons, Scalar(0x3a2818d13220fa5855a19c684ecd963dc9b60ce7eaf1cde66c76a3928801e025)): Cons((sym, Scalar(0x3a0eacecf3e379c8c152fb390a8a4aa2ad40737411230fb7253378fb9c92eaff)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x40c57ef2a1994970505c6049c433a2d824c776ce9af1914a70cdc8d2c2f0e82a)): Cons((cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e)), (cons, Scalar(0x3f744ba4288ab7b559224494b1ca5a3913dcae40db4d647f0b297aad6dffca39))),
  (cons, Scalar(0x4ea6b11b5ac9a37f75f1f52a0d2a712021f0224a7228ad947a925b18aebcf533)): Cons((sym, Scalar(0x3b165850855659488b09987a470794b55365ad166a526926f332a74433a2316f)), (cons, Scalar(0x5018526d52eed2c3f03c17ecca6e1af855d24ab51a399ceb94270343bdd779fb))),
  (cons, Scalar(0x3f744ba4288ab7b559224494b1ca5a3913dcae40db4d647f0b297aad6dffca39)): Cons((cons, Scalar(0x5a54d8e7735c9d347792d1da1b76515f8990b8d3fe7b6bcef19d19ddc2ec5155)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x719bb5dd34249e3f33ed2b79b0039ad8f57ee8d0fb0e4e60909dbe97c59bd73f)): Cons((cons, Scalar(0x429233a25da778729e5aa8782ed17faa2b06bad309479385a0063c534b056f41)), (cons, Scalar(0x3ac4a3fe8bd13db2228cf10d427b5d5bc3e4e953459aa9f42d6013ee979a9d1f))),
  (cons, Scalar(0x429233a25da778729e5aa8782ed17faa2b06bad309479385a0063c534b056f41)): Cons((cons, Scalar(0x22d438c6123ab1192a90497cfbe47760da55a6f59e2e909ecfbcb2a4db7b23e7)), (cons, Scalar(0x26d50ddd548c1d521b6e06339cdad1fa4ea73911d525e4cc769d7a0fb2d742d4))),
  (cons, Scalar(0x3b36cedbf7a815e93bb8889b715edb2ad4baa2b5a03a3823640b118db5f81842)): Cons((sym, Scalar(0x1d49a865861970b584f8041dbb641e162dc3f330120cbd5791e1c5c6d90efc75)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x25d6df3726eb598945801bbdd3990ea0556e050fe56ebf1967c5cfb74e6d284c)): Cons((sym, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873))),
  (cons, Scalar(0x5a54d8e7735c9d347792d1da1b76515f8990b8d3fe7b6bcef19d19ddc2ec5155)): Cons((sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)), (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e))),
  (cons, Scalar(0x473fb2207c277b2d682454f26c9acc67c51476d7e8c3c97dd79cc3c3410cb365)): Cons((sym, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x42570206e353787d3b347f3f169a8a985214d6745648a715ecb6f48822d8ce6e)): Cons((nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x7395bf2464ad008016e56384226a6c7f568f5f16d30312277c2cb1b504848a6f)): Cons((sym, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)), (cons, Scalar(0x3b36cedbf7a815e93bb8889b715edb2ad4baa2b5a03a3823640b118db5f81842))),
  (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873)): Cons((sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x35926b7116f6700e7ea2f4d0efa12b5de9ef8bb3e79542a61336c7bfc3af5175)): Cons((cons, Scalar(0x53b245902ac0ced29c78e64a886299e241369f516f07fb44675ff73fdb789a98)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x635dd9b7cab5ef1fd3f937e70b3664b1a7957f5af24a7c263d04646bb8f59475)): Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)), (cons, Scalar(0x40c57ef2a1994970505c6049c433a2d824c776ce9af1914a70cdc8d2c2f0e82a))),
  (cons, Scalar(0x473be1b6243157f428ec9e32c90b99af0501141694b0d5b20b81fa74e7bb6a77)): Cons((sym, Scalar(0x5db350dc9ddc217713ab63a61315f1654ef2ae615f73e4f3a3734a0b739a1c5d)), (cons, Scalar(0x719bb5dd34249e3f33ed2b79b0039ad8f57ee8d0fb0e4e60909dbe97c59bd73f))),
  (cons, Scalar(0x53b245902ac0ced29c78e64a886299e241369f516f07fb44675ff73fdb789a98)): Cons((sym, Scalar(0x0cdd2254ef6a7ad8565292dfd57144ebbfc315de0f8ac8b862bf4c793b53a5f3)), (cons, Scalar(0x1af493f747728c413d4d1006260dc4b4eabed3b4cddf645d45ba34c8a7eca0f7))),
  (cons, Scalar(0x45a465436fc9f3206ad8e95c088d9eed9c2e354a9017a6ead9e01797a5d5519a)): Cons((cons, Scalar(0x18fabc72e3896162b1d0197ba526555a2a5a614f9a8b2f3fc2752c1d9e6cd81f)), (cons, Scalar(0x63dfb15e83022405c62980b4964ce7a879993e7211acdc26f26d4d35be5dddca))),
  (cons, Scalar(0x1d2a3a4ecf65a3bef6754c2982f0af71cc85f55c4967f0a67b228f16d6a672a9)): Cons((cons, Scalar(0x635dd9b7cab5ef1fd3f937e70b3664b1a7957f5af24a7c263d04646bb8f59475)), (cons, Scalar(0x45a465436fc9f3206ad8e95c088d9eed9c2e354a9017a6ead9e01797a5d5519a))),
  (cons, Scalar(0x41316e88f07b6630a4199b93a484e90224e78ef9d516e0fa0ff4221f26e64eb8)): Cons((cons, Scalar(0x473be1b6243157f428ec9e32c90b99af0501141694b0d5b20b81fa74e7bb6a77)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x52c45eab223ac2602751babb2ddc680a1693c747a44d2e9a82e22543290299ba)): Cons((num, 1), (cons, Scalar(0x341599585aa13261cf71e0c58de5dbe69a9784aeea2f1b467b141b8f7437afea))),
  (cons, Scalar(0x0bf2efd21744e1c8669a4e52b69f30ebf41a5d323c48cb4b458a6a4c89db33bb)): Cons((sym, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)), (cons, Scalar(0x1d2a3a4ecf65a3bef6754c2982f0af71cc85f55c4967f0a67b228f16d6a672a9))),
  (cons, Scalar(0x56384e51ef312c9c17e03f20187299b7ebed89469018c7feee7f969755d3b7c7)): Cons((cons, Scalar(0x4583c1886805b8d3c28fb34f49b92f7b3ec3cca681797c1c7773be6a48edd9d7)), (cons, Scalar(0x41316e88f07b6630a4199b93a484e90224e78ef9d516e0fa0ff4221f26e64eb8))),
  (cons, Scalar(0x63dfb15e83022405c62980b4964ce7a879993e7211acdc26f26d4d35be5dddca)): Cons((cons, Scalar(0x72c45f2dc94b8f4e9508f8375ac423fa6b75d2230498d79b4240c072c319d711)), (cons, Scalar(0x506fcc2065b81603f7cb2ee5cb6f8f965a060585599cad71fdf489b49318650a))),
  (cons, Scalar(0x298e601f2cdad2c7b88b6211d1d4f77486e1d92962ca3b541f404462cc0c74cd)): Cons((sym, Scalar(0x34d05a9c44f96749f077d239cc83ff5c0bc71f957a589dd08e434a3cda144221)), (cons, Scalar(0x0e97d9a7a58cf6556463df89a6fdd235460f3bc189ecce770cae02213c7cb6dd))),
  (cons, Scalar(0x26d50ddd548c1d521b6e06339cdad1fa4ea73911d525e4cc769d7a0fb2d742d4)): Cons((cons, Scalar(0x298e601f2cdad2c7b88b6211d1d4f77486e1d92962ca3b541f404462cc0c74cd)), (cons, Scalar(0x35926b7116f6700e7ea2f4d0efa12b5de9ef8bb3e79542a61336c7bfc3af5175))),
  (cons, Scalar(0x4583c1886805b8d3c28fb34f49b92f7b3ec3cca681797c1c7773be6a48edd9d7)): Cons((sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)), (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e))),
  (cons, Scalar(0x0e97d9a7a58cf6556463df89a6fdd235460f3bc189ecce770cae02213c7cb6dd)): Cons((cons, Scalar(0x4ea6b11b5ac9a37f75f1f52a0d2a712021f0224a7228ad947a925b18aebcf533)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x22d438c6123ab1192a90497cfbe47760da55a6f59e2e909ecfbcb2a4db7b23e7)): Cons((sym, Scalar(0x2d1724c3049eb92aaad3ecd8ff18382a62dace09ed0544501222439eee16cda6)), (cons, Scalar(0x42570206e353787d3b347f3f169a8a985214d6745648a715ecb6f48822d8ce6e))),
  (cons, Scalar(0x341599585aa13261cf71e0c58de5dbe69a9784aeea2f1b467b141b8f7437afea)): Cons((num, 2), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x1af493f747728c413d4d1006260dc4b4eabed3b4cddf645d45ba34c8a7eca0f7)): Cons((cons, Scalar(0x25d6df3726eb598945801bbdd3990ea0556e050fe56ebf1967c5cfb74e6d284c)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x5018526d52eed2c3f03c17ecca6e1af855d24ab51a399ceb94270343bdd779fb)): Cons((cons, Scalar(0x42570206e353787d3b347f3f169a8a985214d6745648a715ecb6f48822d8ce6e)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (sym, Scalar(0x34d05a9c44f96749f077d239cc83ff5c0bc71f957a589dd08e434a3cda144221)): Sym((str, Scalar(0x34d05a9c44f96749f077d239cc83ff5c0bc71f957a589dd08e434a3cda144221))),
  (sym, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)): Sym((str, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25))),
  (sym, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)): Sym((str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e))),
  (sym, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): Sym((str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
  (sym, Scalar(0x68200f6adcca84aba50d43afe7d34b1d9424efadee7702f37734f460b833fd57)): Sym((str, Scalar(0x68200f6adcca84aba50d43afe7d34b1d9424efadee7702f37734f460b833fd57))),
  (sym, Scalar(0x5db350dc9ddc217713ab63a61315f1654ef2ae615f73e4f3a3734a0b739a1c5d)): Sym((str, Scalar(0x5db350dc9ddc217713ab63a61315f1654ef2ae615f73e4f3a3734a0b739a1c5d))),
  (sym, Scalar(0x3b165850855659488b09987a470794b55365ad166a526926f332a74433a2316f)): Sym((str, Scalar(0x3b165850855659488b09987a470794b55365ad166a526926f332a74433a2316f))),
  (sym, Scalar(0x1d49a865861970b584f8041dbb641e162dc3f330120cbd5791e1c5c6d90efc75)): Sym((str, Scalar(0x1d49a865861970b584f8041dbb641e162dc3f330120cbd5791e1c5c6d90efc75))),
  (sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): Sym((str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88))),
  (sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): Sym((str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2))),
  (sym, Scalar(0x2d1724c3049eb92aaad3ecd8ff18382a62dace09ed0544501222439eee16cda6)): Sym((str, Scalar(0x2d1724c3049eb92aaad3ecd8ff18382a62dace09ed0544501222439eee16cda6))),
  (sym, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc)): Sym((str, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc))),
  (sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): Sym((str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc))),
  (sym, Scalar(0x0cdd2254ef6a7ad8565292dfd57144ebbfc315de0f8ac8b862bf4c793b53a5f3)): Sym((str, Scalar(0x0cdd2254ef6a7ad8565292dfd57144ebbfc315de0f8ac8b862bf4c793b53a5f3))),
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  (sym, Scalar(0x3a0eacecf3e379c8c152fb390a8a4aa2ad40737411230fb7253378fb9c92eaff)): Sym((str, Scalar(0x3a0eacecf3e379c8c152fb390a8a4aa2ad40737411230fb7253378fb9c92eaff))),
  (num, 1): Num(1),
  (num, 2): Num(2),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x1e09017b487fb356c2ac6a6c24a5de935c7fb3d8df6635c42c829c89e4fcd20d)): StrCons((char, '1'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x6cd16afd32983547a5a5b5c6c1ebd2c69c15da1f33f41d98d79b07b3a75d3313)): StrCons((char, '3'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x34d05a9c44f96749f077d239cc83ff5c0bc71f957a589dd08e434a3cda144221)): StrCons((char, 'N'), (str, Scalar(0x18762a1a36b97e60c29de4f1fedabd2ec913cc57ac7c1ad2a62a40fa60b88e43))),
  (str, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)): StrCons((char, 'B'), (str, Scalar(0x43a13c42764373f821535ad357d72b0535a62bf6d8bcc1374872ea2e894d3d50))),
  (str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e)): StrCons((char, 'C'), (str, Scalar(0x73b070801a151f5d7aedac8c66babb4ebef568b8b3c54eee50f2effea84cdfaf))),
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): StrCons((char, 'A'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x6e1dbad6ae837622bafb92e9dbc1f149fa1243f8a8d1b04ef702bd27df6e5f38)): StrCons((char, 'T'), (str, Scalar(0x54ec26ab6501db8818022311e787fb40d5e87d9016adc6bdf595880ccb171468))),
  (str, Scalar(0x2227d1c569a84491a1b80f0b80d7280c2da0f973a42da479f445d27b9ea80b39)): StrCons((char, 'E'), (str, Scalar(0x5fbbf7cebd2f799c9d40537e2c87c3049a1756729012151eeb11f84ea1914487))),
  (str, Scalar(0x0b56ad382634f8bd7910c39be6b7def4f958a18231cf042d2cd110a6179d743b)): StrCons((char, 'O'), (str, Scalar(0x270bba6f52b3b2bf60505cd551e6b50f2c952c2ddeeaf79c40e54bd82a680866))),
  (str, Scalar(0x18762a1a36b97e60c29de4f1fedabd2ec913cc57ac7c1ad2a62a40fa60b88e43)): StrCons((char, '2'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x43a13c42764373f821535ad357d72b0535a62bf6d8bcc1374872ea2e894d3d50)): StrCons((char, 'E'), (str, Scalar(0x09e7e1c69036f008f65a52e2fa97e580bc94fe5a5a8ebaeaebff92cfdd505cce))),
  (str, Scalar(0x68200f6adcca84aba50d43afe7d34b1d9424efadee7702f37734f460b833fd57)): StrCons((char, 'S'), (str, Scalar(0x6e1dbad6ae837622bafb92e9dbc1f149fa1243f8a8d1b04ef702bd27df6e5f38))),
  (str, Scalar(0x0f1813fe65f264e21e3ccf455b8279673f9c79e95228c5bbe6ca24079cd8d65a)): StrCons((char, 'T'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x5db350dc9ddc217713ab63a61315f1654ef2ae615f73e4f3a3734a0b739a1c5d)): StrCons((char, 'L'), (str, Scalar(0x00055374e841a84eee52318c885b7b77544a0626fd7b76d31cb6eb1d217a2d7e))),
  (str, Scalar(0x270bba6f52b3b2bf60505cd551e6b50f2c952c2ddeeaf79c40e54bd82a680866)): StrCons((char, 'T'), (str, Scalar(0x4b25e77c7077aae2a9047661389410e8f570338bf47570a19453d40ff24fcff8))),
  (str, Scalar(0x54ec26ab6501db8818022311e787fb40d5e87d9016adc6bdf595880ccb171468)): StrCons((char, 'R'), (str, Scalar(0x592261e4a6a31a525161c44006dc9a13f1e0b63ae07c21ffeb2f6dcb86a51f2e))),
  (str, Scalar(0x4074aab25ec2c5432d7f348b21c8aa8ea180e6bfbbd30ed2903261e9cadc9a6b)): StrCons((char, 'S'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x3b165850855659488b09987a470794b55365ad166a526926f332a74433a2316f)): StrCons((char, 'Q'), (str, Scalar(0x5c294ee38eda2488bff3c260764617fa1fcf7eddf29a0cfad97bf39d9c5827dd))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x1d49a865861970b584f8041dbb641e162dc3f330120cbd5791e1c5c6d90efc75)): StrCons((char, 'B'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x488fc1fe0451c36ce3088f3a3ce2871ca369b5e1ad423a1e0f7de6fd796b257c)): StrCons((char, 'N'), (str, Scalar(0x021206d0197f969eacbd820cf40e0dc495b3ebb28431907913e64f0e22a14b8e))),
  (str, Scalar(0x00055374e841a84eee52318c885b7b77544a0626fd7b76d31cb6eb1d217a2d7e)): StrCons((char, 'E'), (str, Scalar(0x0f1813fe65f264e21e3ccf455b8279673f9c79e95228c5bbe6ca24079cd8d65a))),
  (str, Scalar(0x1db9a044d1d84996117005cc61ea08694531baa2f8cc6878e844f0a0f8769f80)): StrCons((char, 'R'), (str, Scalar(0x0aece14fe00ea90a8ebe73d182127de38b88ed4ca82db9efe570070f5858d5f1))),
  (str, Scalar(0x5fbbf7cebd2f799c9d40537e2c87c3049a1756729012151eeb11f84ea1914487)): StrCons((char, 'N'), (str, Scalar(0x15be7c0e0421496ab63c058c21548390f670c13a63cf7e559b34e5d4575edac1))),
  (str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): StrCons((char, 'G'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x021206d0197f969eacbd820cf40e0dc495b3ebb28431907913e64f0e22a14b8e)): StrCons((char, 'T'), (str, Scalar(0x158cbeed17ce38f7fe4bd991190f09f3f04d7a90fc8012cb2528df4492c5bb9d))),
  (str, Scalar(0x158cbeed17ce38f7fe4bd991190f09f3f04d7a90fc8012cb2528df4492c5bb9d)): StrCons((char, '-'), (str, Scalar(0x2227d1c569a84491a1b80f0b80d7280c2da0f973a42da479f445d27b9ea80b39))),
  (str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): StrCons((char, 'Y'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2d1724c3049eb92aaad3ecd8ff18382a62dace09ed0544501222439eee16cda6)): StrCons((char, 'N'), (str, Scalar(0x1e09017b487fb356c2ac6a6c24a5de935c7fb3d8df6635c42c829c89e4fcd20d))),
  (str, Scalar(0x73b070801a151f5d7aedac8c66babb4ebef568b8b3c54eee50f2effea84cdfaf)): StrCons((char, 'O'), (str, Scalar(0x30bf0575b3a82eeab92a65acefb630cd01853be3b2183f400009ab3e0b735ac4))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)): StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  (str, Scalar(0x15be7c0e0421496ab63c058c21548390f670c13a63cf7e559b34e5d4575edac1)): StrCons((char, 'V'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x30bf0575b3a82eeab92a65acefb630cd01853be3b2183f400009ab3e0b735ac4)): StrCons((char, 'N'), (str, Scalar(0x4074aab25ec2c5432d7f348b21c8aa8ea180e6bfbbd30ed2903261e9cadc9a6b))),
  (str, Scalar(0x09e7e1c69036f008f65a52e2fa97e580bc94fe5a5a8ebaeaebff92cfdd505cce)): StrCons((char, 'G'), (str, Scalar(0x6e2ae924dc91b4b7434f3fe7ddec530b0dd932cdc2dd23021bb0a6870e3817cf))),
  (str, Scalar(0x6e2ae924dc91b4b7434f3fe7ddec530b0dd932cdc2dd23021bb0a6870e3817cf)): StrCons((char, 'I'), (str, Scalar(0x25d81388620245feeff75c2a98911696ac9dc886f31727856909672311caffe8))),
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)): StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  (str, Scalar(0x432194c501058fd688dde60320e9994d089956584f50c64654e062ab4d3a4dd6)): StrCons((char, 'E'), (str, Scalar(0x488fc1fe0451c36ce3088f3a3ce2871ca369b5e1ad423a1e0f7de6fd796b257c))),
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)): StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe))),
  (str, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc)): StrCons((char, 'F'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): StrCons((char, '+'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x16507e8d322113e024b96229c8cd6bab88ecd5df04afd04414fce2fbc9c9ebdc)): StrCons((char, 'U'), (str, Scalar(0x1db9a044d1d84996117005cc61ea08694531baa2f8cc6878e844f0a0f8769f80))),
  (str, Scalar(0x5c294ee38eda2488bff3c260764617fa1fcf7eddf29a0cfad97bf39d9c5827dd)): StrCons((char, 'U'), (str, Scalar(0x0b56ad382634f8bd7910c39be6b7def4f958a18231cf042d2cd110a6179d743b))),
  (str, Scalar(0x25d81388620245feeff75c2a98911696ac9dc886f31727856909672311caffe8)): StrCons((char, 'N'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x0aece14fe00ea90a8ebe73d182127de38b88ed4ca82db9efe570070f5858d5f1)): StrCons((char, 'R'), (str, Scalar(0x432194c501058fd688dde60320e9994d089956584f50c64654e062ab4d3a4dd6))),
  (str, Scalar(0x0cdd2254ef6a7ad8565292dfd57144ebbfc315de0f8ac8b862bf4c793b53a5f3)): StrCons((char, 'N'), (str, Scalar(0x6cd16afd32983547a5a5b5c6c1ebd2c69c15da1f33f41d98d79b07b3a75d3313))),
  (str, Scalar(0x4b25e77c7077aae2a9047661389410e8f570338bf47570a19453d40ff24fcff8)): StrCons((char, 'E'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)): StrCons((char, 'D'), (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
  (str, Scalar(0x3a0eacecf3e379c8c152fb390a8a4aa2ad40737411230fb7253378fb9c92eaff)): StrCons((char, 'C'), (str, Scalar(0x16507e8d322113e024b96229c8cd6bab88ecd5df04afd04414fce2fbc9c9ebdc))),
}]


def tuples : List (Expr × ScalarStore) := [
  (expression, expectedStore)
]

open LSpec in
def main := do
  lspecIO $ tuples.foldl (init := .done)
    fun tSeq (tuple : Expr × ScalarStore) => match tuple with
      | (expr, s) => tSeq ++ test s!"Stores {expr.pprint true false} correctly"
        (expr.hash.1 == s)

def qq := ⟦(begin
    (f)
    (g x y))⟧

open DSL in def ww := [store| scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x061e55f2f2a8ac9a10c33eede0b3f493fee49825a9afa64f4171414c96a96d24)): Cons((sym, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)), (cons, Scalar(0x0dd23356f37fcf5c34d96a2fdb8438c516c6eb9b3fac885499e3ee937aeb4e6f))),
  (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873))),
  (cons, Scalar(0x0470a7564e91ef774035edfa92b5b80aac3f6a616e4af3ce75388dbe3f817661)): Cons((cons, Scalar(0x4583c1886805b8d3c28fb34f49b92f7b3ec3cca681797c1c7773be6a48edd9d7)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x473fb2207c277b2d682454f26c9acc67c51476d7e8c3c97dd79cc3c3410cb365)): Cons((sym, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x0dd23356f37fcf5c34d96a2fdb8438c516c6eb9b3fac885499e3ee937aeb4e6f)): Cons((cons, Scalar(0x473fb2207c277b2d682454f26c9acc67c51476d7e8c3c97dd79cc3c3410cb365)), (cons, Scalar(0x0470a7564e91ef774035edfa92b5b80aac3f6a616e4af3ce75388dbe3f817661))),
  (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873)): Cons((sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x4583c1886805b8d3c28fb34f49b92f7b3ec3cca681797c1c7773be6a48edd9d7)): Cons((sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)), (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (sym, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)): Sym((str, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25))),
  (sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): Sym((str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88))),
  (sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): Sym((str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2))),
  (sym, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc)): Sym((str, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc))),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x6de9f052fdb0ea5a4faa50b897d43659d7751c556e6aecac2bfff221175abd25)): StrCons((char, 'B'), (str, Scalar(0x43a13c42764373f821535ad357d72b0535a62bf6d8bcc1374872ea2e894d3d50))),
  (str, Scalar(0x43a13c42764373f821535ad357d72b0535a62bf6d8bcc1374872ea2e894d3d50)): StrCons((char, 'E'), (str, Scalar(0x09e7e1c69036f008f65a52e2fa97e580bc94fe5a5a8ebaeaebff92cfdd505cce))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): StrCons((char, 'G'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): StrCons((char, 'Y'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x09e7e1c69036f008f65a52e2fa97e580bc94fe5a5a8ebaeaebff92cfdd505cce)): StrCons((char, 'G'), (str, Scalar(0x6e2ae924dc91b4b7434f3fe7ddec530b0dd932cdc2dd23021bb0a6870e3817cf))),
  (str, Scalar(0x6e2ae924dc91b4b7434f3fe7ddec530b0dd932cdc2dd23021bb0a6870e3817cf)): StrCons((char, 'I'), (str, Scalar(0x25d81388620245feeff75c2a98911696ac9dc886f31727856909672311caffe8))),
  (str, Scalar(0x3423b95b8f4e1261de40b112021cb26cb30f7afdcde861d0d5bd9610472520dc)): StrCons((char, 'F'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x25d81388620245feeff75c2a98911696ac9dc886f31727856909672311caffe8)): StrCons((char, 'N'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
}]

#eval qq.hash.1

#lspec LSpec.test "" (qq.hash.1 == ww)

def qqq := ⟦(g x y)⟧

open DSL in def www := [store| scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873))),
  (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873)): Cons((sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x4583c1886805b8d3c28fb34f49b92f7b3ec3cca681797c1c7773be6a48edd9d7)): Cons((sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)), (cons, Scalar(0x49bcf206355dc708cf668aefb2fd901fa41386e8a9de94d2c835ec14675cc14e))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): Sym((str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88))),
  (sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): Sym((str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2))),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): StrCons((char, 'G'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): StrCons((char, 'Y'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
}]

open DSL in def z := [store| scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x1657db08b6e95f4da1960249f21ea86793cc24406ccacc3683e2e1aab33e6c1b)): Cons((cons, Scalar(0x1f585593e270027d7dd8c48da8688528fbfd4be4ce4dacecbf152e4f8b2da1d3)), (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873))),
  (cons, Scalar(0x1f585593e270027d7dd8c48da8688528fbfd4be4ce4dacecbf152e4f8b2da1d3)): Cons((sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)), (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  (cons, Scalar(0x22cf247a887e1cfdbcb3561c9ad3cd945a67e1d4d892b1def964145ed4052873)): Cons((sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (sym, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): Sym((str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2))),
  (sym, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): Sym((str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (str, Scalar(0)): StrNil,
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x142258c35f1541c1665f498e9f0771f6e4549bb53f9b36ab1c296bdd8a7b2ea2)): StrCons((char, 'Y'), (str, Scalar(0))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x4772fdc08a782360ff98c28b1a9c2579200af0d783eacdc4deed5476e5ba1f88)): StrCons((char, 'G'), (str, Scalar(0))),
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0)))
}]

#eval qqq.hash.1

#lspec LSpec.test "" (qqq.hash.1 == www)