import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.StoreDSL
import Lurk.Hashing.Encoding

open Lurk

open Syntax.DSL in def ast := ⟦
  (begin
    nil
    t
    current-env
    ()
    (nil)
    (t)
    (current-env)
    (nil t)
    (lambda (x y) (+ x y))
    (cons 1 2)
    (strcons a b)
    (f)
    (g x y)
    (let (
        (n1 nil)
        (n2 (quote (nil)))
        (n3 (begin)))
      (current-env))
    (quote nil)
    (quote 1)
    (quote (1 2 3))
    ((+ 1 2) (f x) . (cons 4 2)))
⟧

open Hashing.DSL in def expectedStore := [store| scalar_store: {
  (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47)): Sym((strCons, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x0a267220208055d3940e06deae8d333219f640614e23d354d054f0f748aa0435)): Cons((cons, Scalar(0x51f6b294fa3a5385d2d69a445b04541d927bca6a55ee855afaa843e52e8b89b0)), (cons, Scalar(0x2bc27485e60d1b655ec3076b8c9529c31057d4c4314149ed14f495653b00f085))),
  (cons, Scalar(0x0b543d85c70c697f8991b8e6657b16e8a85bd42b5c57e1d82970e4c536e87dfe)): Cons((sym, Scalar(0x593d698d6366dadfbfdc638cc7d93a7234204b3a4d4988e617fea11ad1d6fb75)), (cons, Scalar(0x62ac242da11d8e3a290ddfe2fe37fafdb6826ddfe41cf7e4eb39b7d7deab1e89))),
  (cons, Scalar(0x0d8c5fa309053f2fc641ffb372ca484ba9ac02fa2f536c727a3a83becda87fb8)): Cons((num, 2), (cons, Scalar(0x41086af540bf1e91e75a2c378a94360acccc2bfbc4f00cd7f98a97f8cd718864))),
  (cons, Scalar(0x0e1f63f8a43a3e7776dd6431dcd7a3ac0b299246ef7c5d640fd60514e028364c)): Cons((sym, Scalar(0x19ec9dcc4f273d87d50f490c07138c4e253eaf9cbe0337e18d6f8c2bcdbc9584)), (cons, Scalar(0x3139f05bc10ae0d9ef4301430eb597180563e03e3c15dc74544fe7351e330865))),
  (cons, Scalar(0x0eed7941033e59b578c1adf00c732fd1a8058eacc78aceab878e6409159231dc)): Cons((sym, Scalar(0x3a619e372b651520d8cc250f3000d4f47e55f1561a6152f4ae594ee2a7e3445c)), (cons, Scalar(0x1ec832f9a2bb20e9522d4cf8369dfdc673c661404e34c7b0ee36ce3774bbb40b))),
  (cons, Scalar(0x0eefee456232f8aecdc95c5826cb27515275910921ad29efcf84a6da5f04089a)): Cons((num, 1), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x0fe5c07686c3d079f549ee8451467d71e247e31ec92cc294084910d8733272bb)): Cons((cons, Scalar(0x495ac2403db03b6e95e53f6f96e37a9a45017fd4fd73478e8b4896d89771c3aa)), (cons, Scalar(0x4d542c5b5436ebd1e70152f29f580bb5613bc5d250f6718577effa28757efaec))),
  (cons, Scalar(0x139aef070ff1b7bf3f35c7feea712ac7dc8396ed1d83d0902f39376bbef68d97)): Cons((sym, Scalar(0x48faae48240f370b917dc62f459c34c849038fda77b73dd551a4e227027d7ecf)), (cons, Scalar(0x6369944069a79d424ecc790459638e066fafdbe20f8b7d2b156a21f9c68e5656))),
  (cons, Scalar(0x17390a24b316a6d84dac72c21c0afe1d85d3bf94dacef2ed72af4a4c26cc8a3b)): Cons((nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47)), (cons, Scalar(0x555c8a9eed72942b6cfaa75986bbca5a49e89d54c345b6cf9b52b2cc9d192af5))),
  (cons, Scalar(0x17f4f1d01060ed2c6f18242ca5f13650fdca1506d918c0383e99080febd39ba0)): Cons((sym, Scalar(0x5507d3b73af3ee2a59f4d731cf93a367d0472f470bdc037eb1e15180ef82e65c)), (cons, Scalar(0x62ac242da11d8e3a290ddfe2fe37fafdb6826ddfe41cf7e4eb39b7d7deab1e89))),
  (cons, Scalar(0x18d8aeba056ed65446a18cff698a6214f346fc6531af85d97dde84eefd7539f2)): Cons((sym, Scalar(0x27aa445d491012b4a2c05bcb8452e3631825c690badbeb10807f22d3cb97edae)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x1b06c7df067c7f25a59399e76dd0008a8660089e41e3fd613a1bc2f4ed277aa9)): Cons((sym, Scalar(0x681fa69428658ed53c9235f9e70bcc9c24bf44b0b1b0b20b428b2efe5c28af50)), (cons, Scalar(0x4d51059747ed3aba7c8a6c71ae9b638081850c5ce8b86afd66c902486dd0c5f5))),
  (cons, Scalar(0x1cc29ce292e5cfefa9acd8c4aaccb7a549136174a2f749660617e163415f2673)): Cons((cons, Scalar(0x3b4a20da6468daba0e33b30d69b5bafc3f67927751c0fa218eb048f521d76f3e)), (cons, Scalar(0x4fb491419665f3865c5e3c3158da2c727f5e5220f9de0fac225debaffc4ba6ff))),
  (cons, Scalar(0x1cf790cc39fc38ecd63ff0adb7046871f2562505615572458874d177fba7ea0b)): Cons((cons, Scalar(0x51f6b294fa3a5385d2d69a445b04541d927bca6a55ee855afaa843e52e8b89b0)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x1ec832f9a2bb20e9522d4cf8369dfdc673c661404e34c7b0ee36ce3774bbb40b)): Cons((cons, Scalar(0x62ac242da11d8e3a290ddfe2fe37fafdb6826ddfe41cf7e4eb39b7d7deab1e89)), (cons, Scalar(0x2714c08b245eee61289b91139aad99c328d3e38878058afc477b4099b7a667f8))),
  (cons, Scalar(0x2700f9461aa5c97d317166e0252a42cff605481fe22505c1b1ad26efa27cab4e)): Cons((nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47)), (cons, Scalar(0x37f540a39b180e6457c0cea732eefab42b15b5ea6958741a33c3b61119354dd7))),
  (cons, Scalar(0x2714c08b245eee61289b91139aad99c328d3e38878058afc477b4099b7a667f8)): Cons((cons, Scalar(0x17f4f1d01060ed2c6f18242ca5f13650fdca1506d918c0383e99080febd39ba0)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x28609c2e0cd89c3681b20e9f13b1ccdbf297d2c137ee43404127cbf41657d0ef)): Cons((sym, Scalar(0x19ec9dcc4f273d87d50f490c07138c4e253eaf9cbe0337e18d6f8c2bcdbc9584)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x2867087d533318f8d60e4b5d1dc9312cf0b882c1d465aeb2b844e8de91494a59)): Cons((sym, Scalar(0x726909636803100683eee9f9dbdf86f9f44dc6721d69dc0f9af9378b920103f2)), (cons, Scalar(0x584924e0fe4eaf82e998ee99fbc4df429232fa42883a5990b6f032615a925d29))),
  (cons, Scalar(0x29a5253b2d0ab4e4fc4453433cda1c935dc11e323579d37a247679ac886bf966)): Cons((num, 1), (cons, Scalar(0x0d8c5fa309053f2fc641ffb372ca484ba9ac02fa2f536c727a3a83becda87fb8))),
  (cons, Scalar(0x2bc27485e60d1b655ec3076b8c9529c31057d4c4314149ed14f495653b00f085)): Cons((cons, Scalar(0x37f540a39b180e6457c0cea732eefab42b15b5ea6958741a33c3b61119354dd7)), (cons, Scalar(0x436fe7dc5e6ce93b93c122ffa9d1ca3f7d35502f5f688f4797f54b05fc43705a))),
  (cons, Scalar(0x311adcc768441536cafd5c77ada4c2848481ac7db99ded7bd6d0f4e6bb792903)): Cons((cons, Scalar(0x0eed7941033e59b578c1adf00c732fd1a8058eacc78aceab878e6409159231dc)), (cons, Scalar(0x46eae5607d015178ea0bf339ce9d7d223145dad57eabcd5e6b668d4faa70181b))),
  (cons, Scalar(0x3139f05bc10ae0d9ef4301430eb597180563e03e3c15dc74544fe7351e330865)): Cons((sym, Scalar(0x3b6a744c015bc89e58c736ab0af06a0efe6990f29f0f88a3bb9242e7c6168cd2)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x3589abd32a5219cec60e4df9fbf61027a247e87c68bb2e2463d39603c0b8747b)): Cons((sym, Scalar(0x2e57310fb1d91519d0d058ad96b9f2b949754da1d5920f7d55bc7fe09b5fc53b)), (cons, Scalar(0x51f6b294fa3a5385d2d69a445b04541d927bca6a55ee855afaa843e52e8b89b0))),
  (cons, Scalar(0x36a34bdfe883be75e6b5359e03e46f98b40dc3c32b36f903eca623e781c7e489)): Cons((cons, Scalar(0x5635a08b34a9baee7e9ddcf6c81249221a5aa8af15d41ec03499635fc9f06b8d)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x37f540a39b180e6457c0cea732eefab42b15b5ea6958741a33c3b61119354dd7)): Cons((sym, Scalar(0x4ab487412a1297a8ef131d1e472c7b6061b8fc9029a2017ca977096b1d069e62)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x3951b1f2f18329accfe73c2ee855ae5832ab6bfb78a2028a4d6a43253a9f0a42)): Cons((sym, Scalar(0x4fef4cbca131563503f2eb43754515e62d0151fe7224f7f30b1d0421644705a7)), (cons, Scalar(0x711b24e5f88b6ae0b8ea4e0a3e9098e274fce581b6bfef1f0dd3e56bf83a92ef))),
  (cons, Scalar(0x3b4a20da6468daba0e33b30d69b5bafc3f67927751c0fa218eb048f521d76f3e)): Cons((sym, Scalar(0x49ff152b53db6f73a6119f6f7ac1593d08c905ec13472e22ab498714e813b7a3)), (cons, Scalar(0x40b9f507ebb30420bc5aef5da20a8a5b748d86fada4a37af4882604f49ee678f))),
  (cons, Scalar(0x3f3d54fae579d1b9b239ce878be03a5ed57936fef55dc446483e76959dca7c7b)): Cons((cons, Scalar(0x3589abd32a5219cec60e4df9fbf61027a247e87c68bb2e2463d39603c0b8747b)), (cons, Scalar(0x611920d3ac40901bbb1b75ea7559ef689907bf0144689852d83b8924cd753901))),
  (cons, Scalar(0x40b9f507ebb30420bc5aef5da20a8a5b748d86fada4a37af4882604f49ee678f)): Cons((sym, Scalar(0x71a4b5465b1f3367280f576544cc9c3b952270928f8091fd21c0935e7e1c020b)), (cons, Scalar(0x18d8aeba056ed65446a18cff698a6214f346fc6531af85d97dde84eefd7539f2))),
  (cons, Scalar(0x41086af540bf1e91e75a2c378a94360acccc2bfbc4f00cd7f98a97f8cd718864)): Cons((num, 3), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x42a5c426137a161811abed04e229a0c1f08836e3a08e0682d894b48efdca8d98)): Cons((cons, Scalar(0x4b61410efbff4ab920f01ab49c7fc39860bcbf697aa8a94a2853b1784f741edb)), (cons, Scalar(0x36a34bdfe883be75e6b5359e03e46f98b40dc3c32b36f903eca623e781c7e489))),
  (cons, Scalar(0x436fe7dc5e6ce93b93c122ffa9d1ca3f7d35502f5f688f4797f54b05fc43705a)): Cons((cons, Scalar(0x4e1ea86b68832c24fdd9cf580aaaad9b511f0e81c40230666bfc0964b6ee18e2)), (cons, Scalar(0x4b450d05c43afbfe9acaf0f1fcce7f2de99fc7f72f1ef42b1d3a762f12c4cc53))),
  (cons, Scalar(0x46eae5607d015178ea0bf339ce9d7d223145dad57eabcd5e6b668d4faa70181b)): Cons((cons, Scalar(0x2867087d533318f8d60e4b5d1dc9312cf0b882c1d465aeb2b844e8de91494a59)), (cons, Scalar(0x1cc29ce292e5cfefa9acd8c4aaccb7a549136174a2f749660617e163415f2673))),
  (cons, Scalar(0x477ac9a5c943503056d7c7817b1daa5ffbb32b242b25a013958f7e3de4b3cc83)): Cons((cons, Scalar(0x4e1ea86b68832c24fdd9cf580aaaad9b511f0e81c40230666bfc0964b6ee18e2)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x48e94c46d0f388f1c04e6941121d1fe3445a9fc77d0e33c159638d7ffb4ac60f)): Cons((num, 4), (cons, Scalar(0x696b1e142d1fee60d993eb9c7eedfba797a674d9a0b9d43ce31f1f4bc3467efc))),
  (cons, Scalar(0x495ac2403db03b6e95e53f6f96e37a9a45017fd4fd73478e8b4896d89771c3aa)): Cons((sym, Scalar(0x677decaff967d5b61e64476090ebdd98aec61046c259c9abe8194fd8e9c5e8a4)), (cons, Scalar(0x6f44af3e1318e12e44943f145994c68e407bcc07e40e5de020addc7cef89a933))),
  (cons, Scalar(0x4a8f6534db1ca8498c0cb24bfac8add4915ca8a02d1e0f04475fe985e311b838)): Cons((sym, Scalar(0x173dd3902e9eb25234ffae8d489509077bad20b20b72fe372209dc14c9a3b537)), (cons, Scalar(0x17390a24b316a6d84dac72c21c0afe1d85d3bf94dacef2ed72af4a4c26cc8a3b))),
  (cons, Scalar(0x4b450d05c43afbfe9acaf0f1fcce7f2de99fc7f72f1ef42b1d3a762f12c4cc53)): Cons((cons, Scalar(0x2700f9461aa5c97d317166e0252a42cff605481fe22505c1b1ad26efa27cab4e)), (cons, Scalar(0x311adcc768441536cafd5c77ada4c2848481ac7db99ded7bd6d0f4e6bb792903))),
  (cons, Scalar(0x4b61410efbff4ab920f01ab49c7fc39860bcbf697aa8a94a2853b1784f741edb)): Cons((sym, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395)), (cons, Scalar(0x6f4b8aed5007b795f14404f574ca0cf72268ea4ef51b061fd5a373ca08f401ce))),
  (cons, Scalar(0x4d51059747ed3aba7c8a6c71ae9b638081850c5ce8b86afd66c902486dd0c5f5)): Cons((nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47)), (cons, Scalar(0x0a267220208055d3940e06deae8d333219f640614e23d354d054f0f748aa0435))),
  (cons, Scalar(0x4d542c5b5436ebd1e70152f29f580bb5613bc5d250f6718577effa28757efaec)): Cons((cons, Scalar(0x6d9ecc239486f5bc0914d5b1226844742132afd8e87b0e64e315c3e934be7727)), (cons, Scalar(0x52fc983ad9b81e7d1ed689fe38a2acccc7f2f6b2443de5d650e61bd9538d7509))),
  (cons, Scalar(0x4e1ea86b68832c24fdd9cf580aaaad9b511f0e81c40230666bfc0964b6ee18e2)): Cons((sym, Scalar(0x681fa69428658ed53c9235f9e70bcc9c24bf44b0b1b0b20b428b2efe5c28af50)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x4fb491419665f3865c5e3c3158da2c727f5e5220f9de0fac225debaffc4ba6ff)): Cons((cons, Scalar(0x28609c2e0cd89c3681b20e9f13b1ccdbf297d2c137ee43404127cbf41657d0ef)), (cons, Scalar(0x6ef22812d5db630d6f756dd1f55017f7e8487aff23d1fedb52b16d738490f547))),
  (cons, Scalar(0x51f6b294fa3a5385d2d69a445b04541d927bca6a55ee855afaa843e52e8b89b0)): Cons((nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x52fc983ad9b81e7d1ed689fe38a2acccc7f2f6b2443de5d650e61bd9538d7509)): Cons((cons, Scalar(0x6fc4c0c0ef16872327b6f8d74c43f15c00d5e080488039dad640e0f30ba17e7a)), (cons, Scalar(0x42a5c426137a161811abed04e229a0c1f08836e3a08e0682d894b48efdca8d98))),
  (cons, Scalar(0x555c8a9eed72942b6cfaa75986bbca5a49e89d54c345b6cf9b52b2cc9d192af5)): Cons((sym, Scalar(0x4ab487412a1297a8ef131d1e472c7b6061b8fc9029a2017ca977096b1d069e62)), (cons, Scalar(0x1b06c7df067c7f25a59399e76dd0008a8660089e41e3fd613a1bc2f4ed277aa9))),
  (cons, Scalar(0x5635a08b34a9baee7e9ddcf6c81249221a5aa8af15d41ec03499635fc9f06b8d)): Cons((cons, Scalar(0x5c3f51e1f048be9aa691d14dd58a3a3d1f22f68604267fabfc6603974ab9fb4e)), (cons, Scalar(0x6adb48e408de2a6c782c662520366b579dcafbee647c5c2b515da4d5ec9a7e84))),
  (cons, Scalar(0x584924e0fe4eaf82e998ee99fbc4df429232fa42883a5990b6f032615a925d29)): Cons((num, 1), (cons, Scalar(0x696b1e142d1fee60d993eb9c7eedfba797a674d9a0b9d43ce31f1f4bc3467efc))),
  (cons, Scalar(0x5c262625bedec7a97c732a987997f8a591fcaa3e8f5226eb49858ca538668483)): Cons((sym, Scalar(0x173dd3902e9eb25234ffae8d489509077bad20b20b72fe372209dc14c9a3b537)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x5c3f51e1f048be9aa691d14dd58a3a3d1f22f68604267fabfc6603974ab9fb4e)): Cons((sym, Scalar(0x5507d3b73af3ee2a59f4d731cf93a367d0472f470bdc037eb1e15180ef82e65c)), (cons, Scalar(0x584924e0fe4eaf82e998ee99fbc4df429232fa42883a5990b6f032615a925d29))),
  (cons, Scalar(0x6030cd4384d0ff17583bf41caf54f6c7fe8ca13e4f0f1718251b459a06335270)): Cons((sym, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395)), (cons, Scalar(0x1cf790cc39fc38ecd63ff0adb7046871f2562505615572458874d177fba7ea0b))),
  (cons, Scalar(0x611920d3ac40901bbb1b75ea7559ef689907bf0144689852d83b8924cd753901)): Cons((cons, Scalar(0x139aef070ff1b7bf3f35c7feea712ac7dc8396ed1d83d0902f39376bbef68d97)), (cons, Scalar(0x7108517f26a7fbdef9f88c0eaf25efea72282ec8b613bd94d523fdeb0389f10f))),
  (cons, Scalar(0x6166debc5898f5dbf677649bdaf85d287d16310ee02ca1a022962a3f6360d0b5)): Cons((sym, Scalar(0x726909636803100683eee9f9dbdf86f9f44dc6721d69dc0f9af9378b920103f2)), (cons, Scalar(0x48e94c46d0f388f1c04e6941121d1fe3445a9fc77d0e33c159638d7ffb4ac60f))),
  (cons, Scalar(0x62ac242da11d8e3a290ddfe2fe37fafdb6826ddfe41cf7e4eb39b7d7deab1e89)): Cons((sym, Scalar(0x3b6a744c015bc89e58c736ab0af06a0efe6990f29f0f88a3bb9242e7c6168cd2)), (cons, Scalar(0x6cf32b7820af05d44ee12b30d8adf220076c6cd36313d425753fb36ed69be869))),
  (cons, Scalar(0x6369944069a79d424ecc790459638e066fafdbe20f8b7d2b156a21f9c68e5656)): Cons((cons, Scalar(0x6030cd4384d0ff17583bf41caf54f6c7fe8ca13e4f0f1718251b459a06335270)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x696b1e142d1fee60d993eb9c7eedfba797a674d9a0b9d43ce31f1f4bc3467efc)): Cons((num, 2), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x6adb48e408de2a6c782c662520366b579dcafbee647c5c2b515da4d5ec9a7e84)): Cons((cons, Scalar(0x0e1f63f8a43a3e7776dd6431dcd7a3ac0b299246ef7c5d640fd60514e028364c)), (cons, Scalar(0x6166debc5898f5dbf677649bdaf85d287d16310ee02ca1a022962a3f6360d0b5))),
  (cons, Scalar(0x6cf32b7820af05d44ee12b30d8adf220076c6cd36313d425753fb36ed69be869)): Cons((sym, Scalar(0x4f4b79b17dd45ffd95e2d68e427ca5bf3c3a6cd2abf91a2e3ae1c83644e2f333)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x6d9ecc239486f5bc0914d5b1226844742132afd8e87b0e64e315c3e934be7727)): Cons((sym, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395)), (cons, Scalar(0x51f6b294fa3a5385d2d69a445b04541d927bca6a55ee855afaa843e52e8b89b0))),
  (cons, Scalar(0x6ef22812d5db630d6f756dd1f55017f7e8487aff23d1fedb52b16d738490f547)): Cons((cons, Scalar(0x0b543d85c70c697f8991b8e6657b16e8a85bd42b5c57e1d82970e4c536e87dfe)), (cons, Scalar(0x0fe5c07686c3d079f549ee8451467d71e247e31ec92cc294084910d8733272bb))),
  (cons, Scalar(0x6f44af3e1318e12e44943f145994c68e407bcc07e40e5de020addc7cef89a933)): Cons((cons, Scalar(0x3f3d54fae579d1b9b239ce878be03a5ed57936fef55dc446483e76959dca7c7b)), (cons, Scalar(0x477ac9a5c943503056d7c7817b1daa5ffbb32b242b25a013958f7e3de4b3cc83))),
  (cons, Scalar(0x6f4b8aed5007b795f14404f574ca0cf72268ea4ef51b061fd5a373ca08f401ce)): Cons((cons, Scalar(0x29a5253b2d0ab4e4fc4453433cda1c935dc11e323579d37a247679ac886bf966)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x6fc4c0c0ef16872327b6f8d74c43f15c00d5e080488039dad640e0f30ba17e7a)): Cons((sym, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395)), (cons, Scalar(0x0eefee456232f8aecdc95c5826cb27515275910921ad29efcf84a6da5f04089a))),
  (cons, Scalar(0x7108517f26a7fbdef9f88c0eaf25efea72282ec8b613bd94d523fdeb0389f10f)): Cons((cons, Scalar(0x3951b1f2f18329accfe73c2ee855ae5832ab6bfb78a2028a4d6a43253a9f0a42)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (cons, Scalar(0x711b24e5f88b6ae0b8ea4e0a3e9098e274fce581b6bfef1f0dd3e56bf83a92ef)): Cons((cons, Scalar(0x5c262625bedec7a97c732a987997f8a591fcaa3e8f5226eb49858ca538668483)), (nil, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47))),
  (sym, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395)): Sym((strCons, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395))),
  (sym, Scalar(0x173dd3902e9eb25234ffae8d489509077bad20b20b72fe372209dc14c9a3b537)): Sym((strCons, Scalar(0x173dd3902e9eb25234ffae8d489509077bad20b20b72fe372209dc14c9a3b537))),
  (sym, Scalar(0x19ec9dcc4f273d87d50f490c07138c4e253eaf9cbe0337e18d6f8c2bcdbc9584)): Sym((strCons, Scalar(0x19ec9dcc4f273d87d50f490c07138c4e253eaf9cbe0337e18d6f8c2bcdbc9584))),
  (sym, Scalar(0x27aa445d491012b4a2c05bcb8452e3631825c690badbeb10807f22d3cb97edae)): Sym((strCons, Scalar(0x27aa445d491012b4a2c05bcb8452e3631825c690badbeb10807f22d3cb97edae))),
  (sym, Scalar(0x2e57310fb1d91519d0d058ad96b9f2b949754da1d5920f7d55bc7fe09b5fc53b)): Sym((strCons, Scalar(0x2e57310fb1d91519d0d058ad96b9f2b949754da1d5920f7d55bc7fe09b5fc53b))),
  (sym, Scalar(0x3a619e372b651520d8cc250f3000d4f47e55f1561a6152f4ae594ee2a7e3445c)): Sym((strCons, Scalar(0x3a619e372b651520d8cc250f3000d4f47e55f1561a6152f4ae594ee2a7e3445c))),
  (sym, Scalar(0x3b6a744c015bc89e58c736ab0af06a0efe6990f29f0f88a3bb9242e7c6168cd2)): Sym((strCons, Scalar(0x3b6a744c015bc89e58c736ab0af06a0efe6990f29f0f88a3bb9242e7c6168cd2))),
  (sym, Scalar(0x48faae48240f370b917dc62f459c34c849038fda77b73dd551a4e227027d7ecf)): Sym((strCons, Scalar(0x48faae48240f370b917dc62f459c34c849038fda77b73dd551a4e227027d7ecf))),
  (sym, Scalar(0x49ff152b53db6f73a6119f6f7ac1593d08c905ec13472e22ab498714e813b7a3)): Sym((strCons, Scalar(0x49ff152b53db6f73a6119f6f7ac1593d08c905ec13472e22ab498714e813b7a3))),
  (sym, Scalar(0x4ab487412a1297a8ef131d1e472c7b6061b8fc9029a2017ca977096b1d069e62)): Sym((strCons, Scalar(0x4ab487412a1297a8ef131d1e472c7b6061b8fc9029a2017ca977096b1d069e62))),
  (sym, Scalar(0x4f4b79b17dd45ffd95e2d68e427ca5bf3c3a6cd2abf91a2e3ae1c83644e2f333)): Sym((strCons, Scalar(0x4f4b79b17dd45ffd95e2d68e427ca5bf3c3a6cd2abf91a2e3ae1c83644e2f333))),
  (sym, Scalar(0x4fef4cbca131563503f2eb43754515e62d0151fe7224f7f30b1d0421644705a7)): Sym((strCons, Scalar(0x4fef4cbca131563503f2eb43754515e62d0151fe7224f7f30b1d0421644705a7))),
  (sym, Scalar(0x5507d3b73af3ee2a59f4d731cf93a367d0472f470bdc037eb1e15180ef82e65c)): Sym((strCons, Scalar(0x5507d3b73af3ee2a59f4d731cf93a367d0472f470bdc037eb1e15180ef82e65c))),
  (sym, Scalar(0x593d698d6366dadfbfdc638cc7d93a7234204b3a4d4988e617fea11ad1d6fb75)): Sym((strCons, Scalar(0x593d698d6366dadfbfdc638cc7d93a7234204b3a4d4988e617fea11ad1d6fb75))),
  (sym, Scalar(0x677decaff967d5b61e64476090ebdd98aec61046c259c9abe8194fd8e9c5e8a4)): Sym((strCons, Scalar(0x677decaff967d5b61e64476090ebdd98aec61046c259c9abe8194fd8e9c5e8a4))),
  (sym, Scalar(0x681fa69428658ed53c9235f9e70bcc9c24bf44b0b1b0b20b428b2efe5c28af50)): Sym((strCons, Scalar(0x681fa69428658ed53c9235f9e70bcc9c24bf44b0b1b0b20b428b2efe5c28af50))),
  (sym, Scalar(0x71a4b5465b1f3367280f576544cc9c3b952270928f8091fd21c0935e7e1c020b)): Sym((strCons, Scalar(0x71a4b5465b1f3367280f576544cc9c3b952270928f8091fd21c0935e7e1c020b))),
  (sym, Scalar(0x726909636803100683eee9f9dbdf86f9f44dc6721d69dc0f9af9378b920103f2)): Sym((strCons, Scalar(0x726909636803100683eee9f9dbdf86f9f44dc6721d69dc0f9af9378b920103f2))),
  (strCons, Scalar(0x07c726be868d20b78dfa419438f700d71059892b0573b2a0636ce2372797b395)): StrCons((char, 'Q'), (strCons, Scalar(0x0f6abc479d6e869986be11bdc13a78a89c1ec71f146b2e25ca8a03a1dc0ee1b1))),
  (strCons, Scalar(0x0861e4d377a82a1b35d785dad58d581d363f83f57e7820757b0b37f5a0b558b2)): StrCons((char, 'E'), (strCons, Scalar(0x25cab0a364aad36374f6638243103dc13c4480adfb9ac025ba8bed3b2d41fa9e))),
  (strCons, Scalar(0x0a4326c04603b142850d53c90712915bdbc93000be6c3e4e37bd2b5255b8566e)): StrCons((char, 'S'), (strNil, Scalar(0))),
  (strCons, Scalar(0x0f6abc479d6e869986be11bdc13a78a89c1ec71f146b2e25ca8a03a1dc0ee1b1)): StrCons((char, 'U'), (strCons, Scalar(0x445f44de0c764d973a7ef6c3361439cc156b57404aabafc53f81a329fd933be8))),
  (strCons, Scalar(0x13e599dbf441b209497d0b4fbad4c010824a95efb8b0e190e30ace2972acd168)): StrCons((char, 'N'), (strCons, Scalar(0x55673d717d7dddfb028bb3a374d3c93fb76633986b8e5cf21741412eb0bf15da))),
  (strCons, Scalar(0x149e234b26c202b85cc81755bb67cd3cd9d925a964d4fe4b57a8c69a5af89ccb)): StrCons((char, 'I'), (strCons, Scalar(0x349deb1224da779897b3b1da555b0fb610cff6b4a551174a45152d7908b8d966))),
  (strCons, Scalar(0x14adef056d3694f57f421922dcf0ced90a8cdc47e94282aa17011f308e777be1)): StrCons((char, 'R'), (strCons, Scalar(0x3b3ebe0feefb800b1116acd34ef1c9dc8ca96b999308a7eaa5a9301dd440c4af))),
  (strCons, Scalar(0x1637f59dea99c4ed1196a5fbd9a646367c2617fbe6e53533277fddff59d94d33)): StrCons((char, 'I'), (strCons, Scalar(0x496f5534848c33c84933babe97d32ea7a7871aae7d77a798be56067d4f59c493))),
  (strCons, Scalar(0x173dd3902e9eb25234ffae8d489509077bad20b20b72fe372209dc14c9a3b537)): StrCons((char, 'B'), (strCons, Scalar(0x0861e4d377a82a1b35d785dad58d581d363f83f57e7820757b0b37f5a0b558b2))),
  (strCons, Scalar(0x19ec9dcc4f273d87d50f490c07138c4e253eaf9cbe0337e18d6f8c2bcdbc9584)): StrCons((char, 'F'), (strNil, Scalar(0))),
  (strCons, Scalar(0x209ed099bed931fe2e5fd04a51ac3e20c604eec3e676e1b6a5f7e2d5ffd71ad7)): StrCons((char, 'E'), (strCons, Scalar(0x4ab487412a1297a8ef131d1e472c7b6061b8fc9029a2017ca977096b1d069e62))),
  (strCons, Scalar(0x25cab0a364aad36374f6638243103dc13c4480adfb9ac025ba8bed3b2d41fa9e)): StrCons((char, 'G'), (strCons, Scalar(0x149e234b26c202b85cc81755bb67cd3cd9d925a964d4fe4b57a8c69a5af89ccb))),
  (strCons, Scalar(0x260eab8bf8043f0a8ed51baf6d94f1905c001411462d1d610413e530c3773176)): StrCons((char, 'D'), (strCons, Scalar(0x71a4b5465b1f3367280f576544cc9c3b952270928f8091fd21c0935e7e1c020b))),
  (strCons, Scalar(0x27aa445d491012b4a2c05bcb8452e3631825c690badbeb10807f22d3cb97edae)): StrCons((char, 'B'), (strNil, Scalar(0))),
  (strCons, Scalar(0x27e0f21c90d2d65cec181d3d3c9225f3253b416b90cf5a4589c6e4bdc2e5fc85)): StrCons((char, '-'), (strCons, Scalar(0x66047f2b10a7be51c444ef9b4b7921ac65789d839929c83ac8a99894dae1a262))),
  (strCons, Scalar(0x29399d25419e332ebc26ef805a948020462fccf7aaf6ea86a684c904cfeec1fb)): StrCons((char, 'T'), (strCons, Scalar(0x27e0f21c90d2d65cec181d3d3c9225f3253b416b90cf5a4589c6e4bdc2e5fc85))),
  (strCons, Scalar(0x2c4473dec23ce858f9b4afe8d200c1bc200d64379d1051901cb9e2e46bed2345)): StrCons((char, '1'), (strNil, Scalar(0))),
  (strCons, Scalar(0x2e57310fb1d91519d0d058ad96b9f2b949754da1d5920f7d55bc7fe09b5fc53b)): StrCons((char, 'N'), (strCons, Scalar(0x2c4473dec23ce858f9b4afe8d200c1bc200d64379d1051901cb9e2e46bed2345))),
  (strCons, Scalar(0x2f72d7fc5782874d8ae63646f9f826c1bba2e495077cbf29e1a47f70e4a054d6)): StrCons((char, 'U'), (strCons, Scalar(0x14adef056d3694f57f421922dcf0ced90a8cdc47e94282aa17011f308e777be1))),
  (strCons, Scalar(0x349deb1224da779897b3b1da555b0fb610cff6b4a551174a45152d7908b8d966)): StrCons((char, 'N'), (strNil, Scalar(0))),
  (strCons, Scalar(0x36240127fa1eb68697c0edca2f3cf8f39e8ec17434d603aa5e9ca83d29af9af6)): StrCons((char, 'M'), (strCons, Scalar(0x3be25926c8c9ba49eb06f4f17cc78ba4b9e89f29fb5a67dba2af8dd6c9b97757))),
  (strCons, Scalar(0x37046281a1b71633bd393c508f6c3bd46d983197c8600c6f0e5369294df65a47)): StrCons((char, 'N'), (strCons, Scalar(0x1637f59dea99c4ed1196a5fbd9a646367c2617fbe6e53533277fddff59d94d33))),
  (strCons, Scalar(0x3a619e372b651520d8cc250f3000d4f47e55f1561a6152f4ae594ee2a7e3445c)): StrCons((char, 'L'), (strCons, Scalar(0x719ec2e9490cfc7aaf903ae718ac79934d2f2041d1198c1b787ee1822da80d20))),
  (strCons, Scalar(0x3b3ebe0feefb800b1116acd34ef1c9dc8ca96b999308a7eaa5a9301dd440c4af)): StrCons((char, 'R'), (strCons, Scalar(0x54c89b701a1a2c7d11453f1352b10cf677718ef1fc0bcc00b05cbc7c0b214b1f))),
  (strCons, Scalar(0x3b6a744c015bc89e58c736ab0af06a0efe6990f29f0f88a3bb9242e7c6168cd2)): StrCons((char, 'X'), (strNil, Scalar(0))),
  (strCons, Scalar(0x3be25926c8c9ba49eb06f4f17cc78ba4b9e89f29fb5a67dba2af8dd6c9b97757)): StrCons((char, 'B'), (strCons, Scalar(0x260eab8bf8043f0a8ed51baf6d94f1905c001411462d1d610413e530c3773176))),
  (strCons, Scalar(0x445f44de0c764d973a7ef6c3361439cc156b57404aabafc53f81a329fd933be8)): StrCons((char, 'O'), (strCons, Scalar(0x4bacbe80754b5387c41fa000c617190e20a116afbb900a8c0238a90e56a2416b))),
  (strCons, Scalar(0x48faae48240f370b917dc62f459c34c849038fda77b73dd551a4e227027d7ecf)): StrCons((char, 'N'), (strCons, Scalar(0x5a80d3586da71faeb9905b1bdc70ef329b313ed405cbb1d44d067cdd38e0739e))),
  (strCons, Scalar(0x496f5534848c33c84933babe97d32ea7a7871aae7d77a798be56067d4f59c493)): StrCons((char, 'L'), (strNil, Scalar(0))),
  (strCons, Scalar(0x49ff152b53db6f73a6119f6f7ac1593d08c905ec13472e22ab498714e813b7a3)): StrCons((char, 'S'), (strCons, Scalar(0x67614dad3f46bc8d20ed66aed635095d93985b5cfc1d9077cba7b7216d5b7904))),
  (strCons, Scalar(0x4ab487412a1297a8ef131d1e472c7b6061b8fc9029a2017ca977096b1d069e62)): StrCons((char, 'T'), (strNil, Scalar(0))),
  (strCons, Scalar(0x4bacbe80754b5387c41fa000c617190e20a116afbb900a8c0238a90e56a2416b)): StrCons((char, 'T'), (strCons, Scalar(0x620460908c90b40fa01c95434e5d2ec7160802e9642b3cca29170bbf8cd35288))),
  (strCons, Scalar(0x4f4b79b17dd45ffd95e2d68e427ca5bf3c3a6cd2abf91a2e3ae1c83644e2f333)): StrCons((char, 'Y'), (strNil, Scalar(0))),
  (strCons, Scalar(0x4fef4cbca131563503f2eb43754515e62d0151fe7224f7f30b1d0421644705a7)): StrCons((char, 'N'), (strCons, Scalar(0x5c5e5c7ca49bd88ae4a178a73f65fe15fef00647748e23acba62275b38c0c0bf))),
  (strCons, Scalar(0x53a594d69d08f89676aaaf6dfc0362be20e8b8670385a1b2396a93902ee8e27f)): StrCons((char, 'N'), (strCons, Scalar(0x29399d25419e332ebc26ef805a948020462fccf7aaf6ea86a684c904cfeec1fb))),
  (strCons, Scalar(0x54c89b701a1a2c7d11453f1352b10cf677718ef1fc0bcc00b05cbc7c0b214b1f)): StrCons((char, 'E'), (strCons, Scalar(0x53a594d69d08f89676aaaf6dfc0362be20e8b8670385a1b2396a93902ee8e27f))),
  (strCons, Scalar(0x5507d3b73af3ee2a59f4d731cf93a367d0472f470bdc037eb1e15180ef82e65c)): StrCons((char, '+'), (strNil, Scalar(0))),
  (strCons, Scalar(0x55673d717d7dddfb028bb3a374d3c93fb76633986b8e5cf21741412eb0bf15da)): StrCons((char, 'V'), (strNil, Scalar(0))),
  (strCons, Scalar(0x593d698d6366dadfbfdc638cc7d93a7234204b3a4d4988e617fea11ad1d6fb75)): StrCons((char, 'G'), (strNil, Scalar(0))),
  (strCons, Scalar(0x5a80d3586da71faeb9905b1bdc70ef329b313ed405cbb1d44d067cdd38e0739e)): StrCons((char, '2'), (strNil, Scalar(0))),
  (strCons, Scalar(0x5ad97b1d6c792609ca09ec8511828c84b2c97e901710b2e940b1a91a61f7b53b)): StrCons((char, 'N'), (strCons, Scalar(0x0a4326c04603b142850d53c90712915bdbc93000be6c3e4e37bd2b5255b8566e))),
  (strCons, Scalar(0x5c5e5c7ca49bd88ae4a178a73f65fe15fef00647748e23acba62275b38c0c0bf)): StrCons((char, '3'), (strNil, Scalar(0))),
  (strCons, Scalar(0x5e51c36e66b3403dfa71bd521200bfd9d26a3d030ef8e652cfcbb0b7c8870122)): StrCons((char, 'R'), (strCons, Scalar(0x726909636803100683eee9f9dbdf86f9f44dc6721d69dc0f9af9378b920103f2))),
  (strCons, Scalar(0x620460908c90b40fa01c95434e5d2ec7160802e9642b3cca29170bbf8cd35288)): StrCons((char, 'E'), (strNil, Scalar(0))),
  (strCons, Scalar(0x66047f2b10a7be51c444ef9b4b7921ac65789d839929c83ac8a99894dae1a262)): StrCons((char, 'E'), (strCons, Scalar(0x13e599dbf441b209497d0b4fbad4c010824a95efb8b0e190e30ace2972acd168))),
  (strCons, Scalar(0x67614dad3f46bc8d20ed66aed635095d93985b5cfc1d9077cba7b7216d5b7904)): StrCons((char, 'T'), (strCons, Scalar(0x5e51c36e66b3403dfa71bd521200bfd9d26a3d030ef8e652cfcbb0b7c8870122))),
  (strCons, Scalar(0x677decaff967d5b61e64476090ebdd98aec61046c259c9abe8194fd8e9c5e8a4)): StrCons((char, 'L'), (strCons, Scalar(0x209ed099bed931fe2e5fd04a51ac3e20c604eec3e676e1b6a5f7e2d5ffd71ad7))),
  (strCons, Scalar(0x681fa69428658ed53c9235f9e70bcc9c24bf44b0b1b0b20b428b2efe5c28af50)): StrCons((char, 'C'), (strCons, Scalar(0x2f72d7fc5782874d8ae63646f9f826c1bba2e495077cbf29e1a47f70e4a054d6))),
  (strCons, Scalar(0x719ec2e9490cfc7aaf903ae718ac79934d2f2041d1198c1b787ee1822da80d20)): StrCons((char, 'A'), (strCons, Scalar(0x36240127fa1eb68697c0edca2f3cf8f39e8ec17434d603aa5e9ca83d29af9af6))),
  (strCons, Scalar(0x71a4b5465b1f3367280f576544cc9c3b952270928f8091fd21c0935e7e1c020b)): StrCons((char, 'A'), (strNil, Scalar(0))),
  (strCons, Scalar(0x726909636803100683eee9f9dbdf86f9f44dc6721d69dc0f9af9378b920103f2)): StrCons((char, 'C'), (strCons, Scalar(0x730bbd2298049dea220e714dcf52d5d767f4d8f1180da4369cf3228ed0b075b7))),
  (strCons, Scalar(0x730bbd2298049dea220e714dcf52d5d767f4d8f1180da4369cf3228ed0b075b7)): StrCons((char, 'O'), (strCons, Scalar(0x5ad97b1d6c792609ca09ec8511828c84b2c97e901710b2e940b1a91a61f7b53b)))
}]

open LSpec in
def main := lspecIO $
  test "Hashing and storing works correctly" (ast.encode.2 == expectedStore)
