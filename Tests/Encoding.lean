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
  (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)): Sym((str, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x003f708b0a3652c2ca439758df5566b6efd083cb72efecc4101fee873e110ff7)): Cons((sym, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1)), (cons, Scalar(0x4e3a91e4eb431f84564d52bde41210ab034c011058dc796b7cb39d5a3bee4e8b))),
  (cons, Scalar(0x006b5029762fc3e2720084df437be440f65c60028f8e2f26c4395e5ba26d2d71)): Cons((nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)), (cons, Scalar(0x0f52796490b9419594a9cf6206c7fe9ed6505cb2a9281510695cd53429765a47))),
  (cons, Scalar(0x00b4eedea469a910fd86c99ca4be95c1439db101048b3eb60ef0f561d70f22b0)): Cons((cons, Scalar(0x3e24805f300670a1bdad1bb5e5b9026d0b37c583642727ead41b08e84010a7ca)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x00b823b81c1bd5189a753cdd69ffff62e6e599a4cbdf7becdb98c4425b6f154d)): Cons((cons, Scalar(0x57235a316dd7f54546176263fcdf053f7a6a6f5603971ec414468b7a58da6c07)), (cons, Scalar(0x558abce766290977f3bbbdb84077f5b84b436259fa6c09664535791372bdd9b6))),
  (cons, Scalar(0x02cef3b98ba782f70623c656749725c980a150bea6de2d864806ae9d2d9c70e2)): Cons((cons, Scalar(0x0f52796490b9419594a9cf6206c7fe9ed6505cb2a9281510695cd53429765a47)), (cons, Scalar(0x4f57f75b7c1cd6ec89219f509c5c8e7bc9b04611df21de7a6cc165ef2251aecd))),
  (cons, Scalar(0x0388847753458e0b60ff77e8b99ab6f9aa339213cb9b49a6ea7c3a7931cc975d)): Cons((cons, Scalar(0x2f53e868814345b557f6defa028c708f2031c0a361245804ec5e0acf1e66f3e6)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x05d051752af7f2a1f33027519ad020d49c996dfcf4b1e6c72f703d093536765f)): Cons((nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)), (cons, Scalar(0x3b627f327d5e211603e41bb97912e5a75164e5003ca5e7d96cf5d8027535ae77))),
  (cons, Scalar(0x072d72a908fb5c48f6eaf7bbfe6f484026c401c45e2655fd3991a932967782dc)): Cons((sym, Scalar(0x1028ac1eac9e763b406b30ac847c3486d858c66753f19043e891901e87b2584e)), (cons, Scalar(0x003f708b0a3652c2ca439758df5566b6efd083cb72efecc4101fee873e110ff7))),
  (cons, Scalar(0x0b1a70079f016689d0fcb79f8588ff32ee6cddcfb8124c2cdcdca14c67f9859b)): Cons((cons, Scalar(0x072d72a908fb5c48f6eaf7bbfe6f484026c401c45e2655fd3991a932967782dc)), (cons, Scalar(0x427ebe790d9611e2d8dff421ff0acead8eff4ccce360ced57f635a62a86df8fd))),
  (cons, Scalar(0x0cac6b109c3e2468ad57f5d6f6bc59622e7d0497cc32e05e0908a057fcc4ec29)): Cons((cons, Scalar(0x4b256689aa12055bd4552ad53cd01a2a70862143b79ecbbd1a3738987e91c931)), (cons, Scalar(0x556f67136013edd44271a1b9270a6f5c0c9e2635b4c4841c8e22b7dc09128890))),
  (cons, Scalar(0x0f52796490b9419594a9cf6206c7fe9ed6505cb2a9281510695cd53429765a47)): Cons((sym, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x1072f1be204a5583e53e1b73b424f6501933d7e441e852a8253a1771313ee093)): Cons((num, 4), (cons, Scalar(0x2f84a38586e2c873fd87f3e5aff255144524c7b7e64d68d8bc1e0393911d33e2))),
  (cons, Scalar(0x11c65efae205c3c467b1254428e6053a2dc307a000de64a4bbdbd830ceaea18f)): Cons((sym, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563)), (cons, Scalar(0x288c77459c3120f971c0e14d9d252b1511dbd42b95fffa363fd87d850862c6d9))),
  (cons, Scalar(0x140bfc8fc5fa7a0f5a0657db6a254f877d49a47da99bd462fe822e2d4f9730c0)): Cons((nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x1714c995141170a7504d3c0b7dcdc36c261e620af7f6a9a98cc1e85043c4c1c6)): Cons((sym, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701)), (cons, Scalar(0x11c65efae205c3c467b1254428e6053a2dc307a000de64a4bbdbd830ceaea18f))),
  (cons, Scalar(0x19ef2b04f5da9d821cd89e5d9cdb99abc19cae9a7f0d540511d68fb3d87b4385)): Cons((cons, Scalar(0x140bfc8fc5fa7a0f5a0657db6a254f877d49a47da99bd462fe822e2d4f9730c0)), (cons, Scalar(0x02cef3b98ba782f70623c656749725c980a150bea6de2d864806ae9d2d9c70e2))),
  (cons, Scalar(0x1a589b68f0f2cd27e456c12583b44dd393a5c0b3bdb1b8ad59afdcaa97f06bfe)): Cons((num, 1), (cons, Scalar(0x5867ac20748a94118c86c3524f2aa8a397524c5fe30b7d9c669c5555ed450a81))),
  (cons, Scalar(0x1b1e32ed25a58fadda7e9fc9f03a2a6aeebad6a0b196993f56594091dddad898)): Cons((cons, Scalar(0x6c77f42d7f5373e58736f3896984ddbaae66797a5aeb2f85cc4db528ab95faa8)), (cons, Scalar(0x00b823b81c1bd5189a753cdd69ffff62e6e599a4cbdf7becdb98c4425b6f154d))),
  (cons, Scalar(0x1f20750fdaacce8a12f7d2bd7ccc3c83381f5af0fc9fe9773f7e6e14449809b0)): Cons((sym, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)), (cons, Scalar(0x5fc66c39f73b2b8b8433b5914ec419ed515bb94f83d646a1dadfbfa0e7f12b38))),
  (cons, Scalar(0x1f2b2621236c3709d09738043a648601ffb9d601be6cf63400d2947e8e7a10f3)): Cons((sym, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x20aacf11fdee25eb6ff764cca09e4d550bf1b29a7eb6f977b94ec1c71f2ca221)): Cons((sym, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x244d3213de92afae9c48433c445c2a5a513c3a7a2060114952a0d0d244d15b10)): Cons((cons, Scalar(0x1f20750fdaacce8a12f7d2bd7ccc3c83381f5af0fc9fe9773f7e6e14449809b0)), (cons, Scalar(0x5e3acea24c6e75a40a2d931db5e85520989a442c59ca464dce04c9c2bb4009b1))),
  (cons, Scalar(0x288c77459c3120f971c0e14d9d252b1511dbd42b95fffa363fd87d850862c6d9)): Cons((sym, Scalar(0x29d4f6a380f3e7eac013478ff3d782b2f64842752e789f4c108a29ce3d8e489d)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x28f1ed4de4a03511da5eb9975ffa5fcf56d338f388fef677c7ab043120c8a6ad)): Cons((sym, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)), (cons, Scalar(0x140bfc8fc5fa7a0f5a0657db6a254f877d49a47da99bd462fe822e2d4f9730c0))),
  (cons, Scalar(0x2da50fd09b3e5a96c4c0c1001722f914bdf005c34964c567e447ff0ae00024b7)): Cons((sym, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701)), (cons, Scalar(0x33516ba5e862f4ef1c698c66d9a15090ba0a79497883f5520cbef46f534adacf))),
  (cons, Scalar(0x2f53e868814345b557f6defa028c708f2031c0a361245804ec5e0acf1e66f3e6)): Cons((sym, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)), (cons, Scalar(0x63bb5ab3e83dd9e7613c74ff4eeea5f97df496c01a324d5a3d536e977685ded2))),
  (cons, Scalar(0x2f84a38586e2c873fd87f3e5aff255144524c7b7e64d68d8bc1e0393911d33e2)): Cons((num, 2), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x30ac0ad28e8eb83942df7d6db04739412b44dedabe072d20ea0a4536b5afa2e3)): Cons((cons, Scalar(0x313956190566a6a15f68301f51289e10581fe4be55421be6f436cfebb1563efb)), (cons, Scalar(0x6aaaa37e55cd5fd882495cd965d805d60862085b2426b627dc7f787424688025))),
  (cons, Scalar(0x313956190566a6a15f68301f51289e10581fe4be55421be6f436cfebb1563efb)): Cons((sym, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723)), (cons, Scalar(0x39780e80a7580c7be8d6a1f34a2294a161a4b90114b92c257bc6f02ff5c7b325))),
  (cons, Scalar(0x32a631ead82a77503f100dea1f57bbc632c80bf692f70d55712ae197127f6f34)): Cons((cons, Scalar(0x3c70c5049abcd7d62539389dd95c207adecc5a56c864eb766da2d93bb1aa602e)), (cons, Scalar(0x0b1a70079f016689d0fcb79f8588ff32ee6cddcfb8124c2cdcdca14c67f9859b))),
  (cons, Scalar(0x33516ba5e862f4ef1c698c66d9a15090ba0a79497883f5520cbef46f534adacf)): Cons((num, 1), (cons, Scalar(0x2f84a38586e2c873fd87f3e5aff255144524c7b7e64d68d8bc1e0393911d33e2))),
  (cons, Scalar(0x34871608739d752c6ef81f4f0ea16006d98a31790ff06e7d1287741fcc1b8b8f)): Cons((cons, Scalar(0x1f2b2621236c3709d09738043a648601ffb9d601be6cf63400d2947e8e7a10f3)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x392dab30f0fd292573fe4972e26fea7bf5d754be356b15e8e54f87ccc9b81fba)): Cons((cons, Scalar(0x0cac6b109c3e2468ad57f5d6f6bc59622e7d0497cc32e05e0908a057fcc4ec29)), (cons, Scalar(0x34871608739d752c6ef81f4f0ea16006d98a31790ff06e7d1287741fcc1b8b8f))),
  (cons, Scalar(0x39780e80a7580c7be8d6a1f34a2294a161a4b90114b92c257bc6f02ff5c7b325)): Cons((sym, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x3a5cfec1229fc38240f7b5991ff2239040ce0bd95f228d5e428eaf430af1ab47)): Cons((sym, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x3b627f327d5e211603e41bb97912e5a75164e5003ca5e7d96cf5d8027535ae77)): Cons((sym, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca)), (cons, Scalar(0x6240be44def3adee43c4e9f635f4a95589b06258760d87d99184b959580ad749))),
  (cons, Scalar(0x3bc0c16456a5865d5e4ec34b3c040207203d7134a3fa75f43b3174bf8cd9b5f9)): Cons((cons, Scalar(0x11c65efae205c3c467b1254428e6053a2dc307a000de64a4bbdbd830ceaea18f)), (cons, Scalar(0x5b1c624e77648c1cc80a238bfde11b4d5f85d251175c469065d9c03bd5ba10b9))),
  (cons, Scalar(0x3c70c5049abcd7d62539389dd95c207adecc5a56c864eb766da2d93bb1aa602e)): Cons((sym, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25)), (cons, Scalar(0x33516ba5e862f4ef1c698c66d9a15090ba0a79497883f5520cbef46f534adacf))),
  (cons, Scalar(0x3cf5dab15835c921ec0093c356b948754b3ddeaf094d7da453c7e546eddd4bdb)): Cons((sym, Scalar(0x64b180d8013903a0e2151686fb3f88c380f30dc34e35b5827324610717bc2e5f)), (cons, Scalar(0x3bc0c16456a5865d5e4ec34b3c040207203d7134a3fa75f43b3174bf8cd9b5f9))),
  (cons, Scalar(0x3e24805f300670a1bdad1bb5e5b9026d0b37c583642727ead41b08e84010a7ca)): Cons((sym, Scalar(0x3da4ebe83cb40ef7e87504d3dd4ece1521c545be0110353725bf781b8db7ffe0)), (cons, Scalar(0x434f75f86fcc06bcb175fe181d674fa7819d401ba000775f2978f25490b2b45c))),
  (cons, Scalar(0x427ebe790d9611e2d8dff421ff0acead8eff4ccce360ced57f635a62a86df8fd)): Cons((cons, Scalar(0x3a5cfec1229fc38240f7b5991ff2239040ce0bd95f228d5e428eaf430af1ab47)), (cons, Scalar(0x1b1e32ed25a58fadda7e9fc9f03a2a6aeebad6a0b196993f56594091dddad898))),
  (cons, Scalar(0x434f75f86fcc06bcb175fe181d674fa7819d401ba000775f2978f25490b2b45c)): Cons((cons, Scalar(0x20aacf11fdee25eb6ff764cca09e4d550bf1b29a7eb6f977b94ec1c71f2ca221)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x4b256689aa12055bd4552ad53cd01a2a70862143b79ecbbd1a3738987e91c931)): Cons((sym, Scalar(0x2444305e7cc57b9dd14da29a082327a597c30609135bd5024eca61afa6de21ef)), (cons, Scalar(0x140bfc8fc5fa7a0f5a0657db6a254f877d49a47da99bd462fe822e2d4f9730c0))),
  (cons, Scalar(0x4e3a91e4eb431f84564d52bde41210ab034c011058dc796b7cb39d5a3bee4e8b)): Cons((sym, Scalar(0x2e527b4e08f9a04b1e18acd2d878f763fcc4012de28c0d9f9ae482a0affd50b0)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x4ecc6109e0b9c48a8c0d3890793ce6acf996962150e6f2d3a8e68f89a940ade4)): Cons((nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)), (cons, Scalar(0x19ef2b04f5da9d821cd89e5d9cdb99abc19cae9a7f0d540511d68fb3d87b4385))),
  (cons, Scalar(0x4f57f75b7c1cd6ec89219f509c5c8e7bc9b04611df21de7a6cc165ef2251aecd)): Cons((cons, Scalar(0x1f2b2621236c3709d09738043a648601ffb9d601be6cf63400d2947e8e7a10f3)), (cons, Scalar(0x6f26e34901754cf147bb9c81a5d5c4d1cb94f667e66385fb9648d38cf7df2577))),
  (cons, Scalar(0x4f7733f9b096ba1fdd89f6a1aed0b31710fd895ee02a2db1ec689a21bbe07596)): Cons((cons, Scalar(0x2da50fd09b3e5a96c4c0c1001722f914bdf005c34964c567e447ff0ae00024b7)), (cons, Scalar(0x30ac0ad28e8eb83942df7d6db04739412b44dedabe072d20ea0a4536b5afa2e3))),
  (cons, Scalar(0x549c354dddb4f9e56204d10f8901a2e69bbf292a65d3039d24a29844f4698ba3)): Cons((num, 3), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x556f67136013edd44271a1b9270a6f5c0c9e2635b4c4841c8e22b7dc09128890)): Cons((cons, Scalar(0x66b9be0d77d8fede13b0d8535bc8e64107e85518e6d95cbbc08809e8d03f36f8)), (cons, Scalar(0x00b4eedea469a910fd86c99ca4be95c1439db101048b3eb60ef0f561d70f22b0))),
  (cons, Scalar(0x558abce766290977f3bbbdb84077f5b84b436259fa6c09664535791372bdd9b6)): Cons((cons, Scalar(0x28f1ed4de4a03511da5eb9975ffa5fcf56d338f388fef677c7ab043120c8a6ad)), (cons, Scalar(0x244d3213de92afae9c48433c445c2a5a513c3a7a2060114952a0d0d244d15b10))),
  (cons, Scalar(0x57235a316dd7f54546176263fcdf053f7a6a6f5603971ec414468b7a58da6c07)): Cons((sym, Scalar(0x671a0cf915c7c57bbdb5710e54daf98ee105d1a25b7f33286f055367f1080b97)), (cons, Scalar(0x392dab30f0fd292573fe4972e26fea7bf5d754be356b15e8e54f87ccc9b81fba))),
  (cons, Scalar(0x5777d9e5dbfbc628ca66a20e8a1794e25e71c8d2b9e4216de1a202e12c26a7f5)): Cons((cons, Scalar(0x4f7733f9b096ba1fdd89f6a1aed0b31710fd895ee02a2db1ec689a21bbe07596)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x5867ac20748a94118c86c3524f2aa8a397524c5fe30b7d9c669c5555ed450a81)): Cons((num, 2), (cons, Scalar(0x549c354dddb4f9e56204d10f8901a2e69bbf292a65d3039d24a29844f4698ba3))),
  (cons, Scalar(0x5b1c624e77648c1cc80a238bfde11b4d5f85d251175c469065d9c03bd5ba10b9)): Cons((cons, Scalar(0x1714c995141170a7504d3c0b7dcdc36c261e620af7f6a9a98cc1e85043c4c1c6)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x5e3acea24c6e75a40a2d931db5e85520989a442c59ca464dce04c9c2bb4009b1)): Cons((cons, Scalar(0x69de94247337239de6fd7e0e95a99f09b19d4be0d5423be26261d05aa3f58e1e)), (cons, Scalar(0x5777d9e5dbfbc628ca66a20e8a1794e25e71c8d2b9e4216de1a202e12c26a7f5))),
  (cons, Scalar(0x5fc66c39f73b2b8b8433b5914ec419ed515bb94f83d646a1dadfbfa0e7f12b38)): Cons((num, 1), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x6240be44def3adee43c4e9f635f4a95589b06258760d87d99184b959580ad749)): Cons((sym, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db)), (cons, Scalar(0x4ecc6109e0b9c48a8c0d3890793ce6acf996962150e6f2d3a8e68f89a940ade4))),
  (cons, Scalar(0x63bb5ab3e83dd9e7613c74ff4eeea5f97df496c01a324d5a3d536e977685ded2)): Cons((cons, Scalar(0x140bfc8fc5fa7a0f5a0657db6a254f877d49a47da99bd462fe822e2d4f9730c0)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x66b9be0d77d8fede13b0d8535bc8e64107e85518e6d95cbbc08809e8d03f36f8)): Cons((sym, Scalar(0x5af25bedb07572d4c00f6ce69f457ce78f446d782e42fb060e896dc6f3983e62)), (cons, Scalar(0x0388847753458e0b60ff77e8b99ab6f9aa339213cb9b49a6ea7c3a7931cc975d))),
  (cons, Scalar(0x69de94247337239de6fd7e0e95a99f09b19d4be0d5423be26261d05aa3f58e1e)): Cons((sym, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)), (cons, Scalar(0x710f6211448df6c15a18a75558979b2354f0a7d8036e1710a804969406937990))),
  (cons, Scalar(0x6aaaa37e55cd5fd882495cd965d805d60862085b2426b627dc7f787424688025)): Cons((sym, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25)), (cons, Scalar(0x1072f1be204a5583e53e1b73b424f6501933d7e441e852a8253a1771313ee093))),
  (cons, Scalar(0x6c77f42d7f5373e58736f3896984ddbaae66797a5aeb2f85cc4db528ab95faa8)): Cons((sym, Scalar(0x46a73d19fdba68053290fc8832ece67857cb01ef5d0072c1afe73c0eeb7143e4)), (cons, Scalar(0x11c65efae205c3c467b1254428e6053a2dc307a000de64a4bbdbd830ceaea18f))),
  (cons, Scalar(0x6f26e34901754cf147bb9c81a5d5c4d1cb94f667e66385fb9648d38cf7df2577)): Cons((cons, Scalar(0x006b5029762fc3e2720084df437be440f65c60028f8e2f26c4395e5ba26d2d71)), (cons, Scalar(0x729d3adc6dd0d44f084a2010272a9afd37ebb4b4c314d358c06d42630fe5680f))),
  (cons, Scalar(0x70e904dac08166fcdf68bc467a865cbd01c6f5a40c9fdb576676e077854008e7)): Cons((sym, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024)), (cons, Scalar(0x05d051752af7f2a1f33027519ad020d49c996dfcf4b1e6c72f703d093536765f))),
  (cons, Scalar(0x710f6211448df6c15a18a75558979b2354f0a7d8036e1710a804969406937990)): Cons((cons, Scalar(0x1a589b68f0f2cd27e456c12583b44dd393a5c0b3bdb1b8ad59afdcaa97f06bfe)), (nil, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (cons, Scalar(0x729d3adc6dd0d44f084a2010272a9afd37ebb4b4c314d358c06d42630fe5680f)): Cons((cons, Scalar(0x3cf5dab15835c921ec0093c356b948754b3ddeaf094d7da453c7e546eddd4bdb)), (cons, Scalar(0x32a631ead82a77503f100dea1f57bbc632c80bf692f70d55712ae197127f6f34))),
  (sym, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1)): Sym((str, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1))),
  (sym, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024)): Sym((str, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024))),
  (sym, Scalar(0x1028ac1eac9e763b406b30ac847c3486d858c66753f19043e891901e87b2584e)): Sym((str, Scalar(0x1028ac1eac9e763b406b30ac847c3486d858c66753f19043e891901e87b2584e))),
  (sym, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca)): Sym((str, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca))),
  (sym, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563)): Sym((str, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563))),
  (sym, Scalar(0x2444305e7cc57b9dd14da29a082327a597c30609135bd5024eca61afa6de21ef)): Sym((str, Scalar(0x2444305e7cc57b9dd14da29a082327a597c30609135bd5024eca61afa6de21ef))),
  (sym, Scalar(0x29d4f6a380f3e7eac013478ff3d782b2f64842752e789f4c108a29ce3d8e489d)): Sym((str, Scalar(0x29d4f6a380f3e7eac013478ff3d782b2f64842752e789f4c108a29ce3d8e489d))),
  (sym, Scalar(0x2e527b4e08f9a04b1e18acd2d878f763fcc4012de28c0d9f9ae482a0affd50b0)): Sym((str, Scalar(0x2e527b4e08f9a04b1e18acd2d878f763fcc4012de28c0d9f9ae482a0affd50b0))),
  (sym, Scalar(0x3da4ebe83cb40ef7e87504d3dd4ece1521c545be0110353725bf781b8db7ffe0)): Sym((str, Scalar(0x3da4ebe83cb40ef7e87504d3dd4ece1521c545be0110353725bf781b8db7ffe0))),
  (sym, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25)): Sym((str, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25))),
  (sym, Scalar(0x46a73d19fdba68053290fc8832ece67857cb01ef5d0072c1afe73c0eeb7143e4)): Sym((str, Scalar(0x46a73d19fdba68053290fc8832ece67857cb01ef5d0072c1afe73c0eeb7143e4))),
  (sym, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db)): Sym((str, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db))),
  (sym, Scalar(0x5af25bedb07572d4c00f6ce69f457ce78f446d782e42fb060e896dc6f3983e62)): Sym((str, Scalar(0x5af25bedb07572d4c00f6ce69f457ce78f446d782e42fb060e896dc6f3983e62))),
  (sym, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723)): Sym((str, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723))),
  (sym, Scalar(0x64b180d8013903a0e2151686fb3f88c380f30dc34e35b5827324610717bc2e5f)): Sym((str, Scalar(0x64b180d8013903a0e2151686fb3f88c380f30dc34e35b5827324610717bc2e5f))),
  (sym, Scalar(0x671a0cf915c7c57bbdb5710e54daf98ee105d1a25b7f33286f055367f1080b97)): Sym((str, Scalar(0x671a0cf915c7c57bbdb5710e54daf98ee105d1a25b7f33286f055367f1080b97))),
  (sym, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)): Sym((str, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7))),
  (sym, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701)): Sym((str, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701))),
  (str, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1)): Str((strCons, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1))),
  (str, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024)): Str((strCons, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024))),
  (str, Scalar(0x1028ac1eac9e763b406b30ac847c3486d858c66753f19043e891901e87b2584e)): Str((strCons, Scalar(0x1028ac1eac9e763b406b30ac847c3486d858c66753f19043e891901e87b2584e))),
  (str, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca)): Str((strCons, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca))),
  (str, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563)): Str((strCons, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563))),
  (str, Scalar(0x2444305e7cc57b9dd14da29a082327a597c30609135bd5024eca61afa6de21ef)): Str((strCons, Scalar(0x2444305e7cc57b9dd14da29a082327a597c30609135bd5024eca61afa6de21ef))),
  (str, Scalar(0x29d4f6a380f3e7eac013478ff3d782b2f64842752e789f4c108a29ce3d8e489d)): Str((strCons, Scalar(0x29d4f6a380f3e7eac013478ff3d782b2f64842752e789f4c108a29ce3d8e489d))),
  (str, Scalar(0x2e527b4e08f9a04b1e18acd2d878f763fcc4012de28c0d9f9ae482a0affd50b0)): Str((strCons, Scalar(0x2e527b4e08f9a04b1e18acd2d878f763fcc4012de28c0d9f9ae482a0affd50b0))),
  (str, Scalar(0x3da4ebe83cb40ef7e87504d3dd4ece1521c545be0110353725bf781b8db7ffe0)): Str((strCons, Scalar(0x3da4ebe83cb40ef7e87504d3dd4ece1521c545be0110353725bf781b8db7ffe0))),
  (str, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25)): Str((strCons, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25))),
  (str, Scalar(0x46a73d19fdba68053290fc8832ece67857cb01ef5d0072c1afe73c0eeb7143e4)): Str((strCons, Scalar(0x46a73d19fdba68053290fc8832ece67857cb01ef5d0072c1afe73c0eeb7143e4))),
  (str, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db)): Str((strCons, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db))),
  (str, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)): Str((strCons, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366))),
  (str, Scalar(0x5af25bedb07572d4c00f6ce69f457ce78f446d782e42fb060e896dc6f3983e62)): Str((strCons, Scalar(0x5af25bedb07572d4c00f6ce69f457ce78f446d782e42fb060e896dc6f3983e62))),
  (str, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723)): Str((strCons, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723))),
  (str, Scalar(0x64b180d8013903a0e2151686fb3f88c380f30dc34e35b5827324610717bc2e5f)): Str((strCons, Scalar(0x64b180d8013903a0e2151686fb3f88c380f30dc34e35b5827324610717bc2e5f))),
  (str, Scalar(0x671a0cf915c7c57bbdb5710e54daf98ee105d1a25b7f33286f055367f1080b97)): Str((strCons, Scalar(0x671a0cf915c7c57bbdb5710e54daf98ee105d1a25b7f33286f055367f1080b97))),
  (str, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)): Str((strCons, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7))),
  (str, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701)): Str((strCons, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701))),
  (strCons, Scalar(0x00821eb8f3d483be7691e31a281bbfa482227e46bc485eaa4a1aaecfbfa2ac60)): StrCons((char, 'L'), (strNil, Scalar(0))),
  (strCons, Scalar(0x00a9e7895b491291d977fc971789a34d4992826f25917d1c7f5fce9336c1a450)): StrCons((char, '2'), (strNil, Scalar(0))),
  (strCons, Scalar(0x026850169c06101573432e10717e6fbe009723fe3cdd7bf903d9c514af133562)): StrCons((char, 'I'), (strCons, Scalar(0x00821eb8f3d483be7691e31a281bbfa482227e46bc485eaa4a1aaecfbfa2ac60))),
  (strCons, Scalar(0x028349bb58faf07b5fcec7323ab3d1cde90de91f54dd924955fc4d4af3b3f3dd)): StrCons((char, '1'), (strNil, Scalar(0))),
  (strCons, Scalar(0x04526cacdf0d71d0abe845ad9829419abb10a489d51a5f580a0a8f55db7f50c3)): StrCons((char, 'R'), (strCons, Scalar(0x37fa8084fbf64dc9447e98c7b79b727fc4e2829cee2ed6c3c27c54ddede47019))),
  (strCons, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1)): StrCons((char, 'A'), (strNil, Scalar(0))),
  (strCons, Scalar(0x0aabb78f5c1648ac0c34c2c3e7b03dc600a89033332816690b73d5338f1021f2)): StrCons((char, 'T'), (strCons, Scalar(0x47178dae84a9c84a8133586570cff8468688e9df337f67cb10dc3618f9563655))),
  (strCons, Scalar(0x0e43d12b21f360de90cc467b16ad432a2823140904a70dd8a9f3e5c4b78df024)): StrCons((char, 'B'), (strCons, Scalar(0x395cc8c8de54958eb3d40bad2c3fee64cfbb74d658ffee85d2eafba6c53d08d9))),
  (strCons, Scalar(0x0f000e9fec9cd246b1298ad548d844e77292de9f960ce9bc66d76f0d2440f869)): StrCons((char, 'T'), (strCons, Scalar(0x6f6811728827ce453bb8b61446227113fc3faca4c3b3b595a2f82e2865dc54b4))),
  (strCons, Scalar(0x1028ac1eac9e763b406b30ac847c3486d858c66753f19043e891901e87b2584e)): StrCons((char, 'S'), (strCons, Scalar(0x0f000e9fec9cd246b1298ad548d844e77292de9f960ce9bc66d76f0d2440f869))),
  (strCons, Scalar(0x116485f98b0a6d51f34331e934f957455c72d18b0abfcb45318971c234ed900f)): StrCons((char, 'O'), (strCons, Scalar(0x0aabb78f5c1648ac0c34c2c3e7b03dc600a89033332816690b73d5338f1021f2))),
  (strCons, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca)): StrCons((char, 'T'), (strNil, Scalar(0))),
  (strCons, Scalar(0x1407cd0907fa4e873a9de2ba6ae85b60b674c5c2fce6234d053fb54a2a5af01e)): StrCons((char, 'E'), (strCons, Scalar(0x544db7b3b540dc13e61388e2dc21194a18ad1305934890734ea00e0b14a6ff00))),
  (strCons, Scalar(0x155c79e247f34ebf672db1f83abf897140da0b699e266a1836c884cebe2c07ea)): StrCons((char, 'D'), (strCons, Scalar(0x0a742132187c2f609306848d8ccbc6349c5fe12e644e9ecbbe769caa824142b1))),
  (strCons, Scalar(0x17f0ca334ecaf4ffddfc490a98ee6b8d34f4d15a4646e04666a2034042bba505)): StrCons((char, '-'), (strCons, Scalar(0x4ef39bb0bbe05642a5e3a8e9df2afc26da47e8754ab52eaa5e91f621da885d58))),
  (strCons, Scalar(0x19fd749358cc36a22281d2ce5756ca6813a52fb7658248de29b40d36402d8563)): StrCons((char, 'X'), (strNil, Scalar(0))),
  (strCons, Scalar(0x1eef61065619af67a4dedfe9cbf7202388ee481208b5382cf98a89b61331764c)): StrCons((char, 'B'), (strCons, Scalar(0x155c79e247f34ebf672db1f83abf897140da0b699e266a1836c884cebe2c07ea))),
  (strCons, Scalar(0x1fd1d7333359e5bbfaecd9601f9c2fa3bc90090fccb014bf0daa095ba5f2d301)): StrCons((char, 'N'), (strCons, Scalar(0x33136ba937b8d78a6bb989e9213efbac1fd4fc0f9668b036c622fcc55d7a664b))),
  (strCons, Scalar(0x2444305e7cc57b9dd14da29a082327a597c30609135bd5024eca61afa6de21ef)): StrCons((char, 'N'), (strCons, Scalar(0x028349bb58faf07b5fcec7323ab3d1cde90de91f54dd924955fc4d4af3b3f3dd))),
  (strCons, Scalar(0x29d4f6a380f3e7eac013478ff3d782b2f64842752e789f4c108a29ce3d8e489d)): StrCons((char, 'Y'), (strNil, Scalar(0))),
  (strCons, Scalar(0x2cc89b471ff09ed1278d10c4d1b5fe3437e369fc1095d1e64250eb6bcb5a2f45)): StrCons((char, 'M'), (strCons, Scalar(0x1eef61065619af67a4dedfe9cbf7202388ee481208b5382cf98a89b61331764c))),
  (strCons, Scalar(0x2e527b4e08f9a04b1e18acd2d878f763fcc4012de28c0d9f9ae482a0affd50b0)): StrCons((char, 'B'), (strNil, Scalar(0))),
  (strCons, Scalar(0x3118b30e4b4e3cc635af6f130cbea6967a9bcb47f14132a941be04f85cfe8047)): StrCons((char, 'E'), (strCons, Scalar(0x12df653736b06280dec7a165883140e6ad7cd14024f3b910b796dc1eef5de7ca))),
  (strCons, Scalar(0x33136ba937b8d78a6bb989e9213efbac1fd4fc0f9668b036c622fcc55d7a664b)): StrCons((char, 'S'), (strNil, Scalar(0))),
  (strCons, Scalar(0x37fa8084fbf64dc9447e98c7b79b727fc4e2829cee2ed6c3c27c54ddede47019)): StrCons((char, 'R'), (strCons, Scalar(0x1407cd0907fa4e873a9de2ba6ae85b60b674c5c2fce6234d053fb54a2a5af01e))),
  (strCons, Scalar(0x395cc8c8de54958eb3d40bad2c3fee64cfbb74d658ffee85d2eafba6c53d08d9)): StrCons((char, 'E'), (strCons, Scalar(0x6aa3f2cb1c896b198f13f66adbccd07187e4b039584a096689767570a9c565b5))),
  (strCons, Scalar(0x3cf23c06ce2a2a47005285dbd640e1e28d88abfdc7d84e1c5f1f9ebe8824a41b)): StrCons((char, 'U'), (strCons, Scalar(0x04526cacdf0d71d0abe845ad9829419abb10a489d51a5f580a0a8f55db7f50c3))),
  (strCons, Scalar(0x3da4ebe83cb40ef7e87504d3dd4ece1521c545be0110353725bf781b8db7ffe0)): StrCons((char, 'N'), (strCons, Scalar(0x469983e91629f50bd6a45253f62ec32500f9c120c9330a9c497d781fb3b1fa90))),
  (strCons, Scalar(0x3eb44f9bbba0ae6b75a2cb443f4bd030c42a899bc5b23336ae80a2b252111add)): StrCons((char, 'A'), (strCons, Scalar(0x2cc89b471ff09ed1278d10c4d1b5fe3437e369fc1095d1e64250eb6bcb5a2f45))),
  (strCons, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25)): StrCons((char, 'C'), (strCons, Scalar(0x4bf98f00be5c0ac3aa44f75d7628493a4b788ec518077cacab0b337541077caf))),
  (strCons, Scalar(0x469983e91629f50bd6a45253f62ec32500f9c120c9330a9c497d781fb3b1fa90)): StrCons((char, '3'), (strNil, Scalar(0))),
  (strCons, Scalar(0x46a73d19fdba68053290fc8832ece67857cb01ef5d0072c1afe73c0eeb7143e4)): StrCons((char, 'G'), (strNil, Scalar(0))),
  (strCons, Scalar(0x47178dae84a9c84a8133586570cff8468688e9df337f67cb10dc3618f9563655)): StrCons((char, 'E'), (strNil, Scalar(0))),
  (strCons, Scalar(0x49609d16a4131d9caaeee716c819459d61cc9900d93bf359e0c1124a77e0d4e6)): StrCons((char, 'V'), (strNil, Scalar(0))),
  (strCons, Scalar(0x49ef1bbdb07c91455fd9c6186db24bc885e3fd3686d6da796ceb6f44c02cf047)): StrCons((char, 'N'), (strNil, Scalar(0))),
  (strCons, Scalar(0x4bf98f00be5c0ac3aa44f75d7628493a4b788ec518077cacab0b337541077caf)): StrCons((char, 'O'), (strCons, Scalar(0x1fd1d7333359e5bbfaecd9601f9c2fa3bc90090fccb014bf0daa095ba5f2d301))),
  (strCons, Scalar(0x4ef39bb0bbe05642a5e3a8e9df2afc26da47e8754ab52eaa5e91f621da885d58)): StrCons((char, 'E'), (strCons, Scalar(0x585b575972bf70e5b679daf85f7bb694a4e6ca4c5256d1ab4b23fc1082b23974))),
  (strCons, Scalar(0x50f9056f99c1dd99fd22b88acb8cee821534593e367b8c05a52e882e74980d62)): StrCons((char, 'U'), (strCons, Scalar(0x116485f98b0a6d51f34331e934f957455c72d18b0abfcb45318971c234ed900f))),
  (strCons, Scalar(0x52e16c306cfd4edbb4174a6ae0c73032705e57a0250977e30dfe365f514525db)): StrCons((char, 'C'), (strCons, Scalar(0x3cf23c06ce2a2a47005285dbd640e1e28d88abfdc7d84e1c5f1f9ebe8824a41b))),
  (strCons, Scalar(0x544db7b3b540dc13e61388e2dc21194a18ad1305934890734ea00e0b14a6ff00)): StrCons((char, 'N'), (strCons, Scalar(0x66c680a5385ca83380a1176452ec2ac6bf309acf517224ea1614063e58f4aa17))),
  (strCons, Scalar(0x56673ef243eaf36cda6c3d8f20bbac4cab3dadabe8b7fc776f3d20e9b8b70366)): StrCons((char, 'N'), (strCons, Scalar(0x026850169c06101573432e10717e6fbe009723fe3cdd7bf903d9c514af133562))),
  (strCons, Scalar(0x585b575972bf70e5b679daf85f7bb694a4e6ca4c5256d1ab4b23fc1082b23974)): StrCons((char, 'N'), (strCons, Scalar(0x49609d16a4131d9caaeee716c819459d61cc9900d93bf359e0c1124a77e0d4e6))),
  (strCons, Scalar(0x5af25bedb07572d4c00f6ce69f457ce78f446d782e42fb060e896dc6f3983e62)): StrCons((char, 'N'), (strCons, Scalar(0x00a9e7895b491291d977fc971789a34d4992826f25917d1c7f5fce9336c1a450))),
  (strCons, Scalar(0x600bed84bf074e7a9a62ff4bde8350b541fdade55fdc212c607349b9b7265723)): StrCons((char, 'F'), (strNil, Scalar(0))),
  (strCons, Scalar(0x64b180d8013903a0e2151686fb3f88c380f30dc34e35b5827324610717bc2e5f)): StrCons((char, 'L'), (strCons, Scalar(0x3eb44f9bbba0ae6b75a2cb443f4bd030c42a899bc5b23336ae80a2b252111add))),
  (strCons, Scalar(0x66c680a5385ca83380a1176452ec2ac6bf309acf517224ea1614063e58f4aa17)): StrCons((char, 'T'), (strCons, Scalar(0x17f0ca334ecaf4ffddfc490a98ee6b8d34f4d15a4646e04666a2034042bba505))),
  (strCons, Scalar(0x671a0cf915c7c57bbdb5710e54daf98ee105d1a25b7f33286f055367f1080b97)): StrCons((char, 'L'), (strCons, Scalar(0x3118b30e4b4e3cc635af6f130cbea6967a9bcb47f14132a941be04f85cfe8047))),
  (strCons, Scalar(0x68ef4abba158a16d1ab437f8480a3a9336ac38c3b7bd111d9a6bb6d151bb08b7)): StrCons((char, 'Q'), (strCons, Scalar(0x50f9056f99c1dd99fd22b88acb8cee821534593e367b8c05a52e882e74980d62))),
  (strCons, Scalar(0x6aa3f2cb1c896b198f13f66adbccd07187e4b039584a096689767570a9c565b5)): StrCons((char, 'G'), (strCons, Scalar(0x6e6e74af49f2748524facee96852f13740683e624552935545af4a4ea1988ee8))),
  (strCons, Scalar(0x6e6e74af49f2748524facee96852f13740683e624552935545af4a4ea1988ee8)): StrCons((char, 'I'), (strCons, Scalar(0x49ef1bbdb07c91455fd9c6186db24bc885e3fd3686d6da796ceb6f44c02cf047))),
  (strCons, Scalar(0x6f6811728827ce453bb8b61446227113fc3faca4c3b3b595a2f82e2865dc54b4)): StrCons((char, 'R'), (strCons, Scalar(0x43624ce9ff1458e20f42f0fb87f06bb1a6f7d8ce29d8e0f379d35e8491b77e25))),
  (strCons, Scalar(0x72f76cf396008c69707c13ced0392956668b566a2fccbcb446073ff9d77da701)): StrCons((char, '+'), (strNil, Scalar(0)))
}]

open LSpec in
def main := lspecIO $
  test "Hashing and storing works correctly" (ast.encode.2 == expectedStore)
