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
  (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc)): Sym((str, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x0549b5025c3ed8245bb7c4e6e5cb543bf59dac8d1297af7290c0f12fe690d8d5)): Cons((sym, Scalar(0x69807c7b2c7b867b224bb30fef5b56e956fa3a58173a0d1ff1dce5c44c08e340)), (cons, Scalar(0x16e94fb57a061c7376bc260508e130caa831fffc2961a58342de2132f42c3fe3))),
  (cons, Scalar(0x055a0897509afd60a4974d6ff7685bd8fdc93bb7343e3c43b0bf4707a25181d8)): Cons((sym, Scalar(0x6e9554403114c390be3c9ef295b3e19a31b028d8d86b0ad8a5bb93e321cddab0)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x05cc4799f3a749664357885f06ac9797da75095382ee6cad82abf52d140dce3d)): Cons((cons, Scalar(0x557e7b6e08b333e6d61c23694277037771d47552de64435ba28a89720e355fe5)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x07a57756afe138f7adc1e4d8d48107919def115ec0744df1ed4b92459ade04ba)): Cons((cons, Scalar(0x428280cc53b2f6ec83a350136c099e9455ab7469fbb140f590ce83e645d84c82)), (cons, Scalar(0x4665729a5ee5bda68178ef917eb0f72aa4478e9f42ea6a066dd4a53d9a2925bf))),
  (cons, Scalar(0x093ed78c967d5ceb43240a881c87ea8b02876a253b3521c15d73afae7c392b1b)): Cons((cons, Scalar(0x1cfa39c5a66134ebecb4b4442bef2a263128add5cad740535e4eb6d500883309)), (cons, Scalar(0x5664640efd5d952e69958e0702ccd6ad8d08452cb31f2b0e0349dce3677d2732))),
  (cons, Scalar(0x0c92e52d617c3adff9d9df08c91ec4f20b6759460fa8fbbd9da7ed4aa633804d)): Cons((sym, Scalar(0x6ff1114edbb2a68a987f6c2bdf61210f46dbfcf3fe38c408f0bbbdbcf16490c4)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x0cd78276183e21bfbba1a3ce3491d17e25e465318c3cb6f0af8d0ab9c1cd687e)): Cons((cons, Scalar(0x35f78e9534c042d03014ecd047fd4a717192675b7b3834f80531ae1050a96e15)), (cons, Scalar(0x07a57756afe138f7adc1e4d8d48107919def115ec0744df1ed4b92459ade04ba))),
  (cons, Scalar(0x1063964004f9854ff1a568edf78df18ecbb99e1128a6b8751b9f1ea0c770c24e)): Cons((cons, Scalar(0x6d947a19abcd3ae22e59d7066620a9a0f2106b79a95b2fbda8ab53dfd57cb775)), (cons, Scalar(0x5a83f9d4670a63c6204d5b51644c555dde136cefc000b59b09c3554178d51cfb))),
  (cons, Scalar(0x1193389f4e388b95b6e89a7cd8d7277c94ede7285d5e5632c28bf68acd5674a1)): Cons((sym, Scalar(0x27c4fe61970f7f0fd6f2989a1ee60ee2dd1d92d9acfcb16c731e521efbf7ca33)), (cons, Scalar(0x5ee78001bd68e9ad7ca725e3822af38077da730bd61345f7a3079beb4b8d2d34))),
  (cons, Scalar(0x129a12c8b716f5b794457e762c551cb196307207a8985919c0255b985782579c)): Cons((sym, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3)), (cons, Scalar(0x262ec53f330a2510efa96999165ff9403437b81d5fd9c8af55f14e9b36a957b2))),
  (cons, Scalar(0x14947d3b8cc6ba04608b46ded46ea8b133c5e9e7df5ef0ade71c49eedaa3294f)): Cons((num, 2), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x14c55e7c8c0d3baf62f89b94797ce9343bb705490739c54704f6756d2c53a5e5)): Cons((cons, Scalar(0x60f8bde368605836ec2f3b6236ba82802618b757966983bd1a3a2b7a58255877)), (cons, Scalar(0x20d77c2eb8acadc12e4805fcb9b1ad32feabb257a7bc27947b0c7b948b948ee8))),
  (cons, Scalar(0x152f627ee52003128e9b65d438a9d04f62ccc6180b0bb33c878b3d568a6c668d)): Cons((cons, Scalar(0x1063964004f9854ff1a568edf78df18ecbb99e1128a6b8751b9f1ea0c770c24e)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x16e4897a0e717d6d649c7d97983564c57374a8c37b684cafcf8eca7c30ddff9c)): Cons((num, 2), (cons, Scalar(0x1729366729abf0ee544552ccc635f40e67d585d56b7439d74c337dee2c1b7355))),
  (cons, Scalar(0x16e79d6883e4939447c97c215bb09e4b5835d16ac8d4f7f4193f78574e9a696b)): Cons((sym, Scalar(0x6ff1114edbb2a68a987f6c2bdf61210f46dbfcf3fe38c408f0bbbdbcf16490c4)), (cons, Scalar(0x0549b5025c3ed8245bb7c4e6e5cb543bf59dac8d1297af7290c0f12fe690d8d5))),
  (cons, Scalar(0x16e94fb57a061c7376bc260508e130caa831fffc2961a58342de2132f42c3fe3)): Cons((nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc)), (cons, Scalar(0x310e4c794165642a740528885ef43cda8034557257898d1e1cb0379b04936b31))),
  (cons, Scalar(0x1729366729abf0ee544552ccc635f40e67d585d56b7439d74c337dee2c1b7355)): Cons((num, 3), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x17e668b724ad87d199bba82974b8ec8d2ae153da4f11acd57328c0b7237dc2ca)): Cons((cons, Scalar(0x3f2bea2d24213c6899861e3605380253ace6eec2a903b93c3f71132b388888ac)), (cons, Scalar(0x23f6d81eb9dc92d57c284490332178d25e78aa03f154546f646465ee3cbe3d5a))),
  (cons, Scalar(0x187e2763825abb625685f034871191c7130aafdc0b7f3c479e85966afeb16499)): Cons((sym, Scalar(0x41b4124313d59394046b0fa3c088d77322d25c50d05d47ba8747fd0834d16aa2)), (cons, Scalar(0x1f520f793c0cc3b1b65f52b372d5e48e5b4a26b80dd1dfb5247e9a4af61d50aa))),
  (cons, Scalar(0x196e8eba475a9908331fab7be768a07a136a04687317f474d04228904ca06c57)): Cons((cons, Scalar(0x379f6b6edc496da30549f6361aeb8e515701c7b3a8ce9a3b4cad581e69418550)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x1af662387bf02e6c899203a194c56d1d74b6cb5bb61d4c5e6de169c151a89a0f)): Cons((sym, Scalar(0x44539d9a8d172ff4b6baedf6095780746d7da97f4f47b16ef613b4f0e0683f1d)), (cons, Scalar(0x05cc4799f3a749664357885f06ac9797da75095382ee6cad82abf52d140dce3d))),
  (cons, Scalar(0x1cfa39c5a66134ebecb4b4442bef2a263128add5cad740535e4eb6d500883309)): Cons((cons, Scalar(0x56cfe0d95f7abd105dc5e0a386995c7a4ef0d428d2b7b1a984b4d8ad99339ec9)), (cons, Scalar(0x2fb440ca6a30cde55576ba24d778ce783d1b6ecbfd8a59f4487b62dfb379da89))),
  (cons, Scalar(0x1ef2dbcdae49b5987bab5c0b1b4c3d8ee56fb340c2f50d04c71567e702a5712f)): Cons((cons, Scalar(0x63dd6f342f1b5a46f75d13c69058b06e50b80d51cacd05d7b4f68288c8206dcf)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x1f520f793c0cc3b1b65f52b372d5e48e5b4a26b80dd1dfb5247e9a4af61d50aa)): Cons((nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc)), (cons, Scalar(0x16e79d6883e4939447c97c215bb09e4b5835d16ac8d4f7f4193f78574e9a696b))),
  (cons, Scalar(0x1fdf558e039ec31be1c1904059fb08af9073d8e9adb04a876b7f6474bcd696bf)): Cons((cons, Scalar(0x3c9dba12750a5cbb3ee67cd0486546234c0616ffaed3cda722e320f19ef01f52)), (cons, Scalar(0x0cd78276183e21bfbba1a3ce3491d17e25e465318c3cb6f0af8d0ab9c1cd687e))),
  (cons, Scalar(0x20d77c2eb8acadc12e4805fcb9b1ad32feabb257a7bc27947b0c7b948b948ee8)): Cons((cons, Scalar(0x324c43bd20b625ff4c27157d9bba73cd01ec55545a0fcebf20e7ce1e17de315e)), (cons, Scalar(0x514b67aabcc2ff1f4a9f43e8bd61ff8726aa3602c690c252b19086e095b37604))),
  (cons, Scalar(0x23f6d81eb9dc92d57c284490332178d25e78aa03f154546f646465ee3cbe3d5a)): Cons((cons, Scalar(0x6570de9248c6d1c479e17b8ea743ee4cda581bbb99ef69d5d9876871e1195f61)), (cons, Scalar(0x14c55e7c8c0d3baf62f89b94797ce9343bb705490739c54704f6756d2c53a5e5))),
  (cons, Scalar(0x24d55339300aa0cd736b6ce04fed8a457f032df17b9642d77c13fde79fd3a076)): Cons((sym, Scalar(0x3b4805e52d6de38cbf960ef7f15538029834695a4c1abdda38dc9a870220bf84)), (cons, Scalar(0x055a0897509afd60a4974d6ff7685bd8fdc93bb7343e3c43b0bf4707a25181d8))),
  (cons, Scalar(0x24e9b1c7d25353eae520b0ca7b8dc9a94b90c1a75b23a561e2dd57db6b2cb35c)): Cons((sym, Scalar(0x41b4124313d59394046b0fa3c088d77322d25c50d05d47ba8747fd0834d16aa2)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x25a937f0d1cd897a36637741d9b38673eaaf17c0c9eb1da64cdc07c3791b5817)): Cons((cons, Scalar(0x6bbb0c72a545676b8a770044da938e19861c3358c7c5d6c4ba61320d67b169d2)), (cons, Scalar(0x196e8eba475a9908331fab7be768a07a136a04687317f474d04228904ca06c57))),
  (cons, Scalar(0x262ec53f330a2510efa96999165ff9403437b81d5fd9c8af55f14e9b36a957b2)): Cons((num, 1), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x2816e143451f879c5e5bc27684d5808136a3a8f5f2c43179410b60f201156a28)): Cons((cons, Scalar(0x3a7981615296edc8b2e91270394b8d40b88e2570bf28cc6a095503529d0653b2)), (cons, Scalar(0x152f627ee52003128e9b65d438a9d04f62ccc6180b0bb33c878b3d568a6c668d))),
  (cons, Scalar(0x2b8d9ae786386fc5ff999ec838d001fe1b1c0e6955983b7b2d029129546cbe02)): Cons((num, 1), (cons, Scalar(0x16e4897a0e717d6d649c7d97983564c57374a8c37b684cafcf8eca7c30ddff9c))),
  (cons, Scalar(0x2d5dd3254b99bb432d07502b7fb38d1bd5e10b3f3080453a6053750f837230e4)): Cons((cons, Scalar(0x0c92e52d617c3adff9d9df08c91ec4f20b6759460fa8fbbd9da7ed4aa633804d)), (cons, Scalar(0x17e668b724ad87d199bba82974b8ec8d2ae153da4f11acd57328c0b7237dc2ca))),
  (cons, Scalar(0x2fb440ca6a30cde55576ba24d778ce783d1b6ecbfd8a59f4487b62dfb379da89)): Cons((cons, Scalar(0x1af662387bf02e6c899203a194c56d1d74b6cb5bb61d4c5e6de169c151a89a0f)), (cons, Scalar(0x563e7bd6ea783fbe2a11cf45bc2a5c8bfb9d4736993e86ba2319732b61335353))),
  (cons, Scalar(0x310e4c794165642a740528885ef43cda8034557257898d1e1cb0379b04936b31)): Cons((cons, Scalar(0x63dd6f342f1b5a46f75d13c69058b06e50b80d51cacd05d7b4f68288c8206dcf)), (cons, Scalar(0x2d5dd3254b99bb432d07502b7fb38d1bd5e10b3f3080453a6053750f837230e4))),
  (cons, Scalar(0x324c43bd20b625ff4c27157d9bba73cd01ec55545a0fcebf20e7ce1e17de315e)): Cons((sym, Scalar(0x65b3657600c366c323d6024c3fc30d8d44fe8e1c78e931c021b754506e9de2eb)), (cons, Scalar(0x58d187a4e79de0439e07729f2106946d4f31d05407cfd9da6d4e1c315b57b717))),
  (cons, Scalar(0x32f22ddfe82fafe1662c5cd6264c21037256e7e5616dd23da821426c3a2b4c62)): Cons((cons, Scalar(0x2b8d9ae786386fc5ff999ec838d001fe1b1c0e6955983b7b2d029129546cbe02)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x35f78e9534c042d03014ecd047fd4a717192675b7b3834f80531ae1050a96e15)): Cons((sym, Scalar(0x5d6c7347909bc882cddb879dc02e157a25a5b8c5a86cf35092bb4eb000d29734)), (cons, Scalar(0x6bbb0c72a545676b8a770044da938e19861c3358c7c5d6c4ba61320d67b169d2))),
  (cons, Scalar(0x379f6b6edc496da30549f6361aeb8e515701c7b3a8ce9a3b4cad581e69418550)): Cons((sym, Scalar(0x36ce160a0f23ca6d7fd20cfab35c914dd4f4e518b0d7d7039793009c1a0e7021)), (cons, Scalar(0x6bbb0c72a545676b8a770044da938e19861c3358c7c5d6c4ba61320d67b169d2))),
  (cons, Scalar(0x3a27b4c46cfcdafde2300a839175580b26c3b66457df2345bf5c3e3feb921fdf)): Cons((sym, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3)), (cons, Scalar(0x63dd6f342f1b5a46f75d13c69058b06e50b80d51cacd05d7b4f68288c8206dcf))),
  (cons, Scalar(0x3a7981615296edc8b2e91270394b8d40b88e2570bf28cc6a095503529d0653b2)): Cons((sym, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3)), (cons, Scalar(0x32f22ddfe82fafe1662c5cd6264c21037256e7e5616dd23da821426c3a2b4c62))),
  (cons, Scalar(0x3c9dba12750a5cbb3ee67cd0486546234c0616ffaed3cda722e320f19ef01f52)): Cons((sym, Scalar(0x27c4fe61970f7f0fd6f2989a1ee60ee2dd1d92d9acfcb16c731e521efbf7ca33)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x3f2bea2d24213c6899861e3605380253ace6eec2a903b93c3f71132b388888ac)): Cons((sym, Scalar(0x69807c7b2c7b867b224bb30fef5b56e956fa3a58173a0d1ff1dce5c44c08e340)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x428280cc53b2f6ec83a350136c099e9455ab7469fbb140f590ce83e645d84c82)): Cons((sym, Scalar(0x637607c0b1756ce43df6749d361305441389cbf97959342eb9b881d6f878e619)), (cons, Scalar(0x093ed78c967d5ceb43240a881c87ea8b02876a253b3521c15d73afae7c392b1b))),
  (cons, Scalar(0x4665729a5ee5bda68178ef917eb0f72aa4478e9f42ea6a066dd4a53d9a2925bf)): Cons((cons, Scalar(0x3a27b4c46cfcdafde2300a839175580b26c3b66457df2345bf5c3e3feb921fdf)), (cons, Scalar(0x59c6b57224c20911789cc51c33ca2f6d7eaf11163d9ae6bfedabc5e5a1af4bef))),
  (cons, Scalar(0x514b67aabcc2ff1f4a9f43e8bd61ff8726aa3602c690c252b19086e095b37604)): Cons((cons, Scalar(0x653ffa86714ed18569293c631415bccddf9b79304fd5866c08ce9002c28906d0)), (cons, Scalar(0x1fdf558e039ec31be1c1904059fb08af9073d8e9adb04a876b7f6474bcd696bf))),
  (cons, Scalar(0x557e7b6e08b333e6d61c23694277037771d47552de64435ba28a89720e355fe5)): Cons((sym, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3)), (cons, Scalar(0x1ef2dbcdae49b5987bab5c0b1b4c3d8ee56fb340c2f50d04c71567e702a5712f))),
  (cons, Scalar(0x563e7bd6ea783fbe2a11cf45bc2a5c8bfb9d4736993e86ba2319732b61335353)): Cons((cons, Scalar(0x5ac94ec852751d576e2e72e0f6675030a3aa870b853467bee83a73e16b923a07)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x5664640efd5d952e69958e0702ccd6ad8d08452cb31f2b0e0349dce3677d2732)): Cons((cons, Scalar(0x3f2bea2d24213c6899861e3605380253ace6eec2a903b93c3f71132b388888ac)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x56cfe0d95f7abd105dc5e0a386995c7a4ef0d428d2b7b1a984b4d8ad99339ec9)): Cons((sym, Scalar(0x04619ac0bd15a9afdbbcd89c8c8e18ebd2cde0cb36324e593d9f0647a06c9e31)), (cons, Scalar(0x63dd6f342f1b5a46f75d13c69058b06e50b80d51cacd05d7b4f68288c8206dcf))),
  (cons, Scalar(0x58d187a4e79de0439e07729f2106946d4f31d05407cfd9da6d4e1c315b57b717)): Cons((num, 1), (cons, Scalar(0x14947d3b8cc6ba04608b46ded46ea8b133c5e9e7df5ef0ade71c49eedaa3294f))),
  (cons, Scalar(0x59c6b57224c20911789cc51c33ca2f6d7eaf11163d9ae6bfedabc5e5a1af4bef)): Cons((cons, Scalar(0x129a12c8b716f5b794457e762c551cb196307207a8985919c0255b985782579c)), (cons, Scalar(0x2816e143451f879c5e5bc27684d5808136a3a8f5f2c43179410b60f201156a28))),
  (cons, Scalar(0x5a0ef771530059cc359a9733ce808a416c8e19ebb6cb30786473dd7fbc07512d)): Cons((sym, Scalar(0x65b3657600c366c323d6024c3fc30d8d44fe8e1c78e931c021b754506e9de2eb)), (cons, Scalar(0x62dcaa22523bfe9909cb4a409ca66aa2e35ddd5b3f93710c0dca95778077045c))),
  (cons, Scalar(0x5a83f9d4670a63c6204d5b51644c555dde136cefc000b59b09c3554178d51cfb)): Cons((cons, Scalar(0x1193389f4e388b95b6e89a7cd8d7277c94ede7285d5e5632c28bf68acd5674a1)), (cons, Scalar(0x5a0ef771530059cc359a9733ce808a416c8e19ebb6cb30786473dd7fbc07512d))),
  (cons, Scalar(0x5ac94ec852751d576e2e72e0f6675030a3aa870b853467bee83a73e16b923a07)): Cons((sym, Scalar(0x3bf92e0030968a97dd68fde7dc9533714d623deab221bb35646eaf9c79afc521)), (cons, Scalar(0x642ec4bee490b5050c481a4b730d083f7d49d91c673cca7e49bd74cf128b8f6a))),
  (cons, Scalar(0x5b28a422e6d9c6c2e74e5940881b0eed373cc9cf70a8569a0c704300a925b89d)): Cons((sym, Scalar(0x08e85121eee08ea965a5b97128f991f33a0020fc2061305474854ce4790fd61f)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x5ee78001bd68e9ad7ca725e3822af38077da730bd61345f7a3079beb4b8d2d34)): Cons((sym, Scalar(0x3da4f3c376db6e3211960c1b64d748812fd21081366ae5723dac07ff156b1ae0)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x60f8bde368605836ec2f3b6236ba82802618b757966983bd1a3a2b7a58255877)): Cons((sym, Scalar(0x1081a608b20bed1a08eec31d56a1a7a8fa111c417a939a5248c2cfeb99569715)), (cons, Scalar(0x25a937f0d1cd897a36637741d9b38673eaaf17c0c9eb1da64cdc07c3791b5817))),
  (cons, Scalar(0x62dcaa22523bfe9909cb4a409ca66aa2e35ddd5b3f93710c0dca95778077045c)): Cons((num, 4), (cons, Scalar(0x14947d3b8cc6ba04608b46ded46ea8b133c5e9e7df5ef0ade71c49eedaa3294f))),
  (cons, Scalar(0x63dd6f342f1b5a46f75d13c69058b06e50b80d51cacd05d7b4f68288c8206dcf)): Cons((nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x642ec4bee490b5050c481a4b730d083f7d49d91c673cca7e49bd74cf128b8f6a)): Cons((cons, Scalar(0x24e9b1c7d25353eae520b0ca7b8dc9a94b90c1a75b23a561e2dd57db6b2cb35c)), (nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc))),
  (cons, Scalar(0x653ffa86714ed18569293c631415bccddf9b79304fd5866c08ce9002c28906d0)): Cons((sym, Scalar(0x408223c41b5ffcf7d1d5cc75c499f635f3555cdd835685bdcc9d5cb45bf2d40d)), (cons, Scalar(0x24d55339300aa0cd736b6ce04fed8a457f032df17b9642d77c13fde79fd3a076))),
  (cons, Scalar(0x6570de9248c6d1c479e17b8ea743ee4cda581bbb99ef69d5d9876871e1195f61)): Cons((nil, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc)), (cons, Scalar(0x0c92e52d617c3adff9d9df08c91ec4f20b6759460fa8fbbd9da7ed4aa633804d))),
  (cons, Scalar(0x6bbb0c72a545676b8a770044da938e19861c3358c7c5d6c4ba61320d67b169d2)): Cons((sym, Scalar(0x3da4f3c376db6e3211960c1b64d748812fd21081366ae5723dac07ff156b1ae0)), (cons, Scalar(0x5b28a422e6d9c6c2e74e5940881b0eed373cc9cf70a8569a0c704300a925b89d))),
  (cons, Scalar(0x6d947a19abcd3ae22e59d7066620a9a0f2106b79a95b2fbda8ab53dfd57cb775)): Cons((sym, Scalar(0x36ce160a0f23ca6d7fd20cfab35c914dd4f4e518b0d7d7039793009c1a0e7021)), (cons, Scalar(0x58d187a4e79de0439e07729f2106946d4f31d05407cfd9da6d4e1c315b57b717))),
  (sym, Scalar(0x04619ac0bd15a9afdbbcd89c8c8e18ebd2cde0cb36324e593d9f0647a06c9e31)): Sym((str, Scalar(0x04619ac0bd15a9afdbbcd89c8c8e18ebd2cde0cb36324e593d9f0647a06c9e31))),
  (sym, Scalar(0x08e85121eee08ea965a5b97128f991f33a0020fc2061305474854ce4790fd61f)): Sym((str, Scalar(0x08e85121eee08ea965a5b97128f991f33a0020fc2061305474854ce4790fd61f))),
  (sym, Scalar(0x1081a608b20bed1a08eec31d56a1a7a8fa111c417a939a5248c2cfeb99569715)): Sym((str, Scalar(0x1081a608b20bed1a08eec31d56a1a7a8fa111c417a939a5248c2cfeb99569715))),
  (sym, Scalar(0x27c4fe61970f7f0fd6f2989a1ee60ee2dd1d92d9acfcb16c731e521efbf7ca33)): Sym((str, Scalar(0x27c4fe61970f7f0fd6f2989a1ee60ee2dd1d92d9acfcb16c731e521efbf7ca33))),
  (sym, Scalar(0x36ce160a0f23ca6d7fd20cfab35c914dd4f4e518b0d7d7039793009c1a0e7021)): Sym((str, Scalar(0x36ce160a0f23ca6d7fd20cfab35c914dd4f4e518b0d7d7039793009c1a0e7021))),
  (sym, Scalar(0x3b4805e52d6de38cbf960ef7f15538029834695a4c1abdda38dc9a870220bf84)): Sym((str, Scalar(0x3b4805e52d6de38cbf960ef7f15538029834695a4c1abdda38dc9a870220bf84))),
  (sym, Scalar(0x3bf92e0030968a97dd68fde7dc9533714d623deab221bb35646eaf9c79afc521)): Sym((str, Scalar(0x3bf92e0030968a97dd68fde7dc9533714d623deab221bb35646eaf9c79afc521))),
  (sym, Scalar(0x3da4f3c376db6e3211960c1b64d748812fd21081366ae5723dac07ff156b1ae0)): Sym((str, Scalar(0x3da4f3c376db6e3211960c1b64d748812fd21081366ae5723dac07ff156b1ae0))),
  (sym, Scalar(0x408223c41b5ffcf7d1d5cc75c499f635f3555cdd835685bdcc9d5cb45bf2d40d)): Sym((str, Scalar(0x408223c41b5ffcf7d1d5cc75c499f635f3555cdd835685bdcc9d5cb45bf2d40d))),
  (sym, Scalar(0x41b4124313d59394046b0fa3c088d77322d25c50d05d47ba8747fd0834d16aa2)): Sym((str, Scalar(0x41b4124313d59394046b0fa3c088d77322d25c50d05d47ba8747fd0834d16aa2))),
  (sym, Scalar(0x44539d9a8d172ff4b6baedf6095780746d7da97f4f47b16ef613b4f0e0683f1d)): Sym((str, Scalar(0x44539d9a8d172ff4b6baedf6095780746d7da97f4f47b16ef613b4f0e0683f1d))),
  (sym, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3)): Sym((str, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3))),
  (sym, Scalar(0x5d6c7347909bc882cddb879dc02e157a25a5b8c5a86cf35092bb4eb000d29734)): Sym((str, Scalar(0x5d6c7347909bc882cddb879dc02e157a25a5b8c5a86cf35092bb4eb000d29734))),
  (sym, Scalar(0x637607c0b1756ce43df6749d361305441389cbf97959342eb9b881d6f878e619)): Sym((str, Scalar(0x637607c0b1756ce43df6749d361305441389cbf97959342eb9b881d6f878e619))),
  (sym, Scalar(0x65b3657600c366c323d6024c3fc30d8d44fe8e1c78e931c021b754506e9de2eb)): Sym((str, Scalar(0x65b3657600c366c323d6024c3fc30d8d44fe8e1c78e931c021b754506e9de2eb))),
  (sym, Scalar(0x69807c7b2c7b867b224bb30fef5b56e956fa3a58173a0d1ff1dce5c44c08e340)): Sym((str, Scalar(0x69807c7b2c7b867b224bb30fef5b56e956fa3a58173a0d1ff1dce5c44c08e340))),
  (sym, Scalar(0x6e9554403114c390be3c9ef295b3e19a31b028d8d86b0ad8a5bb93e321cddab0)): Sym((str, Scalar(0x6e9554403114c390be3c9ef295b3e19a31b028d8d86b0ad8a5bb93e321cddab0))),
  (sym, Scalar(0x6ff1114edbb2a68a987f6c2bdf61210f46dbfcf3fe38c408f0bbbdbcf16490c4)): Sym((str, Scalar(0x6ff1114edbb2a68a987f6c2bdf61210f46dbfcf3fe38c408f0bbbdbcf16490c4))),
  (str, Scalar(0x00215ab865d362fc068509f9005dbe9315f4753975939ee9dc0d382c45a192ea)): Cons((char, 'N'), (str, Scalar(0x0d3289168dd5f209a732c60dd0967412481786203d5d401c6b4e5919091c9ce3))),
  (str, Scalar(0x0165eadd75517052068570cea96d69d7bf90d59743dba54abf2d2a6cf73b805a)): Cons((char, 'O'), (str, Scalar(0x50c1f8604198a8832b77b3842b79259929d7f221023340f2d39f0c4954bd51d2))),
  (str, Scalar(0x04619ac0bd15a9afdbbcd89c8c8e18ebd2cde0cb36324e593d9f0647a06c9e31)): Cons((char, 'N'), (str, Scalar(0x3994534dabc7dd7f40ba675f4076747d9c3138ce25d12831a9ebdea166d5ab47))),
  (str, Scalar(0x0751d4726e918aa193cc9b691702cc3630e0beb7725dac2bc0ed1f5409ab6e89)): Cons((char, 'N'), (empty, Scalar(0))),
  (str, Scalar(0x0822e3541deb54ee96e2eff6d0a15f837229c43ad9963f9aaeab33ba61546423)): Cons((char, 'O'), (str, Scalar(0x3551dde02bac773dc82370b16d08a9d91b5e9818798197d31bbb22985e59678f))),
  (str, Scalar(0x08e85121eee08ea965a5b97128f991f33a0020fc2061305474854ce4790fd61f)): Cons((char, 'Y'), (empty, Scalar(0))),
  (str, Scalar(0x0d3289168dd5f209a732c60dd0967412481786203d5d401c6b4e5919091c9ce3)): Cons((char, 'T'), (str, Scalar(0x17830fa1ff639f6ab6c31485095db68f605de110f95ecc4fefbd2a6668738650))),
  (str, Scalar(0x1081a608b20bed1a08eec31d56a1a7a8fa111c417a939a5248c2cfeb99569715)): Cons((char, 'L'), (str, Scalar(0x709089848f5ab3b8b74adc7f0b6d93f63325cff37564f76da380b2a1afbeb0b1))),
  (str, Scalar(0x16bbab1389f84638cc6f93f7ffda7facc3cdb9e31dece67eed6a029b18552e8a)): Cons((char, 'M'), (str, Scalar(0x5534e32254fe2386ccf445c447812b153de93b1c63a1bb626fbec8f5231e598b))),
  (str, Scalar(0x17830fa1ff639f6ab6c31485095db68f605de110f95ecc4fefbd2a6668738650)): Cons((char, '-'), (str, Scalar(0x51ab6d10cd80fafd5b686fe532625bb18eca6251a1380270147a14601d33a2f6))),
  (str, Scalar(0x1a90b922ef23807591c85cbe13aad72e549cc323b1ffb9cbdcc6455be587b6dc)): Cons((char, 'N'), (str, Scalar(0x5e4f6ef99ba3439e086a9b0c0e7724817d168f80dccb76be4ee4e293f3e57a6a))),
  (str, Scalar(0x1cef59108a83c3e2048ec5049aed22e2cf8cf6ba1052f9d34e693f95f8fab8bb)): Cons((char, 'E'), (empty, Scalar(0))),
  (str, Scalar(0x1f7f3fb2067fcabd8a25351c565a3efb767b607a71a2f0f7915a1173b9dac79a)): Cons((char, '2'), (empty, Scalar(0))),
  (str, Scalar(0x24a94e6ce1f93e9312759da7ea60cf4f183e45e593a0c344d5fa2cda33108431)): Cons((char, 'U'), (str, Scalar(0x0165eadd75517052068570cea96d69d7bf90d59743dba54abf2d2a6cf73b805a))),
  (str, Scalar(0x27c4fe61970f7f0fd6f2989a1ee60ee2dd1d92d9acfcb16c731e521efbf7ca33)): Cons((char, 'F'), (empty, Scalar(0))),
  (str, Scalar(0x2b001e42c3d5bba650bd41938cd77192bcdd840106237f7c2e95029fe57cf4cc)): Cons((char, 'I'), (str, Scalar(0x0751d4726e918aa193cc9b691702cc3630e0beb7725dac2bc0ed1f5409ab6e89))),
  (str, Scalar(0x2cadb76d53badab62dd9f7e72bc90c9aac9cfdc64d0f1ecd3f39d2e6edb141b4)): Cons((char, 'T'), (str, Scalar(0x3a06abf6a4d28c4e27397e4d465fbcec866959a180fc0aa110ca8d9d23a6d9c0))),
  (str, Scalar(0x2cd815475b5a8153d9c6d7de1488d1f063861a8ad168dbcd98e8becc0dbe73a5)): Cons((char, 'S'), (empty, Scalar(0))),
  (str, Scalar(0x2ee38a087b81427d20486cf6da22f4c6edb841f782f7f6a4a8f7e88a5db4f410)): Cons((char, '3'), (empty, Scalar(0))),
  (str, Scalar(0x2eef597304e70f6014ab716d9beceb1b8e07aa3cd223017c29dbcbd36503d595)): Cons((char, 'U'), (str, Scalar(0x47a21c067315309c72623c63736bc3eda5d1ab7dee341d794f9f91aabde22e8e))),
  (str, Scalar(0x3551dde02bac773dc82370b16d08a9d91b5e9818798197d31bbb22985e59678f)): Cons((char, 'N'), (str, Scalar(0x2cd815475b5a8153d9c6d7de1488d1f063861a8ad168dbcd98e8becc0dbe73a5))),
  (str, Scalar(0x36ce160a0f23ca6d7fd20cfab35c914dd4f4e518b0d7d7039793009c1a0e7021)): Cons((char, '+'), (empty, Scalar(0))),
  (str, Scalar(0x3994534dabc7dd7f40ba675f4076747d9c3138ce25d12831a9ebdea166d5ab47)): Cons((char, '1'), (empty, Scalar(0))),
  (str, Scalar(0x3a06abf6a4d28c4e27397e4d465fbcec866959a180fc0aa110ca8d9d23a6d9c0)): Cons((char, 'R'), (str, Scalar(0x65b3657600c366c323d6024c3fc30d8d44fe8e1c78e931c021b754506e9de2eb))),
  (str, Scalar(0x3b4805e52d6de38cbf960ef7f15538029834695a4c1abdda38dc9a870220bf84)): Cons((char, 'A'), (empty, Scalar(0))),
  (str, Scalar(0x3bf92e0030968a97dd68fde7dc9533714d623deab221bb35646eaf9c79afc521)): Cons((char, 'N'), (str, Scalar(0x2ee38a087b81427d20486cf6da22f4c6edb841f782f7f6a4a8f7e88a5db4f410))),
  (str, Scalar(0x3da4f3c376db6e3211960c1b64d748812fd21081366ae5723dac07ff156b1ae0)): Cons((char, 'X'), (empty, Scalar(0))),
  (str, Scalar(0x408223c41b5ffcf7d1d5cc75c499f635f3555cdd835685bdcc9d5cb45bf2d40d)): Cons((char, 'S'), (str, Scalar(0x2cadb76d53badab62dd9f7e72bc90c9aac9cfdc64d0f1ecd3f39d2e6edb141b4))),
  (str, Scalar(0x419d7930ea2448a3c5ed723e6c710683d76875a57080d771835e598eaddb6c51)): Cons((char, 'V'), (empty, Scalar(0))),
  (str, Scalar(0x41b4124313d59394046b0fa3c088d77322d25c50d05d47ba8747fd0834d16aa2)): Cons((char, 'B'), (str, Scalar(0x6451419f28996289e27c3d95e8d226ed024fd6410e3560ebf744d64498784440))),
  (str, Scalar(0x44539d9a8d172ff4b6baedf6095780746d7da97f4f47b16ef613b4f0e0683f1d)): Cons((char, 'N'), (str, Scalar(0x1f7f3fb2067fcabd8a25351c565a3efb767b607a71a2f0f7915a1173b9dac79a))),
  (str, Scalar(0x45d3669fd8b47931f519c58b072a156bbc4cea7f23116eb8640739111f18cef3)): Cons((char, 'Q'), (str, Scalar(0x24a94e6ce1f93e9312759da7ea60cf4f183e45e593a0c344d5fa2cda33108431))),
  (str, Scalar(0x47a21c067315309c72623c63736bc3eda5d1ab7dee341d794f9f91aabde22e8e)): Cons((char, 'R'), (str, Scalar(0x550ab1c3b94fb260963eb2be34d0ce63eecc69e4a38adcd4a88a9d15dbb9d5d4))),
  (str, Scalar(0x4a22f3f83e2e434fedb5944a0b55bd17d970b18a72560d04ba92cfb9838865ad)): Cons((char, 'D'), (str, Scalar(0x3b4805e52d6de38cbf960ef7f15538029834695a4c1abdda38dc9a870220bf84))),
  (str, Scalar(0x4d703718ec511b278ac868ff4d20ef2dfc580e1933aadcdf739b5c743066642a)): Cons((char, 'E'), (str, Scalar(0x00215ab865d362fc068509f9005dbe9315f4753975939ee9dc0d382c45a192ea))),
  (str, Scalar(0x4fc3e7f26da6a9810a7fa5547a705b15b16404042f7b2b79398bed9217fb8a5b)): Cons((char, 'E'), (str, Scalar(0x6ff1114edbb2a68a987f6c2bdf61210f46dbfcf3fe38c408f0bbbdbcf16490c4))),
  (str, Scalar(0x50c1f8604198a8832b77b3842b79259929d7f221023340f2d39f0c4954bd51d2)): Cons((char, 'T'), (str, Scalar(0x1cef59108a83c3e2048ec5049aed22e2cf8cf6ba1052f9d34e693f95f8fab8bb))),
  (str, Scalar(0x518a54fa4b8496f67e6e52e93ae008bad153aaadbfb6a3196eeb74519284ef69)): Cons((char, 'G'), (str, Scalar(0x2b001e42c3d5bba650bd41938cd77192bcdd840106237f7c2e95029fe57cf4cc))),
  (str, Scalar(0x51ab6d10cd80fafd5b686fe532625bb18eca6251a1380270147a14601d33a2f6)): Cons((char, 'E'), (str, Scalar(0x5ecc166457b78db597f676d7809f004dd1bce4962c17b9b08a34c53579556a14))),
  (str, Scalar(0x550ab1c3b94fb260963eb2be34d0ce63eecc69e4a38adcd4a88a9d15dbb9d5d4)): Cons((char, 'R'), (str, Scalar(0x4d703718ec511b278ac868ff4d20ef2dfc580e1933aadcdf739b5c743066642a))),
  (str, Scalar(0x5534e32254fe2386ccf445c447812b153de93b1c63a1bb626fbec8f5231e598b)): Cons((char, 'B'), (str, Scalar(0x4a22f3f83e2e434fedb5944a0b55bd17d970b18a72560d04ba92cfb9838865ad))),
  (str, Scalar(0x5d6c7347909bc882cddb879dc02e157a25a5b8c5a86cf35092bb4eb000d29734)): Cons((char, 'G'), (empty, Scalar(0))),
  (str, Scalar(0x5e4f6ef99ba3439e086a9b0c0e7724817d168f80dccb76be4ee4e293f3e57a6a)): Cons((char, 'I'), (str, Scalar(0x6a03e2259afdcbb55eb05cbfd375df351b31ad06611ce27ba492b7f999456068))),
  (str, Scalar(0x5ecc166457b78db597f676d7809f004dd1bce4962c17b9b08a34c53579556a14)): Cons((char, 'N'), (str, Scalar(0x419d7930ea2448a3c5ed723e6c710683d76875a57080d771835e598eaddb6c51))),
  (str, Scalar(0x637607c0b1756ce43df6749d361305441389cbf97959342eb9b881d6f878e619)): Cons((char, 'L'), (str, Scalar(0x4fc3e7f26da6a9810a7fa5547a705b15b16404042f7b2b79398bed9217fb8a5b))),
  (str, Scalar(0x6451419f28996289e27c3d95e8d226ed024fd6410e3560ebf744d64498784440)): Cons((char, 'E'), (str, Scalar(0x518a54fa4b8496f67e6e52e93ae008bad153aaadbfb6a3196eeb74519284ef69))),
  (str, Scalar(0x65b3657600c366c323d6024c3fc30d8d44fe8e1c78e931c021b754506e9de2eb)): Cons((char, 'C'), (str, Scalar(0x0822e3541deb54ee96e2eff6d0a15f837229c43ad9963f9aaeab33ba61546423))),
  (str, Scalar(0x69807c7b2c7b867b224bb30fef5b56e956fa3a58173a0d1ff1dce5c44c08e340)): Cons((char, 'C'), (str, Scalar(0x2eef597304e70f6014ab716d9beceb1b8e07aa3cd223017c29dbcbd36503d595))),
  (str, Scalar(0x6a03e2259afdcbb55eb05cbfd375df351b31ad06611ce27ba492b7f999456068)): Cons((char, 'L'), (empty, Scalar(0))),
  (str, Scalar(0x6e9554403114c390be3c9ef295b3e19a31b028d8d86b0ad8a5bb93e321cddab0)): Cons((char, 'B'), (empty, Scalar(0))),
  (str, Scalar(0x6ff1114edbb2a68a987f6c2bdf61210f46dbfcf3fe38c408f0bbbdbcf16490c4)): Cons((char, 'T'), (empty, Scalar(0))),
  (str, Scalar(0x709089848f5ab3b8b74adc7f0b6d93f63325cff37564f76da380b2a1afbeb0b1)): Cons((char, 'A'), (str, Scalar(0x16bbab1389f84638cc6f93f7ffda7facc3cdb9e31dece67eed6a029b18552e8a)))
}]

open LSpec in
def main := lspecIO $
  test "Hashing and storing works correctly" (ast.encode.2 == expectedStore)
