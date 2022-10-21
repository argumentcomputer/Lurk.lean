import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.Scalar

def got := ⟦
  (letrec (
    (exp (lambda (base exponent)
           (if (= 0 exponent)
               1
               (* base (exp base (- exponent 1))))))
    (exp2 (lambda (base exponent)
            (if (= 0 exponent)
                1
                (* base (exp2 base (- exponent 1))))))
    (exp3 (lambda (base exponent)
            (if (= 0 exponent)
                1
                (* base (exp3 base (- exponent 1)))))))
    (+ (+ (exp 3 2) (exp2 2 3))
        (exp3 4 2)))⟧.hash.1

open Lurk.Hashing

def expected : Std.RBMap ScalarPtr ScalarExpr compare := .ofList [
  (⟨Tag.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩,
    .sym ⟨Tag.str, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.cons, .ofNat 0x372a4b6d9926eedaacdf900162e971d451503abe5d3f55ae0af995dce3bb8002⟩, .cons
    ⟨.sym, .ofNat 0x36f5e2cba528eb9dc684d288dccad8288006162a58b1e73cbeef5c008eef2d8c⟩
    ⟨.cons, .ofNat 0x5fb55a24ea19996865f8bc0eb0e34ad31a3d7dc9ace65f95ff19972c80fc84fb⟩),

  (⟨Tag.cons, .ofNat 0x70e549c0ff526f7956888ca64eae920a3a739e43c7346c8f752dbf1587728406⟩, .cons
    ⟨.cons, .ofNat 0x0894bb6769277cc462bbe53d342a023af312a10f729e1de0a591cbf5a5d8584a⟩
    ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.cons, .ofNat 0x3d0314cd0d483ff7687c97535c42b0af10b4e05340b3e4d82968a1e18a9dea09⟩, .cons
    ⟨.cons, .ofNat 0x04e9ceaa93fecf230cbb8195ec7010726c6dffe970a9234f218a8ab10c62749f⟩
    ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.cons, .ofNat 0x47d0739ef47e6604f7eb1286122403f244d65a99203bcd9fb47ba510c3208c18⟩, .cons
    ⟨.sym, .ofNat 0x6857f71a633308380336278f5fada99d934358a40432c77d19346735dbdff5d0⟩
    ⟨.cons, .ofNat 0x1801855261e4f89983dc87ad485b64df23d3bf53031ead1ae7e65b2939b4bfca⟩),

  (⟨Tag.cons, .ofNat 0x66b06a2ce9063b31894e7ae3d445b16b4b7eaa0129cde9b265f6f51138891319⟩, .cons
    ⟨.num, .ofNat 2⟩
    ⟨.cons, .ofNat 0x3fd6586eb0fe1ce80046357d8eaacd6a8263f989babe0d88f7296ebe8d0d7c4e⟩),

  (⟨Tag.cons, .ofNat 0x4340e6947bfc0bf5af2005ea6a3f76e28ad2a01e027f93fa7c28931c5c85ce1d⟩, .cons
    ⟨.cons, .ofNat 0x333267139c4df16b2b905e84793851d4b232da6093d6e3d660168d4c1f43b4d3⟩
    ⟨.cons, .ofNat 0x5a00ed88dd2e17e47e3656e1dcb71bfc2d9a2f8e5902e366efe8507a753d553f⟩),

  (⟨Tag.cons, .ofNat 0x0f32fb9cf280f58e2e007999bbb05c5bc4aa76e0047df97032dcb74c194a3d1e⟩, .cons
    ⟨.sym, .ofNat 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩
    ⟨.cons, .ofNat 0x4340e6947bfc0bf5af2005ea6a3f76e28ad2a01e027f93fa7c28931c5c85ce1d⟩),

  (⟨Tag.cons, .ofNat 0x3b56fd33ebbe79722beebacbd2ebd88a14dd9ff1d0819e716b56359413821f1f⟩, .cons
    ⟨.cons, .ofNat 0x47d0739ef47e6604f7eb1286122403f244d65a99203bcd9fb47ba510c3208c18⟩
    ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.cons, .ofNat 0x102d1c235a0eb283800aa5ae7d98d5c33a7b90e58e58ada9c205b4905c91511f⟩, .cons
    ⟨.sym, .ofNat 0x36f5e2cba528eb9dc684d288dccad8288006162a58b1e73cbeef5c008eef2d8c⟩
    ⟨.cons, .ofNat 0x2b37c81d4d872356b656e85069b6e3c538c361fc87eff2d07263267947a8db5e⟩),

  (⟨Tag.cons, .ofNat 0x15261efad9d95873e9680f6006a2e499bca9b91e69e71e9fcafdb47af21c2022⟩, .cons
    ⟨.sym, .ofNat 0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617⟩
    ⟨.cons, .ofNat 0x22cfde08b4c90b702d21f34f1c4c452caa04aa95dec72e5cdcfd495711fdcd55⟩),

  (⟨Tag.cons, .ofNat 0x0ef4376f4c5606d1de7476b8efad02976608e5d6c63402bf1897ec280b0a4b23⟩, .cons
    ⟨.sym, .ofNat 0x2e0d5c3ecec046111f37d82e3454d792399b9236b05fc45ef441dae03714c021⟩
    ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.cons, .ofNat 0x34c2268b43ecfd6dcb1ab454e5211185e62170a40f1bd80d01d0317d1e91dc24⟩, .cons
    ⟨.sym, .ofNat 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩
    ⟨.cons, .ofNat 0x5ca3a18af5b041c9098ce9bc0331569954f18938c2dac5979bfaf570244c356a⟩),

  (⟨Tag.cons, .ofNat 0x03d4694d9fc4a529ced28106ca3d85f3fdcbe5aaa706d8a039f80b193c252e25⟩, .cons
    ⟨.cons, .ofNat 0x61efce90ee70dee8d3e9c2eb24a8ac4bb5018fcc021d564fa8402e6d919e4fe4⟩
    ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.cons, .ofNat 0x0d3f9307e8ebbc14dc7c890e7c4e4123277995db8f2409e578ad061925bafa2c⟩, .cons
    ⟨.cons, .ofNat 0x6288a3eb4d50b4dbfdbdff12c36165426b785f0be3e5c12de9f062b1b10f5459⟩
    ⟨.cons, .ofNat 0x1d3989426b9da495721dcc979d162d9406a55acd33bfb338856924ba057234ba⟩),

  (⟨Tag.cons, .ofNat 0x4bfb01738fddeea5757a778e9fccd465a09dcea77d59c701fcc2162816ac9f35⟩, .cons
    ⟨.sym, .ofNat 0x23302b7a6dd05d071225916ac1e4f663a6879bf45f7a90cf58a6443156443aa1⟩
    ⟨.cons, .ofNat 0x66b06a2ce9063b31894e7ae3d445b16b4b7eaa0129cde9b265f6f51138891319⟩),

  (⟨Tag.cons, .ofNat 0x5a00ed88dd2e17e47e3656e1dcb71bfc2d9a2f8e5902e366efe8507a753d553f⟩, .cons
    ⟨.cons, .ofNat 0x372a4b6d9926eedaacdf900162e971d451503abe5d3f55ae0af995dce3bb8002⟩
    ⟨.nil, .ofNat 0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2⟩),

  (⟨Tag.sym, .ofNat 0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617⟩, .sym
    ⟨.str,   .ofNat 0x0ff050c891a70d4c6885c671f39a3cb377b8b3a7f514a92539204c40e582b617⟩),

  (⟨Tag.sym, .ofNat 0x2e0d5c3ecec046111f37d82e3454d792399b9236b05fc45ef441dae03714c021⟩, .sym
    ⟨.str,   .ofNat 0x2e0d5c3ecec046111f37d82e3454d792399b9236b05fc45ef441dae03714c021⟩),

  (⟨Tag.sym, .ofNat 0x5191bdbc4e614fe12c53816f4867a1f30e72971a255140a000386cd5a7527131⟩, .sym
    ⟨.str,   .ofNat 0x5191bdbc4e614fe12c53816f4867a1f30e72971a255140a000386cd5a7527131⟩),

  (⟨Tag.sym, .ofNat 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩, .sym
    ⟨.str,   .ofNat 0x486533910b416f4c0ee301179aae3c7ba5b55f9fac42e07ff7b1719862147839⟩),

  (⟨Tag.sym, .ofNat 0x63f54baca36ac31205e11d1bcd336891c40ae48b9a29b3683a7eb9f430fd4a4b⟩, .sym
    ⟨.str,   .ofNat 0x63f54baca36ac31205e11d1bcd336891c40ae48b9a29b3683a7eb9f430fd4a4b⟩),

  (⟨Tag.sym, .ofNat 0x5b99c690e9124338f91704cc89d273e470462ba12d8b436f5798387b1dacbe58⟩, .sym
    ⟨.str,   .ofNat 0x5b99c690e9124338f91704cc89d273e470462ba12d8b436f5798387b1dacbe58⟩),

  (⟨Tag.sym, .ofNat 0x5980aacfb34baea4c8464d3cc5f417446265e10f8e102be3b7c356b078a3f061⟩, .sym
    ⟨.str,   .ofNat 0x5980aacfb34baea4c8464d3cc5f417446265e10f8e102be3b7c356b078a3f061⟩),

  (⟨Tag.sym, .ofNat 0x36f5e2cba528eb9dc684d288dccad8288006162a58b1e73cbeef5c008eef2d8c⟩, .sym
    ⟨.str,   .ofNat 0x36f5e2cba528eb9dc684d288dccad8288006162a58b1e73cbeef5c008eef2d8c⟩),

  (⟨Tag.sym, .ofNat 0x23302b7a6dd05d071225916ac1e4f663a6879bf45f7a90cf58a6443156443aa1⟩, .sym
    ⟨.str,   .ofNat 0x23302b7a6dd05d071225916ac1e4f663a6879bf45f7a90cf58a6443156443aa1⟩),

  (⟨Tag.sym, .ofNat 0x6857f71a633308380336278f5fada99d934358a40432c77d19346735dbdff5d0⟩, .sym
    ⟨.str,   .ofNat 0x6857f71a633308380336278f5fada99d934358a40432c77d19346735dbdff5d0⟩),

  (⟨Tag.sym, .ofNat 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩, .sym
    ⟨.str,   .ofNat 0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc⟩),

  (⟨Tag.sym, .ofNat 0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa⟩, .sym
    ⟨.str,   .ofNat 0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa⟩),

  (⟨Tag.num, .ofNat 0⟩, .num (.ofNat 0)),
  (⟨Tag.num, .ofNat 1⟩, .num (.ofNat 1)),
  (⟨Tag.num, .ofNat 2⟩, .num (.ofNat 2)),
  (⟨Tag.num, .ofNat 3⟩, .num (.ofNat 3)),
  (⟨Tag.num, .ofNat 4⟩, .num (.ofNat 4))
]

open LSpec in
def main := do
  let tSeq := test "Stores have the same size" (got.exprs.size == expected.size)
  lspecIO $ expected.fold (init := tSeq) fun tSeq ptr expectedExpr =>
    withOptionSome s!"{ptr} is found" (got.exprs.find? ptr) fun gotExpr =>
      tSeq ++ test s!"Expected ({expectedExpr}) equals resulting expression ({gotExpr})"
        (expectedExpr == gotExpr)
