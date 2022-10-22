import LSpec
import Lurk.Syntax.DSL
import Lurk.Syntax.Printing
import Lurk.Hashing.StoreDSL
import Lurk.Hashing.Hashing

open Lurk Hashing Syntax

def lambda1 := ⟦(lambda (x) x)⟧

open DSL in def lambda1Store := [store| scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)):
    Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)):
    Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)),
      (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x260d89d830ea48cdc7314a9f9c1181381cabdd1db21002d3b929219553382c17)):
    Cons((cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)),
      (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  (cons, Scalar(0x19a091e5857edb8313fbfbb79694df57e2861b41738c02fb9ae31915aca7cac5)):
    Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)),
      (cons, Scalar(0x260d89d830ea48cdc7314a9f9c1181381cabdd1db21002d3b929219553382c17))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)):
    Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)):
    Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)):
    StrNil,
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)):
    StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)):
    StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)):
    StrCons((char, 'A'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)):
    StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)):
    StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)):
    StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)):
    StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)):
    StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe))),
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)):
    StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)):
    StrCons((char, 'D'), (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
}]


def tuples : List (Expr × ScalarStore) := [
  (lambda1, lambda1Store)
]

open LSpec in
def main := do
  lspecIO $ tuples.foldl (init := .done)
    fun tSeq (tuple : Expr × ScalarStore) => match tuple with
      | (expr, s) => tSeq ++ test s!"Stores {expr.pprint true false} correctly"
        (expr.hash.1 == s)
