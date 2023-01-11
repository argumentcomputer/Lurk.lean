import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[default_target]
lean_exe lurk where
  root := `Main

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "cfda9cb724febf6894af59515860b34426a970d9"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "704823e421b333ea9960347e305c60f654618422"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "2e7eb85008f8bfb9d246ae0508e167e7a0de2eb3"

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

lean_exe Tests.Decoding
lean_exe Tests.Encoding
lean_exe Tests.Evaluation
lean_exe Tests.Parsing
lean_exe Tests.SerDe
