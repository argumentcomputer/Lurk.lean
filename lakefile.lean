import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[default_target]
lean_exe lurk {
  root := `Main
}

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "dcfee71e6753c9239ab922d6fdcca0c1999c2ae4"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "adaa6c339d116c5fb67d924f0952c63603f2859b"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "a2cd91c2def98d73326fbe280a773ed8ebf9c3ae"

require std from git
  "https://github.com/leanprover/std4/" @ "d83e97c7843deb1cf4a6b2a2c72aaf2ece0b4ce8"

lean_exe Tests.Parsing
lean_exe Tests.Evaluation
lean_exe Tests.Encoding
lean_exe Tests.Decoding
lean_exe Tests.SerDe
