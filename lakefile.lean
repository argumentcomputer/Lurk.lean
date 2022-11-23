import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[default_target]
lean_exe lurk {
  root := `Main
}

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "750e7538e2d8da4d3f78bf90e268b84c06f3d361"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "f905b68f529de2af44cf6ea63489b7e3cd090050"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "89798a6cb76b2b29469ff752af2fd8543b3a5515"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "71e7d8d10d617bca953056310168ecee5fc46015"

require std from git
  "https://github.com/leanprover/std4/" @ "d83e97c7843deb1cf4a6b2a2c72aaf2ece0b4ce8"

lean_exe Tests.Parsing
lean_exe Tests.Evaluation
lean_exe Tests.Encoding
lean_exe Tests.Decoding
lean_exe Tests.SerDe
