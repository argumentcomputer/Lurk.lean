import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[default_target]
lean_exe lurk {
  root := `Main
}

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "44fac19cebc3cb11e61526e824913a7ed842d435"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "2b914196a8c67838e63c1c1e44eaf339b8a50eb7"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "02e423d02d2ba1b76bed3cf6459a5c2d7a13afb8"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "e9238a79b3bef1be1bc1e99f26acc189bec12542"

lean_exe Tests.Parsing
lean_exe Tests.Evaluation
lean_exe Tests.Encoding
lean_exe Tests.Decoding
