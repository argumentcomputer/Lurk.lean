import Lake
open Lake DSL

package Lurk where
  precompileModules := true

lean_lib Lurk

@[default_target]
lean_exe lurk where
  root := `Main

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "6ed4420a3c81d3ff9006e73a685498d8e0967cd0"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "515b7eff7765dcf55ce275ac41fa13a30a59f1d0"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "dde7324b17e5f7b67ad0eb591906b57b1a9401a4"

require std from git
  "https://github.com/leanprover/std4/" @ "2919713bde15d55e3ea3625a03546531283bcb54"

lean_exe Tests.Decoding
lean_exe Tests.Encoding
lean_exe Tests.Evaluation
lean_exe Tests.Parsing
lean_exe Tests.SerDe
