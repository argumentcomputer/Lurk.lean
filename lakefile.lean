import Lake
open Lake DSL

package Lurk where
  precompileModules := true

lean_lib Lurk

@[default_target]
lean_exe lurk where
  root := `Main

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "995807a3ee648851ab7e43e5e35de37fb11856ba"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "818538aced05fe563ef95bb3dcdf5ed755896139"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "129fd4ba76d5cb9abf271dc29208a28f45fd981e"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "4b02c12e70a88b2ecf735899f85fe18d296fac90"

require std from git
  "https://github.com/leanprover/std4/" @ "2919713bde15d55e3ea3625a03546531283bcb54"

lean_exe Tests.Decoding
lean_exe Tests.Encoding
lean_exe Tests.Evaluation
lean_exe Tests.Parsing
lean_exe Tests.SerDe
