import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[defaultTarget]
lean_exe lurk {
  root := `Main
}

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "dd565ffec739f9ee0a79a3bf47ab5e1e0db0d8e2"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "a8dc2f38fc38f16efcc877ca8a4c7b37d3965db0"

lean_exe Tests.Evaluation
