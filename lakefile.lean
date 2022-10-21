import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[defaultTarget]
lean_exe lurk {
  root := `Main
}

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "e5b3e06ed3a98cf67a70ce2e2a0f757153f19419"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "cbf5cd7c098c4369d93b9b8399a323bf0a28c107"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "a8dc2f38fc38f16efcc877ca8a4c7b37d3965db0"

lean_exe Tests.Evaluation
lean_exe Tests.Hashing
