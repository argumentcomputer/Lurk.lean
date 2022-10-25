import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[defaultTarget]
lean_exe lurk {
  root := `Main
}

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "c8996dde8d9b00ce487e53d02234efd1c2a062b2"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "11336e502174b1449f525b1e44d76f6a44fbd274"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "a8dc2f38fc38f16efcc877ca8a4c7b37d3965db0"

lean_exe Tests.Evaluation
lean_exe Tests.Hashing
