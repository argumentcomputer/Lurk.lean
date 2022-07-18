import Lake
open Lake DSL

package lurk 

@[defaultTarget]
lean_exe lurk {
  root := `Main
}

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "80b290a322267aee7dbca96b2547fa24de64236a"