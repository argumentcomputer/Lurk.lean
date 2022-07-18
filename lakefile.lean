import Lake
open Lake DSL

package lurk {
  -- add package configuration options here
}

lean_lib Lurk {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe lurk {
  root := `Main
}
