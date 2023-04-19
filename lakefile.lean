import Lake
open Lake DSL

package is0 {
  -- add package configuration options here
}

lean_lib Is0 {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe is0 {
  root := `Main
}
