import Lake
open Lake DSL

package murphi {
  -- add package configuration options here
}

lean_lib Murphi {
  -- add library configuration options here
}

@[default_target]
lean_exe murphi {
  root := `Main
}
