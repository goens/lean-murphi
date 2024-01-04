import Lake
open Lake DSL

package Murphi {
  -- add package configuration options here
}

@[default_target]
lean_lib Murphi {
  -- add library configuration options here
}

lean_exe murphi {
  root := `Main
}
