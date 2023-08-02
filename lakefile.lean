import Lake
open Lake DSL

package «sol-2-11» {
  -- add package configuration options here
}

lean_lib «Sol211» {
  -- add library configuration options here
}

@[default_target]
lean_exe «sol-2-11» {
  root := `Main
}
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"