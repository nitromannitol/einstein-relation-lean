import Lake
open Lake DSL

package «EinsteinRelation» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

-- De Giorgi–Nash–Moser theory, Lean v4.26 backport with the d = 2 branch.
require DeGiorgi from git
  "https://github.com/nitromannitol/DeGiorgi" @ "31fc3240a6af8a506c2c6e9b540b091525d5c451"

@[default_target]
lean_lib EinsteinRelation where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib EinsteinRelationAudit where
  globs := #[.submodules `EinsteinRelationAudit]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
