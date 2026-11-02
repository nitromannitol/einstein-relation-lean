import EinsteinFull.Blueprint.Roots.Proofs.D4SharpExampleRoot
import EinsteinFull.External.AKMWhiteNoiseExistence

/-!
# The root `sharp.example` (Proposition 7.1)

The root from its single graph dependency `sharp.example#positive-coefficient`. The white-noise
witness of the construction (`paper/main.tex:1528–1529`) is the admitted input
`EinsteinFull.External.akm_white_noise_exists` (Armstrong–Kuusi–Mourrat, Proposition 5.14).
-/

namespace EinsteinFull.Blueprint

/-- `sharp.example` from `sharp.example#positive-coefficient`. -/
theorem node_sharp_u2E_example_of_deps
    (hpos : node_sharp_u2E_example_u23_positive_u2D_coefficientStmt) :
    node_sharp_u2E_exampleStmt :=
  node_sharp_u2E_example_of_deps_of_whiteNoise EinsteinFull.External.akm_white_noise_exists hpos

end EinsteinFull.Blueprint
