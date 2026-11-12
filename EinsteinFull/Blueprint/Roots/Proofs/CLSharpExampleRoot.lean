import EinsteinFull.Blueprint.Roots.Proofs.D4SharpExampleRoot
import EinsteinFull.External.AKMWhiteNoiseExistence
import EinsteinFull.WhiteNoise.Existence

/-!
# The root `sharp.example` (Proposition 7.1)

The root from its single graph dependency `sharp.example#positive-coefficient`. The white-noise
witness of the construction (`paper/main.tex:1528–1529`) is Armstrong–Kuusi–Mourrat, Proposition
5.14, proved in `EinsteinFull/WhiteNoise/Existence.lean`
(`EinsteinFull.WhiteNoise.akmWhiteNoiseExistence`).
-/

namespace EinsteinFull.Blueprint

/-- `sharp.example` from `sharp.example#positive-coefficient`. -/
theorem node_sharp_u2E_example_of_deps
    (hpos : node_sharp_u2E_example_u23_positive_u2D_coefficientStmt) :
    node_sharp_u2E_exampleStmt :=
  node_sharp_u2E_example_of_deps_of_whiteNoise EinsteinFull.WhiteNoise.akmWhiteNoiseExistence hpos

end EinsteinFull.Blueprint
