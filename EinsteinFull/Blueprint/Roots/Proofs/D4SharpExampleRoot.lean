import EinsteinFull.Calculus.S4SharpLawSupport
import EinsteinFull.External.Draft.AKMWhiteNoiseExistence

/-!
Root reduction for Proposition 7.1 (`sharp.example`) from its single graph dependency
`sharp.example#positive-coefficient`, given AKM white-noise existence (decision D4, 2026-10-29: source review
PASS, approved by the author). The existence input is a hypothesis here. It becomes the admitted axiom
`EinsteinFull.External.akm_white_noise_exists` after the canonical review receipt; the frozen vendor hole
`EinsteinRelation.Frozen.whiteNoiseExists` is never used.
-/

namespace EinsteinFull.Blueprint

/-- `sharp.example` from `sharp.example#positive-coefficient`, given AKM white-noise existence. -/
theorem node_sharp_u2E_example_of_deps_of_whiteNoise
    (hW : EinsteinFull.External.Draft.akmWhiteNoiseExistenceStmt)
    (hpos : node_sharp_u2E_example_u23_positive_u2D_coefficientStmt) :
    node_sharp_u2E_exampleStmt :=
  EinsteinFull.Calculus.S4.sharp_example_of_whiteNoise (fun d hd => hW d hd) hpos

end EinsteinFull.Blueprint
