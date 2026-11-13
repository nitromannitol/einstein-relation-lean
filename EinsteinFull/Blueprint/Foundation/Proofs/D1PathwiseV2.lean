import EinsteinFull.Calculus.S4KernelSupport
import EinsteinFull.Calculus.C4TextbookFoundation

/-!
D1: the smooth-scope pathwise node.

The statement quantifies over every solution of the literal `fderiv`-flux martingale problem. The paper
assumes smooth coefficients, and the statement carries the hypothesis `HasSmoothBounds D Q`. It follows from
the admitted Bass well-posedness axiom through `foundation_textbook_well_posed`.
-/

namespace EinsteinFull.Blueprint

/-- Smooth-scope pathwise node: existence and identification of the physical and reduced laws by the inverse clock. -/
theorem node_eq_u2E_reduced_u2D_generator_u23_pathwise_of_deps :
    node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2 :=
  pathwiseV2_of_svWellPosed EinsteinFull.foundation_textbook_well_posed

end EinsteinFull.Blueprint
