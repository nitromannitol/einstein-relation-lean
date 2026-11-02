import EinsteinFull.External.Draft.GMPDirichletLowerV2

namespace EinsteinFull.External

/-- Exact source-reviewed conditional specialization of GMP Lemma 5.3.
The spectral predicate identifies the weighted Dirichlet kernel; existence
for arbitrary measurable density representatives is not asserted. Actual
killed-path identification and regeneration applications remain internal. -/
axiom gmp_dirichlet_lower : EinsteinFull.External.Draft.gmpDirichletLowerStmtV2

end EinsteinFull.External
