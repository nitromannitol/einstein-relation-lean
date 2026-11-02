import EinsteinFull.Calculus.SbxBTubeExactAssemblerR12
import EinsteinFull.Calculus.SbxBWeightedRowInitialTraceClosureR15

open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

namespace EinsteinFull

/-- The tube probability estimate for the original renewal statement. -/
theorem b_tube_probability_r15 :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  apply b_tube_probability_of_weighted_spectral_row_initial_trace
  intro d hd κ hκ R hR ρ α hell hρ s
  exact Calculus.br15_weighted_row_initial_trace_of_ellipticity hd hκ hR hell s

#print axioms b_tube_probability_r15

end EinsteinFull
