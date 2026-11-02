import EinsteinFull.Calculus.SbxBTubeExactAssemblerR12
import EinsteinFull.Calculus.SbxBSpectralCompactTestInitialDeltaR14

open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

namespace EinsteinFull.Calculus

/-- Every uniformly elliptic native spectral resolution has the weighted
initial trace at every prescribed interior point. -/
theorem br15_weighted_row_initial_trace_of_ellipticity {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) : br14WeightedRowInitialTrace s :=
  br14_weighted_row_initial_trace_of_cutoff hd hκ hR hell s
    (br14_spectral_cutoff_preservation_of_exponential_defect d hd κ hκ
      (EinsteinFull.b_renewal_exponential_defect_of_ellipticity d hd κ hκ)
      hR hell s)

#print axioms br15_weighted_row_initial_trace_of_ellipticity

end EinsteinFull.Calculus
