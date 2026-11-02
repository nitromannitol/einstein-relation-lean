import EinsteinFull.Calculus.SbxBWeightedRowInitialTraceClosureR15

open EinsteinRelation EinsteinFull.External.Source.GMP

namespace EinsteinFull

/-- A continuous uniformly elliptic density gives the native spectral kernel
its initial delta at every prescribed interior point. -/
theorem b_native_initial_delta_of_continuous_density_r15 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (hρ : Continuous ρ)
    (s : DirichletSpectralResolution ρ α R) : BNativeSpectralInitialDeltaR13 s := by
  intro y hy ψ hψ
  exact Calculus.br14_native_column_initial_delta hκ hell hρ s
    (Calculus.br15_weighted_row_initial_trace_of_ellipticity hd hκ hR hell s)
    y hy ψ hψ.1.continuous hψ.2.1 hψ.2.2

#print axioms b_native_initial_delta_of_continuous_density_r15

end EinsteinFull
