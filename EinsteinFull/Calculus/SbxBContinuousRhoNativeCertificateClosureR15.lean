import EinsteinFull.Calculus.SbxBActualSpectrumSelectionR14
import EinsteinFull.Calculus.SbxBContinuousDensityNativeDeltaClosureR15

open EinsteinRelation EinsteinFull.External.Source.GMP

namespace EinsteinFull

/-- A continuous uniformly elliptic density admits an actual Dirichlet
spectrum and a common gradient for its native fundamental solution. -/
theorem b_continuous_rho_native_certificate_of_ellipticity_r15
    {d : ℕ} (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (hρ : Continuous ρ) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R (bNativeSpectralKernelR13 s) G := by
  obtain ⟨s, _, G, _, _, _, _, _, hcert⟩ :=
    b_actual_spectrum_selection_r14 hd hκ hR hell
  exact ⟨s, G, hcert (b_native_initial_delta_of_continuous_density_r15
    hd hκ hR hell hρ s)⟩

#print axioms b_continuous_rho_native_certificate_of_ellipticity_r15

end EinsteinFull
