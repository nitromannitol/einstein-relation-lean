import EinsteinFull.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.Calculus.SbxBActualSpectrumSelectionR14
import EinsteinFull.Calculus.SbxBContinuousDensityNativeDeltaClosureR15
import EinsteinFull.Calculus.SbxBTubeExactAssemblerR12

open EinsteinRelation EinsteinFull.External.Source.GMP

namespace EinsteinFull

/-- The centered local return holds at every positive scale for the actual
clipped coefficients, with constants uniform in the environment and force. -/
theorem b_centered_local_return_unconditional_r15 : b_centered_local_return_input := by
  apply b_centered_local_return_of_continuous_native_primitives
  · intro d hd κ hκ R hR ρ α hell hρ
    obtain ⟨s, u, G, hs, hb, hv, hc, hz, hcert⟩ :=
      b_actual_spectrum_selection_r14 hd hκ hR hell
    exact ⟨bNativeSpectralKernelR13 s, G,
      hcert (b_native_initial_delta_of_continuous_density_r15 hd hκ hR hell hρ s)⟩
  · intro d hd κ hκ
    obtain ⟨δ, hδ, hmass⟩ := b_renewal_native_half_survival_of_ellipticity d hd κ hκ
    refine ⟨δ, hδ, ?_⟩
    intro R hR ρ α hell K G hK x r u hr hball hu hut
    exact hmass R ρ α K G hell hK x r u hr hball hu hut
  · intro d hd κ hκ
    obtain ⟨δ, H, hδ, hH, hcomp⟩ := b_renewal_native_harnack_of_ellipticity d hd κ hκ
    refine ⟨δ, H, hδ, hH, ?_⟩
    intro R hR ρ α hell K G hK x y r u hr hball hy hu hut hxy
    exact hcomp R ρ α K G hell hK x y r u hr hball hy hu hut hxy

#print axioms b_centered_local_return_unconditional_r15

end EinsteinFull
