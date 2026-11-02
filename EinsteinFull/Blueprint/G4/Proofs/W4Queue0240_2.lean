import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integral
import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradients
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Work.W2.UnforcedCorrelationIntegrabilitySupport

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Absolute integrability and the half-energy identity for the actual unforced
correlation. The adopted resolvent argument already supplies the prescribed
dependencies internally; their exact binders are retained for graph composition. -/
@[nolint unusedArguments]
theorem node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integral_of_deps
    (_hmassive : node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradientsStmt)
    (_hscalar : node_p_u3A_scalarStmt) :
    node_e_u3A_linear_u2D_velocity_u23_spectral_u2D_integralStmt := by
  intro d hd D Q hQ β a hβ _ha first P hP i
  simp_rw [velocityCorrelation_zero_eq]
  have hi := hβ.integrable_correlation_Ici first hP first i
  refine ⟨hi.re, ?_⟩
  calc
    _ = (∫ t in Set.Ici (0 : ℝ), ∫ ω,
        β first ω * P t.toNNReal (β i) ω ∂reducedLaw Q).re := integral_re hi
    _ = _ := by
      rw [hβ.integral_correlation_Ici_eq_corrector_energy first hP,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        ← corrector_energy_eq_inner,
        show (1 / 2 : ℂ).re = (1 / 2 : ℝ) by norm_num]
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

end EinsteinFull.Blueprint
