import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinRelation.Clock.CentredClockField
import EinsteinFull.Blueprint.G4.node_finite_u2D_time_u2D_analyticity
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints
import EinsteinFull.Calculus.ComplexHighExponentSupport
import EinsteinFull.Calculus.ComplexEndpointAnalyticSupport

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Adapted from W3 finiteXi_drift_norm_bound; the unfinished gradient-limit
module is deliberately not imported. Only its elementary proved bound is used. -/
private theorem finiteTime_drift_norm_bound {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (j : Fin d) :
    ‖β j‖ ≤ (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity := by
  letI := reducedLaw_probability Q
  have hD := D.one_le_ellipticity
  have hB : 0 ≤ (1 / 2 : ℝ) * d *
      reducedLipschitzConstant D.ellipticity := by
    unfold reducedLipschitzConstant
    positivity
  have hb := Lp.norm_le_of_ae_bound (f := β j) hB (by
    filter_upwards [hβ.ae_eq_cdiv j, ae_abs_cdiv_le_reduced Q j] with ω hω hbound
    rw [hω]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num :
      (0 : ℝ) < 1 / 2)]
    nlinarith only [hbound])
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] using hb


private theorem observation_norm_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    (K : ℝ) (hK : 0 ≤ K) (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
    ‖f‖ ≤ K := by
  letI := reducedLaw_probability Q
  have h := Lp.norm_le_of_ae_bound (f := f) hK hf
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] using h

private theorem bilinear_norm_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f g : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ ω, f ω * g ω ∂reducedLaw Q‖ ≤ ‖f‖ * ‖g‖ := by
  rw [← inner_complexL2Conjugation_eq_integral_mul]
  exact (norm_inner_le_norm _ _).trans_eq (by rw [norm_complexL2Conjugation])

/-- Entire finite-time correlations with a structural bound on every compact
force disc and time interval, using exactly the endpoint graph dependency. -/
theorem node_finite_u2D_time_u2D_analyticity_of_deps
    (hendpoints : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt) :
    node_finite_u2D_time_u2D_analyticityStmt := by
  intro d hd D T R hT hR
  obtain ⟨C, c, hC, _hc, he⟩ := hendpoints d hd D 2 (by norm_num) T (R + 1) hT
    (by linarith)
  obtain ⟨A, hA, hentry⟩ := DriftH5.exists_ae_abs_entry_le d D.ellipticity D.dependenceRange
  let K := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
  let M := max (sourceReducedBound D.ellipticity) 0
  have hK : 0 ≤ K := by
    dsimp [K, reducedLipschitzConstant]
    have hD := D.one_le_ellipticity
    positivity
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨C * (K + R * A) + C * (R * M), by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ P hP
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let Pdag := fun ζ t => complexL2Transpose (reducedLaw Q) (P ζ t)
  have hdag (ζ : ℂ) : IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ) :=
    isComplexTransposeSemigroup_complexL2Transpose Q (P ζ)
  have hβnorm (j : Fin d) : ‖β j‖ ≤ K := finiteTime_drift_norm_bound D Q hQ β hβ j
  have hanorm (j k : Fin d) : ‖a j k‖ ≤ A := by
    apply observation_norm_bound Q _ A hA
    filter_upwards [ha j k, hentry Q] with ω haω hω
    rw [haω, Complex.norm_real, Real.norm_eq_abs]
    exact hω j k
  have hμnorm : ‖μ‖ ≤ M := by
    apply observation_norm_bound Q _ M hM
    filter_upwards [hμ, Clock.ae_abs_clockAtOrigin_le Q] with ω hμω hω
    rw [hμω, Complex.norm_real, Real.norm_eq_abs]
    exact hω.trans (le_max_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro t j ζ
    exact (analyticAt_velocityCorrelation hP j β a t ζ).differentiableAt
  · intro t ζ
    exact (analyticAt_clockCorrelation hP β μ t ζ).differentiableAt
  · intro t ζ ht hζ j
    obtain ⟨E, H, hE, _hhol, _hH, hbound, _hrest⟩ :=
      he Q hQ β a μ hβ ha hμ P Pdag hP hdag (.inr true) t ht
    have hEeq : complexLpToL2 (reducedLaw Q) (by norm_num) (E ζ) = Pdag ζ t (β ⟨0, by omega⟩) := by
      apply Lp.ext
      exact hE ζ
    have hb : ‖Pdag ζ t (β ⟨0, by omega⟩)‖ ≤ C := by
      rw [← hEeq]
      exact (norm_complexLpToL2_le (reducedLaw Q) (by norm_num) (E ζ)).trans
        (hbound ζ (by linarith))
    have hp (f : Lp ℂ 2 (reducedLaw Q)) :
        (∫ ω, β ⟨0, by omega⟩ ω * (P ζ t f) ω ∂reducedLaw Q) =
          ∫ ω, f ω * (Pdag ζ t (β ⟨0, by omega⟩)) ω ∂reducedLaw Q := by
      calc
        _ = ∫ ω, (P ζ t f) ω * β ⟨0, by omega⟩ ω ∂reducedLaw Q := by
          congr 1
          ext ω
          exact mul_comm _ _
        _ = _ := hdag ζ t f (β ⟨0, by omega⟩)
    have hv : ‖velocityCorrelation Q ⟨0, by omega⟩ j ζ (P ζ) β a t‖ ≤
        C * (K + R * A) := by
      rw [velocityCorrelation, hp]
      have hf : ‖β j + ζ • a ⟨0, by omega⟩ j‖ ≤ K + R * A := by
        exact (norm_add_le _ _).trans (add_le_add (hβnorm j)
          (by rw [norm_smul]; exact mul_le_mul hζ (hanorm _ _) (norm_nonneg _) hR))
      exact (bilinear_norm_bound Q _ _).trans
        ((mul_le_mul hf hb (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _))
    have hc : ‖clockCorrelation Q ⟨0, by omega⟩ ζ (P ζ) β μ t‖ ≤ C * (R * M) := by
      rw [clockCorrelation, hp]
      have hf : ‖ζ • μ‖ ≤ R * M := by
        rw [norm_smul]
        exact mul_le_mul hζ hμnorm (norm_nonneg _) hR
      exact (bilinear_norm_bound Q _ _).trans
        ((mul_le_mul hf hb (norm_nonneg _) (mul_nonneg hR hM)).trans_eq (mul_comm _ _))
    exact add_le_add hv hc

end EinsteinFull.Blueprint
