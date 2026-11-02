import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.HorizontalMollifierBounds

open MeasureTheory

namespace EinsteinRelation.Correctors

noncomputable section

/-- The centered coefficient-action flux column under the actual reduced law. -/
def canonicalCenteredCorrectorFlux {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
  canonicalCorrectorFlux Q i -
    Lp.const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i)

/-- Expanding the construction gives the literal coefficient action on `eᵢ + Gᵢ`,
then subtracts its expected column, as in `paper/main.tex:698-702`. -/
theorem canonicalCenteredCorrectorFlux_eq_source_action_sub_mean
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    canonicalCenteredCorrectorFlux Q i =
      reducedOriginCoefficientAction Q
        (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) +
          (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) -
        Lp.const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i) := by
  rfl

theorem canonicalCenteredCorrectorFlux_ae {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    (fun ω => canonicalCenteredCorrectorFlux Q i ω) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) := by
  change (fun ω => (canonicalCorrectorFlux Q i -
      Lp.const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i)) ω) =ᵐ[
        reducedEnvironmentLaw Q]
      (fun ω => canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i)
  filter_upwards [Lp.coeFn_sub (canonicalCorrectorFlux Q i)
      (Lp.const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i)),
    Lp.coeFn_const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i)] with ω hsub hconst
  calc
    (canonicalCorrectorFlux Q i -
        Lp.const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i)) ω =
        canonicalCorrectorFlux Q i ω -
          (Lp.const 2 (reducedEnvironmentLaw Q) (expectedCorrectorFlux Q i)) ω := hsub
    _ = canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i := by
      congr 1

theorem canonicalCenteredCorrectorFlux_memLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    MemLp (canonicalCenteredCorrectorFlux Q i) 2 (reducedEnvironmentLaw Q) :=
  Lp.memLp (canonicalCenteredCorrectorFlux Q i)

theorem canonicalCenteredCorrectorFlux_integrable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Integrable (canonicalCenteredCorrectorFlux Q i) (reducedEnvironmentLaw Q) :=
  (canonicalCenteredCorrectorFlux_memLp Q i).integrable (by norm_num)

theorem canonicalCenteredCorrectorFlux_mean_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∫ ω, canonicalCenteredCorrectorFlux Q i ω ∂reducedEnvironmentLaw Q = 0 := by
  have hflux := canonicalCorrectorFlux_integrable Q i
  calc
    ∫ ω, canonicalCenteredCorrectorFlux Q i ω ∂reducedEnvironmentLaw Q =
        ∫ ω, (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i)
          ∂reducedEnvironmentLaw Q :=
      integral_congr_ae (canonicalCenteredCorrectorFlux_ae Q i)
    _ = 0 := by
      rw [integral_sub hflux (integrable_const _)]
      simp [expectedCorrectorFlux_eq_integral]

private theorem horizontalEuclideanGradient_integral_eq_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q)) :
    ∫ ω, horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f ω ∂reducedEnvironmentLaw Q = 0 := by
  let μ := reducedEnvironmentLaw Q
  let hμ := reducedEnvironmentLaw_stationary Q
  let D := horizontalEuclideanGradient μ hμ f
  have hDint : Integrable D μ := (Lp.memLp D).integrable (by norm_num)
  have hcoord (j : Fin d) :
      ∫ ω, (D ω : EuclideanSpace ℝ (Fin d)) j ∂μ = 0 := by
    have hmean := horizontalEuclideanGradient_mean_zero μ hμ f j
    rw [euclideanCoordinateMean, ContinuousLinearMap.comp_apply,
      EinsteinRelation.l2Expectation_apply] at hmean
    have hproj : (fun ω =>
        ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).compLpL 2 μ D) ω) =ᵐ[μ]
        (fun ω => D ω j) := by
      filter_upwards [ContinuousLinearMap.coeFn_compLpL
        (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j) D
        (p := 2) (μ := μ)] with ω hω
      simpa only [PiLp.proj_apply] using hω
    rw [integral_congr_ae hproj] at hmean
    exact hmean
  ext j
  have hprojInt := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j) hDint
  change (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j
      (∫ ω, D ω ∂μ)) = 0
  rw [← hprojInt]
  exact hcoord j

private theorem horizontalGradient_inner_const_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (f : horizontalH1 (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q))
    (c : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f)
      (Lp.const 2 (reducedEnvironmentLaw Q) c) = 0 := by
  let μ := reducedEnvironmentLaw Q
  let D := horizontalEuclideanGradient μ (reducedEnvironmentLaw_stationary Q) f
  have hDint : Integrable D μ := (Lp.memLp D).integrable (by norm_num)
  rw [L2.inner_def]
  calc
    ∫ ω, inner ℝ (D ω) ((Lp.const 2 μ c) ω) ∂μ =
        ∫ ω, inner ℝ (D ω) c ∂μ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_const 2 μ c] with ω hω
          simpa only [Function.const_apply] using congrArg (fun x => inner ℝ (D ω) x) hω
    _ = inner ℝ (∫ ω, D ω ∂μ) c := by
      calc
        ∫ ω, inner ℝ (D ω) c ∂μ = ∫ ω, inner ℝ c (D ω) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => real_inner_comm _ _
        _ = inner ℝ c (∫ ω, D ω ∂μ) := integral_inner hDint c
        _ = inner ℝ (∫ ω, D ω ∂μ) c := by rw [real_inner_comm]
    _ = 0 := by rw [horizontalEuclideanGradient_integral_eq_zero]; simp

theorem canonicalCenteredCorrectorFlux_variational_horizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q)) :
    inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f) (canonicalCenteredCorrectorFlux Q i) = 0 := by
  rw [canonicalCenteredCorrectorFlux, inner_sub_right,
    canonicalCorrectorGradient_variational_horizontalH1]
  simp only [horizontalGradient_inner_const_zero]
  ring

theorem canonicalCenteredCorrectorFlux_variational_horizontalCore {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    {F : FieldPair d → ℝ} (hF : EinsteinRelation.IsHorizontalTest F) :
    inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q)
      ⟨(hF.memLp (reducedEnvironmentLaw Q) 2).toLp F,
        hF.mem_horizontalH1 (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)⟩)
      (canonicalCenteredCorrectorFlux Q i) = 0 :=
  canonicalCenteredCorrectorFlux_variational_horizontalH1 Q i _

theorem actual_reduced_law_centered_flux_variational_H1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q)) :
    ∫ ω, inner ℝ
      (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f ω)
      (canonicalCenteredCorrectorFlux Q i ω) ∂reducedEnvironmentLaw Q = 0 := by
  rw [← L2.inner_def]
  exact canonicalCenteredCorrectorFlux_variational_horizontalH1 Q i f

theorem actual_reduced_law_centered_flux_variational_core {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    {F : FieldPair d → ℝ} (hF : EinsteinRelation.IsHorizontalTest F) :
    ∫ ω, inner ℝ
      (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q)
        ⟨(hF.memLp (reducedEnvironmentLaw Q) 2).toLp F,
          hF.mem_horizontalH1 (reducedEnvironmentLaw Q)
            (reducedEnvironmentLaw_stationary Q)⟩ ω)
      (canonicalCenteredCorrectorFlux Q i ω) ∂reducedEnvironmentLaw Q = 0 := by
  rw [← L2.inner_def]
  exact canonicalCenteredCorrectorFlux_variational_horizontalCore Q i hF

theorem actual_reduced_law_centered_flux_compact_kernel {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (ζ : Vec d → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (F : FieldPair d → ℝ) (hF : Measurable F)
    (hFb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M) :
    ∫ ω, inner ℝ
      (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q)
        ⟨((isHorizontalTest_horizontalMollify ζ hζ hζc F hF hFb).memLp
            (reducedEnvironmentLaw Q) 2).toLp (horizontalMollify ζ F),
          (isHorizontalTest_horizontalMollify ζ hζ hζc F hF hFb).mem_horizontalH1
            (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q)⟩ ω)
      (canonicalCenteredCorrectorFlux Q i ω) ∂reducedEnvironmentLaw Q = 0 :=
  actual_reduced_law_centered_flux_variational_core Q i
    (isHorizontalTest_horizontalMollify ζ hζ hζc F hF hFb)

end

end EinsteinRelation.Correctors
