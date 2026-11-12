import EinsteinRelation.Correctors.HeatHessianUnitIntegrability
import EinsteinRelation.Correctors.HeatHessianUniformL1
import EinsteinRelation.Correctors.HeatGradientUniformLp
import EinsteinRelation.Correctors.CenteredCorrectorFluxSupport

/-! Source: `paper/main.tex:722,756`. The canonical centered flux supplies
the stationary square moments required for the heat cutoff argument. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Square-integrable stationary source coordinates give one finite
`C/t` bound before time and the three derivative indices. -/
theorem exists_stationary_heatGradient_L2_bound_of_unit {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (hF2 : ∀ i, MemLp (fun ω => F ω i) 2 Q)
    (hunit : ∀ i j : Fin d, Integrable (coordinateDerivative j
      (coordinateDerivative i (euclideanHeatKernel (d := d) 1))) volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j k l : Fin d) (t : ℝ), 0 < t → eLpNorm
      (fun ω => akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l 0)
        2 Q ≤ ENNReal.ofReal (C / t) := by
  let A : ℝ := 1 + ∑ i, (eLpNorm (fun ω => F ω i) 2 Q).toReal
  have hA : 0 < A := by
    have : 0 ≤ ∑ i, (eLpNorm (fun ω => F ω i) 2 Q).toReal :=
      Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    dsimp [A]
    linarith
  have hi (i : Fin d) : eLpNorm (fun ω => F ω i) 2 Q ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal (hF2 i).eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    have := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) =>
        ENNReal.toReal_nonneg (a := eLpNorm (fun ω => F ω j) 2 Q))
      (Finset.mem_univ i)
    dsimp [A]
    linarith
  obtain ⟨K, hK, hmass⟩ := heatKernel_mixedHessian_uniform_L1_of_unit hunit
  refine ⟨2 * K * A, by positivity, ?_⟩
  intro j k l t ht
  exact eLpNorm_heatGradientSpaceIntegral_le_div hQ F hF (by norm_num) (by norm_num)
    A K hA.le hK.le hi t ht j k l (fun i => hmass t ht i l)

/-- The Gaussian Hessian premise is discharged by its actual unit-time
integrability, leaving only the stationary source's L² membership. -/
theorem exists_stationary_heatGradient_L2_bound {d : ℕ}
    {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → Vec d) (hF : Measurable F)
    (hF2 : ∀ i, MemLp (fun ω => F ω i) 2 Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j k l : Fin d) (t : ℝ), 0 < t → eLpNorm
      (fun ω => akmHeatGradientSpaceIntegral (fun y => F (translate y ω)) t j k l 0)
        2 Q ≤ ENNReal.ofReal (C / t) :=
  exists_stationary_heatGradient_L2_bound_of_unit hQ F hF hF2
    integrable_unit_heatKernel_mixedHessian

/-- The literal canonical centered source is jointly measurable and has
square-integrable coordinates on the actual reduced environment law. -/
theorem canonical_flux_source_measurable_memLp {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp) ∧
    ∀ j, MemLp (fun ω => (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i).ofLp j)
      2 (reducedEnvironmentLaw Q) := by
  have hV : Measurable (fun ω => canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) :=
    (Lp.stronglyMeasurable (canonicalCorrectorFlux Q i)).measurable.sub measurable_const
  refine ⟨(PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp hV, ?_⟩
  intro j
  have hmem := (Lp.memLp (canonicalCorrectorFlux Q i)).sub
    (memLp_const (expectedCorrectorFlux Q i))
  apply hmem.of_le_mul (c := 1)
  · exact (((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).continuous).measurable.comp
      hV).aestronglyMeasurable
  · exact ae_of_all _ (fun ω => by
      simpa only [one_mul, Real.norm_eq_abs] using
        PiLp.norm_apply_le (canonicalCorrectorFlux Q i ω - expectedCorrectorFlux Q i) j)

end EinsteinRelation.Correctors
