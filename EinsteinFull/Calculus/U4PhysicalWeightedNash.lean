import EinsteinFull.Calculus.C8FoundationGMPAssociation
import Ch1Statements.Nash

open MeasureTheory
open scoped ENNReal
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

noncomputable section
namespace EinsteinFull

/-- At zero force the source graph measure is Lebesgue measure. -/
theorem u4_sourceReducedMeasure_zero {d : ℕ} (hd : 2 ≤ d) :
    densityWeightedMeasure (sourceReducedDensity hd 0) = (volume : Measure (Vec d)) := by
  simp [densityWeightedMeasure, sourceReducedDensity, sourceForceWeight]

/-- The actual unforced physical measure and volume are uniformly comparable. -/
theorem u4_unforced_physical_measure_comparable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω) :
    physicalReversibleMeasure ω hd 0 ≤ ENNReal.ofReal (Real.exp (2 * Λ)) • volume ∧
    (volume : Measure (Vec d)) ≤ ENNReal.ofReal (Real.exp (2 * Λ)) •
      physicalReversibleMeasure ω hd 0 := by
  have hm : densityWeightedMeasure (sourcePhysicalDensity ω hd 0) =
      physicalReversibleMeasure ω hd 0 := by
    simp [densityWeightedMeasure, sourcePhysicalDensity, sourceForceWeight,
      physicalReversibleMeasure, physicalReversibleDensity, physicalForceWeight]
  constructor
  · simpa only [hm, u4_sourceReducedMeasure_zero] using
      sourcePhysicalMeasure_le_reduced ω hd 0 Λ hω
  · simpa only [hm, u4_sourceReducedMeasure_zero] using
      sourceReducedMeasure_le_physical ω hd 0 Λ hω

/-- Ellipticity controls the physical graph gradient with the actual half-energy. -/
theorem u4_physical_graph_energy_lower {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0)) :
    ((1 / 2 : ℝ) * Λ⁻¹) *
        (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
      ∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0 := by
  have hi := u.gradient_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hf := physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω u u
  have hp : ∀ x, ((1 / 2 : ℝ) * Λ⁻¹) * ‖u.weakGradient x‖ ^ 2 ≤
      weightedFormIntegrand ω.1 u u x := by
    intro x
    have he := (hω.1 x).2 (WithLp.ofLp (u.weakGradient x))
    have hn : euclideanSq (WithLp.ofLp (u.weakGradient x)) = ‖u.weakGradient x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]
    unfold weightedFormIntegrand
    calc
      ((1 / 2 : ℝ) * Λ⁻¹) * ‖u.weakGradient x‖ ^ 2 =
          (1 / 2 : ℝ) * (Λ⁻¹ * euclideanSq (WithLp.ofLp (u.weakGradient x))) := by
        rw [hn]
        ring
      _ ≤ (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
          ((ω.1 x).mulVec (WithLp.ofLp (u.weakGradient x))) :=
        mul_le_mul_of_nonneg_left he.1 (by norm_num)
  have hm := integral_mono_ae (hi.const_mul ((1 / 2 : ℝ) * Λ⁻¹)) hf
    (Filter.Eventually.of_forall hp)
  rw [integral_const_mul] at hm
  exact hm

/-- Spatial gradient mass is controlled by the literal physical gradient mass. -/
theorem u4_unforced_physical_graph_gradient_comparison {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0)) :
    (∫ x, ‖u.weakGradient x‖ ^ 2) ≤
      Real.exp (2 * Λ) *
        (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd 0) := by
  exact integral_le_const_mul_of_measure_le volume (physicalReversibleMeasure ω hd 0)
    (Real.exp (2 * Λ)) (Real.exp_pos _).le
    (u4_unforced_physical_measure_comparable hd ω Λ hω).2
    (fun x => ‖u.weakGradient x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg _) 
    (u.gradient_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0))

/-- The spatial gradient is bounded by the anisotropic physical form. -/
theorem u4_unforced_physical_graph_spatial_gradient_le_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd 0)) :
    (∫ x, ‖u.weakGradient x‖ ^ 2) ≤
      (Real.exp (2 * Λ) * (2 * Λ)) *
        (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have h := u4_physical_graph_energy_lower hd ω Λ hΛ hω u
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * Λ by positivity)
  have hgrad : (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
      (2 * Λ) * (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0) := by
    have heq : (2 * Λ) * ((1 / 2 : ℝ) * Λ⁻¹) = 1 := by
      field_simp
    simpa only [← mul_assoc, heq, one_mul] using h'
  calc
    _ ≤ Real.exp (2 * Λ) *
        (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd 0) :=
      u4_unforced_physical_graph_gradient_comparison hd ω Λ hω u
    _ ≤ Real.exp (2 * Λ) * ((2 * Λ) *
        (∫ x, weightedFormIntegrand ω.1 u u x ∂physicalReversibleMeasure ω hd 0)) :=
      mul_le_mul_of_nonneg_left hgrad (Real.exp_pos _).le
    _ = _ := by ring

/-- Physical L¹ control transfers to Lebesgue measure. -/
theorem u4_unforced_physical_integral_abs_comparison {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : Integrable f (physicalReversibleMeasure ω hd 0)) :
    Integrable f volume ∧
      (∫ x, |f x|) ≤ Real.exp (2 * Λ) *
        (∫ x, |f x| ∂physicalReversibleMeasure ω hd 0) := by
  have hv : Integrable f volume := memLp_one_iff_integrable.mp <|
    (memLp_one_iff_integrable.mpr hf).of_measure_le_smul
      (c := ENNReal.ofReal (Real.exp (2 * Λ))) ENNReal.ofReal_ne_top
      (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  refine ⟨hv, ?_⟩
  apply integral_le_const_mul_of_measure_le volume (physicalReversibleMeasure ω hd 0)
    (Real.exp (2 * Λ)) (Real.exp_pos _).le
    (u4_unforced_physical_measure_comparable hd ω Λ hω).2
    (fun x => |f x|) (Filter.Eventually.of_forall fun x => abs_nonneg _)
  simpa only [Real.norm_eq_abs] using hf.norm

end EinsteinFull
