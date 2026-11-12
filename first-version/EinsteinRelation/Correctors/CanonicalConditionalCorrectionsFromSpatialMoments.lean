import EinsteinRelation.Correctors.ConditionalMollifierDerivativeSpatialMoment
import EinsteinRelation.Correctors.EuclideanLpCoordinates

/-! # Common-field corrections from joint spatial moments

Source: `paper/main.tex:921–925,942–947`. Ordinary joint source moments
control both literal derivative corrections. These estimates retain the
Euclidean norm and require no moment bound at every spatial point.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

private theorem observation_le_borel {d : ℕ} (r : ℝ) :
    reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < r} ≤
      borel (FieldPair d) := by
  rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
  exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < r} =>
    ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le

private theorem eLpNorm_euclidean_rowsum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} {p : ℝ≥0∞} {B : ℝ} (hp : 1 ≤ p) (_hB : 0 ≤ B)
    (T : Fin d → Fin d → Ω → ℝ) (hTm : ∀ j k, Measurable (T j k))
    (hTb : ∀ j k, eLpNorm (T j k) p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => euclideanNorm (fun j => ∑ k, T j k ω)) p μ ≤
      ENNReal.ofReal (((d : ℝ) * d) * B) := by
  classical
  have hFm : Measurable (fun ω j => ∑ k, T j k ω) :=
    measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun k _ => hTm j k
  have hrow (j : Fin d) : eLpNorm (fun ω => ∑ k, T j k ω) p μ ≤
      ∑ k, eLpNorm (T j k) p μ := by
    have heq : (fun ω => ∑ k, T j k ω) = ∑ k, T j k := by
      funext ω
      simp only [Finset.sum_apply]
    rw [heq]
    exact eLpNorm_sum_le (μ := μ) (f := T j) (s := Finset.univ)
      (fun k _ => (hTm j k).aestronglyMeasurable) hp
  simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
  rw [eLpNorm_norm]
  calc
    _ ≤ ∑ j : Fin d, eLpNorm (fun ω => ∑ k, T j k ω) p μ :=
      eLpNorm_toLp_le_sum_coordinates hp _ hFm
    _ ≤ ∑ j : Fin d, ∑ k : Fin d, eLpNorm (T j k) p μ :=
      Finset.sum_le_sum fun j _ => hrow j
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, ENNReal.ofReal B :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hTb j k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d)]
      congr 1
      ring

/-- Joint scalar source moments give the actual Euclidean scalar derivative
correction bound. Source: `paper/main.tex:942–947`. -/
theorem canonicalConditionalMollifierFields_scalarCorrection_of_spatial_moments (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R C : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (_hR : 0 < R) {p : ℝ≥0∞} (_hp : 1 ≤ p) (_hpt : p ≠ ∞)
      (_hC : 0 ≤ C) (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
      (_hum : StronglyMeasurable (Function.uncurry u))
      (_hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
      (_hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
        ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)))
      (_hb : eLpNorm (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
        ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ≤ ENNReal.ofReal C),
      MemLp (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω)) p
          (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω)) p
          (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (W * C * R⁻¹) := by
  obtain ⟨W, hW, hbound⟩ := eLpNorm_conditional_mollifier_derivative_le_spatial_moment d
  refine ⟨((d : ℝ) + 1) * W, by positivity, ?_⟩
  intro L r₀ R C Q i hR p hp hpt hC u S hum hSm hu hb
  let f := canonicalConditionalMollifierFields Q i R u S
  have hFm : Measurable f.scalarCorrection :=
    (measurable_canonicalConditionalMollifierFields Q i hR u S hum hSm).2.2.2.1.mono
      (observation_le_borel (33 * R)) le_rfl
  have hj (j : Fin d) : eLpNorm (fun ω => f.scalarCorrection ω j) p
      (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (W * R⁻¹ * C) := by
    have h := (hbound Q hR hp hpt u hum hu j).trans
      (mul_le_mul_right hb (ENNReal.ofReal (W * R⁻¹)))
    simpa only [← ENNReal.ofReal_mul (by positivity : 0 ≤ W * R⁻¹)] using h
  have hn : eLpNorm (fun ω => euclideanNorm (f.scalarCorrection ω)) p
      (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal ((((d : ℝ) + 1) * W) * C * R⁻¹) := by
    simp_rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rw [eLpNorm_norm]
    calc
      _ ≤ ∑ j : Fin d, eLpNorm (fun ω => f.scalarCorrection ω j) p
          (reducedEnvironmentLaw Q) := eLpNorm_toLp_le_sum_coordinates hp _ hFm
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal (W * R⁻¹ * C) := Finset.sum_le_sum fun j _ => hj j
      _ = ENNReal.ofReal ((d : ℝ) * (W * R⁻¹ * C)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hW.le (inv_nonneg.mpr hR.le)])
  exact ⟨⟨(Entropy.continuous_euclideanNorm'.measurable.comp hFm).aestronglyMeasurable,
    hn.trans_lt ENNReal.ofReal_lt_top⟩, hn⟩

/-- Joint skew-entry moments give the actual Euclidean skew derivative
correction bound. Source: `paper/main.tex:942–947`. -/
theorem canonicalConditionalMollifierFields_skewCorrection_of_spatial_moments (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R C : ℝ} (Q : EnvironmentLaw d L r₀)
      (i : Fin d) (_hR : 0 < R) {p : ℝ≥0∞} (_hp : 1 ≤ p) (_hpt : p ≠ ∞)
      (_hC : 0 ≤ C) (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
      (_hum : StronglyMeasurable (Function.uncurry u))
      (_hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
      (_hS : ∀ j k, MemLp (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k) p
        ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)))
      (_hb : ∀ j k, eLpNorm (fun z : FieldPair d × Vec d => S z.1 (-z.2) j k) p
        ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) ≤ ENNReal.ofReal C),
      MemLp (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω)) p
          (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω)) p
          (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (W * C * R⁻¹) := by
  classical
  obtain ⟨W, hW, hbound⟩ := eLpNorm_conditional_mollifier_derivative_le_spatial_moment d
  refine ⟨(((d : ℝ) * d) + 1) * W, by positivity, ?_⟩
  intro L r₀ R C Q i hR p hp hpt hC u S hum hSm hS hb
  let m := reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R}
  letI : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  let A (j k : Fin d) (ω : FieldPair d) (y : Vec d) : ℝ :=
    conditionalSpatialAverage m (reducedEnvironmentLaw Q) (fun a z => S a z j k)
      (translate y ω) (-y) * coordinateDerivative k (Calculus.unitMassScaledMollifier d R) (-y)
  let T (j k : Fin d) (ω : FieldPair d) : ℝ := ∫ y, A j k ω y
  let f := canonicalConditionalMollifierFields Q i R u S
  have hsections : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ j k : Fin d, Integrable (A j k ω) volume :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      ae_integrable_conditional_mollifier_derivative Q hR hp hpt
        (fun ω x => S ω x j k) (hSm j k) (hS j k) k
  have hsum : f.skewCorrection =ᵐ[reducedEnvironmentLaw Q] (fun ω j => ∑ k, T j k ω) := by
    filter_upwards [hsections] with ω hω
    funext j
    change (∫ y, ∑ k : Fin d, A j k ω y) = ∑ k, ∫ y, A j k ω y
    exact integral_finset_sum _ (fun k _ => hω j k)
  have hTm (j k : Fin d) : Measurable (T j k) := by
    have hid : @Measurable (FieldPair d × Vec d) (FieldPair d × Vec d)
        ((borel (FieldPair d)).prod inferInstance) (m.prod inferInstance) id :=
      ((measurable_id'' (observation_le_borel (32 * R))).comp measurable_fst).prodMk measurable_snd
    have hc := (stronglyMeasurable_conditionalSpatialAverage m (reducedEnvironmentLaw Q)
      (fun a z => S a z j k) (hSm j k)).comp_measurable hid
    have hmove : Measurable (fun z : FieldPair d × Vec d => (translate z.2 z.1, -z.2)) :=
      (Probability.continuous_translate.measurable.comp measurable_swap).prodMk measurable_snd.neg
    have hm : StronglyMeasurable (fun z : FieldPair d × Vec d => A j k z.1 z.2) :=
      (hc.comp_measurable hmove).mul
        (((Entropy.continuous_coordinateDerivative_unitMassScaledMollifier R k).measurable.comp
          measurable_snd.neg).stronglyMeasurable)
    exact hm.integral_prod_right'.measurable
  have hTbound (j k : Fin d) : eLpNorm (T j k) p (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (W * R⁻¹ * C) := by
    have h := (hbound Q hR hp hpt (fun ω x => S ω x j k) (hSm j k) (hS j k) k).trans
      (mul_le_mul_right (hb j k) (ENNReal.ofReal (W * R⁻¹)))
    simpa only [← ENNReal.ofReal_mul (by positivity : 0 ≤ W * R⁻¹)] using h
  have hn : eLpNorm (fun ω => euclideanNorm (f.skewCorrection ω)) p
      (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal (((((d : ℝ) * d) + 1) * W) * C * R⁻¹) := by
    rw [eLpNorm_congr_ae (hsum.mono fun _ h => congrArg euclideanNorm h)]
    apply (eLpNorm_euclidean_rowsum_le (reducedEnvironmentLaw Q) hp
      (by positivity : 0 ≤ W * R⁻¹ * C) T hTm hTbound).trans
    apply ENNReal.ofReal_le_ofReal
    have ht : 0 ≤ W * R⁻¹ * C := by positivity
    nlinarith only [ht]
  have hKm : Measurable f.skewCorrection :=
    (measurable_canonicalConditionalMollifierFields Q i hR u S hum hSm).2.2.2.2.mono
      (observation_le_borel (33 * R)) le_rfl
  exact ⟨⟨(Entropy.continuous_euclideanNorm'.measurable.comp hKm).aestronglyMeasurable,
    hn.trans_lt ENNReal.ofReal_lt_top⟩, hn⟩

end EinsteinRelation.Correctors
