import EinsteinRelation.Correctors.CanonicalConditionalMollifierFields
import EinsteinRelation.Correctors.LocalConditionalTranslation

/-! # Moving-center identities for the chosen conditional fields

Source: `paper/main.tex:913–938,948–973`. The joint conditional versions
used in the spatial equations are the same moving-window conditional
expectations used in the moment estimates. No second choice of a local
field is needed.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- The actual mollifier center domain has finite volume.
Source: `paper/main.tex:921–938`. -/
theorem finiteMeasure_mollifierCenterDomain {d : ℕ} (R : ℝ) :
    IsFiniteMeasure (volume : Measure {y : Vec d // euclideanNorm y ≤ R}) := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  have hfin : volume {y : Vec d | euclideanNorm y ≤ R} < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (show {y : Vec d | euclideanNorm y ≤ R} ⊆
      Metric.closedBall (0 : Vec d) R from ?_)) (isCompact_closedBall _ _).measure_lt_top
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Entropy.norm_le_euclideanNorm'' y).trans hy
  exact ⟨(Measure.Subtype.volume_univ hS.nullMeasurableSet).trans_lt hfin⟩

/-- Transport the fixed-center conditional source to its actual moving
coefficient window. Source: `paper/main.tex:913–925,948–963`. -/
theorem centered_conditionalSpatialAverage_ae_eq_condExp
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (R : ℝ)
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u)) (y : Vec d)
    (hui : Integrable (fun ω => u ω (-y)) (reducedEnvironmentLaw Q)) :
    (fun ω => conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u (translate y ω) (-y)) =ᵐ[reducedEnvironmentLaw Q]
      (reducedEnvironmentLaw Q)[fun ω => u (translate y ω) (-y) |
        reducedCoefficientObservationSigma {x : Vec d | euclideanNorm (x - y) < 32 * R}] := by
  have hle : reducedCoefficientObservationSigma
      {x : Vec d | euclideanNorm x < 32 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < 32 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hpres : MeasurePreserving (translate y)
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
    ⟨Probability.measurable_translate y, reducedEnvironmentLaw_stationary Q y⟩
  have hv := hpres.quasiMeasurePreserving.ae_eq_comp
    (conditionalSpatialAverage_ae_eq_condExp _ _ hle u (-y) hui)
  exact hv.trans (condExp_reducedObservation_translate Q
    {x : Vec d | euclideanNorm x < 32 * R} y
    (hum.measurable.comp (measurable_id.prodMk measurable_const)) hui).symm

/-- Jointly measurable conditional versions give the same sample integrals.
No integrability premise is needed for equality of the integrals themselves.
Source: `paper/main.tex:921–938`. -/
theorem ae_integral_eq_of_forall_ae_eq
    {X Ω E : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (ν : Measure X) [SigmaFinite ν] (μ : Measure Ω) [SigmaFinite μ]
    (f g : X × Ω → E) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x, (fun ω => f (x, ω)) =ᵐ[μ] (fun ω => g (x, ω))) :
    (fun ω => ∫ x, f (x, ω) ∂ν) =ᵐ[μ] (fun ω => ∫ x, g (x, ω) ∂ν) := by
  have h := (Measure.ae_ae_comm (μ := ν) (ν := μ) (measurableSet_eq_fun hf hg)).mp
    (ae_of_all _ hfg)
  exact h.mono fun _ hω => integral_congr_ae hω

/-- Restrict a literal mollifier average to its actual center domain.
Source: `paper/main.tex:921–938`. -/
theorem mollifier_integral_eq_centerIntegral {d : ℕ} {R : ℝ}
    (hR : 0 < R) (v : Vec d → ℝ) :
    (∫ y, Calculus.unitMassScaledMollifier d R (-y) * v y) =
      ∫ y : {y : Vec d // euclideanNorm y ≤ R},
        Calculus.unitMassScaledMollifier d R (-y.1) * v y.1 := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  calc
    _ = ∫ y in {y : Vec d | euclideanNorm y ≤ R},
        Calculus.unitMassScaledMollifier d R (-y) * v y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hw : Calculus.unitMassScaledMollifier d R (-y) = 0 := by
        by_contra hn
        have hb := Entropy.euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hR hn
        have he : euclideanNorm (-y) = euclideanNorm y := by
          simp only [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_neg, norm_neg]
        exact hy (by simpa only [Set.mem_setOf_eq, he] using hb.le)
      rw [hw, zero_mul]
    _ = _ := (integral_subtype hS _).symm

/-- The transported conditional source is jointly measurable in its center
and environment. Source: `paper/main.tex:913–938`. -/
theorem measurable_centered_conditionalSpatialAverage
    {d : ℕ} {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀)
    (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u)) :
    Measurable (fun z : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d =>
      conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate z.1.1 z.2) (-z.1.1)) := by
  have hobs : reducedCoefficientObservationSigma
      {x : Vec d | euclideanNorm x < 32 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < 32 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hc := (stronglyMeasurable_conditionalSpatialAverage
    (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
    (reducedEnvironmentLaw Q) u hum).measurable
  exact hc.comp
    (((measurable_id'' hobs).comp (Probability.continuous_translate.measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))).prodMk
        (measurable_subtype_coe.comp measurable_fst).neg)

/-- Restrict one coordinate of the literal derivative correction to its
actual center domain. Source: `paper/main.tex:921–938`. -/
theorem mollifier_derivative_integral_eq_centerIntegral {d : ℕ} {R : ℝ}
    (hR : 0 < R) (v : Vec d → ℝ) (j : Fin d) :
    (∫ y, v y * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)) =
      ∫ y : {y : Vec d // euclideanNorm y ≤ R},
        v y.1 * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y.1) := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  calc
    _ = ∫ y in {y : Vec d | euclideanNorm y ≤ R},
        v y * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have he : euclideanNorm (-y) = euclideanNorm y := by
        simp only [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_neg, norm_neg]
      rw [Entropy.coordinateDerivative_unitMassScaledMollifier_eq_zero hR j
        (by rw [he]; exact not_le.mp hy), mul_zero]
    _ = _ := (integral_subtype hS _).symm

end EinsteinRelation.Correctors
