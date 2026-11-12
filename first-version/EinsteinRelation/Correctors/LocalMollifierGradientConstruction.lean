import EinsteinRelation.Correctors.LocalConditionalGradientConstruction
import EinsteinRelation.Correctors.LocalMollifierSpatialTest

/-! # One local conditional-gradient average for every moment

Source: `paper/main.tex:968–973`. The actual mollifier and one joint version
of the canonical conditional gradient are fixed before the moment exponent.
Every conditional-tail bound then controls this same local average.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- The reflected source mollifier has mass one on its actual center domain.
Source: `paper/main.tex:921–938,968–973`. -/
theorem integral_center_mollifier_eq_one {d : ℕ} {R : ℝ} (hR : 0 < R) :
    (∫ y : {y : Vec d // euclideanNorm y ≤ R},
      Calculus.unitMassScaledMollifier d R (-y.1)) = 1 := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  calc
    _ = ∫ y in {y : Vec d | euclideanNorm y ≤ R},
        Calculus.unitMassScaledMollifier d R (-y) :=
      integral_subtype hS (fun y => Calculus.unitMassScaledMollifier d R (-y))
    _ = 1 := by
      have heq : (∫ y in {y : Vec d | euclideanNorm y ≤ R},
          Calculus.unitMassScaledMollifier d R (-y)) =
          ∫ y, Calculus.unitMassScaledMollifier d R (-y) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        by_contra hn
        have hb := Entropy.euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hR hn
        have he : euclideanNorm (-y) = euclideanNorm y := by
          simp only [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_neg, norm_neg]
        exact hy (by simpa only [Set.mem_setOf_eq, he] using hb.le)
      rw [heq]
      simpa only [zero_sub] using integral_translated_unitMassScaledMollifier hR (0 : Vec d)

/-- Construct one coefficient-local average of the production canonical
corrector gradient, valid simultaneously for every supplied finite-moment
conditional-tail estimate. Source: `paper/main.tex:968–973`. -/
theorem exists_local_canonical_mollifier_gradient_average {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 1 ≤ R) :
    let f : FieldPair d → Vec d := fun ω =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) ω).ofLp
    ∃ V : FieldPair d → Vec d,
      Measurable[reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}] V ∧
      ∀ (p A : ℝ), 1 ≤ p → 0 ≤ A →
        eLpNorm (fun ω => euclideanNorm (f ω - (reducedEnvironmentLaw Q)[f |
          reducedCoefficientObservationSigma {z | euclideanNorm (z - 0) < 8 * R}] ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A →
        MemLp (fun ω => euclideanNorm (V ω - f ω))
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => euclideanNorm (V ω - f ω))
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * A) := by
  let f : FieldPair d → Vec d := fun ω =>
    ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) ω).ofLp
  let J := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  have hfm : Measurable f :=
    J.continuous.measurable.comp (Lp.stronglyMeasurable _).measurable
  have hfi : Integrable f (reducedEnvironmentLaw Q) :=
    J.toContinuousLinearMap.integrable_comp ((Lp.memLp _).integrable (by norm_num))
  obtain ⟨u, hu, huv⟩ := exists_joint_center_conditioned_vector_orbit (R := R) Q hfm hfi
  let w : {y : Vec d // euclideanNorm y ≤ R} → ℝ :=
    fun y => Calculus.unitMassScaledMollifier d R (-y.1)
  have hwm : Measurable w :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp
      measurable_subtype_coe.neg
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  have hc : Continuous (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.comp continuous_neg
  have hcs : HasCompactSupport (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.hasCompactSupport_unitMassScaledMollifier (zero_lt_one.trans_le hR)).comp_homeomorph
      (Homeomorph.neg _)
  have hwi : Integrable w volume :=
    (integrableOn_iff_comap_subtypeVal hS).mp
      (hc.integrable_of_hasCompactSupport hcs).integrableOn
  have hfin : volume {y : Vec d | euclideanNorm y ≤ R} < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (show {y : Vec d | euclideanNorm y ≤ R} ⊆
      Metric.closedBall (0 : Vec d) R from ?_)) (isCompact_closedBall _ _).measure_lt_top
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Entropy.norm_le_euclideanNorm'' y).trans hy
  letI : IsFiniteMeasure (volume : Measure {y : Vec d // euclideanNorm y ≤ R}) :=
    ⟨(Measure.Subtype.volume_univ hS.nullMeasurableSet).trans_lt hfin⟩
  have hw0 : ∀ y, 0 ≤ w y :=
    fun y => Entropy.unitMassScaledMollifier_nonneg' (zero_lt_one.trans_le hR) _
  have hw : (∫ y, w y ∂volume) = 1 :=
    integral_center_mollifier_eq_one (zero_lt_one.trans_le hR)
  have hobs : reducedCoefficientObservationSigma {z : Vec d | euclideanNorm z < 33 * R} ≤
      borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {z : Vec d | euclideanNorm z < 33 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hua : Measurable u :=
    hu.comp (measurable_fst.prodMk (measurable_snd.mono le_rfl hobs))
  have hlocal : Measurable[reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm z < 33 * R}]
      (fun ω => ∫ y, w y • u (y, ω) ∂volume) := by
    letI : MeasurableSpace (FieldPair d) :=
      reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}
    have hm := (hwm.comp measurable_snd).smul (hu.comp measurable_swap)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨fun ω => ∫ y, w y • u (y, ω) ∂volume, hlocal, ?_⟩
  intro p A hp hA htail
  have hb := local_center_conditioned_euclidean_gradient_bound hR volume hp hA
    w hwm hwi hw0 hw f hfi hfm htail u hua huv
  exact hb.2

end EinsteinRelation.Correctors
