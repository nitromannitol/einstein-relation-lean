import EinsteinRelation.Correctors.LocalMollifierGradientConstruction

/-! # A literal conditional-gradient average with its joint version retained

Source: `paper/main.tex:921–938,968–973`. The same center-conditioned
canonical gradient defines the actual mollifier integral before all moment
exponents. Retaining its conditional versions and almost-sure center
integrability allows its use in the spatial weak-equation assembly.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
namespace EinsteinRelation.Correctors
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- One joint conditional version realizes the literal local gradient average
and all its moment estimates. Source: `paper/main.tex:968–973`. -/
theorem exists_local_canonical_mollifier_gradient_realization {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 1 ≤ R) :
    let f : FieldPair d → Vec d := fun ω =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) ω).ofLp
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Vec d)
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      (∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
            {z | euclideanNorm (z - y.1) < 32 * R}]) ∧
      (let V : FieldPair d → Vec d := fun ω => ∫ y,
          Calculus.unitMassScaledMollifier d R (-y.1) • u (y, ω) ∂volume
       Measurable[reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}] V ∧
      ∀ (p A : ℝ), 1 ≤ p → 0 ≤ A →
        eLpNorm (fun ω => euclideanNorm (f ω - (reducedEnvironmentLaw Q)[f |
          reducedCoefficientObservationSigma {z | euclideanNorm (z - 0) < 8 * R}] ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A →
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y =>
          Calculus.unitMassScaledMollifier d R (-y.1) • u (y, ω)) volume) ∧
        MemLp (fun ω => euclideanNorm (V ω - f ω))
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => euclideanNorm (V ω - f ω))
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * A)) := by
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
  refine ⟨u, hu, huv, hlocal, ?_⟩
  intro p A hp hA htail
  have hb := local_center_conditioned_euclidean_gradient_bound hR volume hp hA
    w hwm hwi hw0 hw f hfi hfm htail u hua huv
  exact hb

end EinsteinRelation.Correctors
