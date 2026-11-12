import EinsteinRelation.Correctors.LocalMollifierCorrectionConstruction

/-! # Moment-independent local mollifier corrections

Source: `paper/main.tex:895–906,921–938,942–963`. The conditional scalar
and skew versions are chosen once, before every exponent and estimate
constant. The weights are the literal derivatives of the source mollifier.
Tail and shift estimates for the source correctors remain internal obligations.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

private theorem finite_center_volume {d : ℕ} (R : ℝ) :
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

/-- Choose one scalar conditional field and its literal mollifier correction
before every moment exponent and centered tail/shift estimate.
Source: `paper/main.tex:913–938,948–963`. -/
theorem exists_local_mollifier_scalar_correction_uniform (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (_hR : 1 ≤ R)
    (f : FieldPair d → ℝ) (_hfm : Measurable f)
    (_hf : Integrable f (reducedEnvironmentLaw Q))
    (g : Vec d × FieldPair d → ℝ) (_hgm : Measurable g)
    (_hgi : ∀ y, Integrable (fun ω => g (y, ω)) (reducedEnvironmentLaw Q)),
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) ℝ
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      (∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun ω => f ω + g (y.1, ω) |
            reducedCoefficientObservationSigma
              {z | euclideanNorm (z - y.1) < 32 * R}]) ∧
      (let H : FieldPair d → Vec d := fun ω => ∫ y,
          u (y, ω) • gradient (Calculus.unitMassScaledMollifier d R) (-y.1) ∂volume
       (@Measurable (FieldPair d) (Vec d)
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
          inferInstance H) ∧
        ∀ (p A B : ℝ), 1 ≤ p → 0 ≤ A → 0 ≤ B →
        ∀ (_hshift : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
          eLpNorm (fun ω => g (y.1, ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
            ENNReal.ofReal B)
        (_htail : eLpNorm (f - (reducedEnvironmentLaw Q)[f |
          reducedCoefficientObservationSigma {z : Vec d | euclideanNorm (z - 0) < 8 * R}])
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A),
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y =>
          u (y, ω) • gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) volume) ∧
        MemLp (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹)) := by
  obtain ⟨W, hW, hweights⟩ := exists_uniform_mollifier_derivative_weights d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q hR f hfm hf g hgm hgi
  obtain ⟨hwm, hwi, hw, hwbound⟩ := hweights R (zero_lt_one.trans_le hR)
  letI := finite_center_volume (d := d) R
  let w : {y : Vec d // euclideanNorm y ≤ R} → Vec d :=
    fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1)
  obtain ⟨u, hum, huv⟩ := exists_joint_center_conditioned_family Q
    (fun z => f z.2 + g z) ((hfm.comp measurable_snd).add hgm)
    (fun y => hf.add (hgi y))
  have hle : reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm z < 33 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {z : Vec d // euclideanNorm z < 33 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hui : @Measurable
      ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
      ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
      inferInstance
      (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})) id :=
    measurable_fst.prodMk ((measurable_id'' hle).comp measurable_snd)
  have hu : Measurable u := hum.comp hui
  refine ⟨u, hum, huv, ?_, ?_⟩
  · letI : MeasurableSpace (FieldPair d) :=
      reducedCoefficientObservationSigma {z : Vec d | euclideanNorm z < 33 * R}
    have hm : Measurable (fun z => u z • w z.1) := hum.smul (hwm.comp measurable_fst)
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  · intro p A B hp hA hB hshift htail
    have hbound := local_center_conditioned_scalar_derivative_bound hR volume hp hA hB
      (fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1))
      hwm hwi hw hwbound f hf (fun y ω => g (y.1, ω))
      (fun y => hgi y.1) hshift htail u hu huv
    exact ⟨hbound.1, hbound.2.2⟩

/-- Construct the skew conditional field and its locally measurable
literal mollifier correction before every moment exponent and tail/shift bound.
Source: `paper/main.tex:913–938,948–963`. -/
theorem exists_local_mollifier_skew_correction_uniform (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (_hR : 1 ≤ R)
    (f : Fin d → FieldPair d → Vec d)
    (_hf : ∀ k, Integrable (f k) (reducedEnvironmentLaw Q))
    (F : Vec d × FieldPair d → Mat d) (_hFm : Measurable F)
    (_hFi : ∀ y k, Integrable (fun ω j => F (y, ω) j k) (reducedEnvironmentLaw Q))
    (_hskew : ∀ y, ∀ᵐ ω ∂reducedEnvironmentLaw Q, (F (y, ω)).transpose = -F (y, ω)),
    ∃ S : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Mat d)
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance S) ∧
      (∀ z, (S z).transpose = -S z) ∧
      (∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
        (fun ω j => S (y, ω) j k) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun ω j => F (y.1, ω) j k |
            reducedCoefficientObservationSigma
              {z | euclideanNorm (z - y.1) < 32 * R}]) ∧
      (let K : FieldPair d → Vec d := fun ω => ∫ y,
          (S (y, ω)).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) ∂volume
       (@Measurable (FieldPair d) (Vec d)
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
          inferInstance K) ∧
        ∀ (p A B : ℝ), 1 ≤ p → 0 ≤ A → 0 ≤ B →
        ∀ (_hshift : ∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
          eLpNorm (fun ω => euclideanNorm ((fun j => F (y.1, ω) j k) - f k ω))
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B)
        (_htail : ∀ k, eLpNorm (fun ω => euclideanNorm (f k ω -
          (reducedEnvironmentLaw Q)[f k | reducedCoefficientObservationSigma
            {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
            (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A),
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y =>
          (S (y, ω)).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1))) volume) ∧
        MemLp (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹)) := by
  obtain ⟨W, hW, hweights⟩ := exists_uniform_mollifier_derivative_weights d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q hR f hf F hFm hFi hskew
  obtain ⟨hwm, hwi, hw, hwbound⟩ := hweights R (zero_lt_one.trans_le hR)
  letI := finite_center_volume (d := d) R
  let w : {y : Vec d // euclideanNorm y ≤ R} → Vec d :=
    fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1)
  obtain ⟨S, hSm, hSs, hSv⟩ :=
    exists_joint_center_conditioned_skew_family Q R F hFm hFi hskew
  have hle : reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm z < 33 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {z : Vec d // euclideanNorm z < 33 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hui : @Measurable
      ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
      ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
      inferInstance
      (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})) id :=
    measurable_fst.prodMk ((measurable_id'' hle).comp measurable_snd)
  have hS : Measurable S := hSm.comp hui
  let g : Fin d → {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → Vec d :=
    fun k y ω => (fun j => F (y.1, ω) j k) - f k ω
  have hgi (k : Fin d) (y : {y : Vec d // euclideanNorm y ≤ R}) :
      Integrable (g k y) (reducedEnvironmentLaw Q) := (hFi y.1 k).sub (hf k)
  have hversion (k : Fin d) (y : {y : Vec d // euclideanNorm y ≤ R}) :
      (fun ω j => S (y, ω) j k) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[f k + g k y | reducedCoefficientObservationSigma
          {z | euclideanNorm (z - y.1) < 32 * R}] := by
    have heq : f k + g k y = fun ω j => F (y.1, ω) j k := by
      ext ω j
      dsimp only [g, Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq]
    exact hSv k y
  refine ⟨S, hSm, hSs, hSv, ?_, ?_⟩
  · letI : MeasurableSpace (FieldPair d) :=
      reducedCoefficientObservationSigma {z : Vec d | euclideanNorm z < 33 * R}
    have hm : Measurable (fun z => (S z).mulVec (w z.1)) := by
      apply measurable_pi_lambda
      intro j
      change Measurable (fun z => ∑ k : Fin d, S z j k * w z.1 k)
      exact Finset.measurable_fun_sum _ fun k _ =>
        ((continuous_id.matrix_elem j k).measurable.comp hSm).mul
          (((measurable_pi_apply k).comp hwm).comp measurable_fst)
    exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  · intro p A B hp hA hB hshift htail
    have hbound := local_center_conditioned_skew_derivative_bound hR volume hp hA hB
      (fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1))
      hwm hwi hw hwbound f hf g hgi hshift htail S hS hversion
    exact ⟨hbound.1, hbound.2.2⟩

end EinsteinRelation.Correctors
