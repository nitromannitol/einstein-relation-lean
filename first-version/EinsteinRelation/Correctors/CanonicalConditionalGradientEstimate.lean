import EinsteinRelation.Correctors.CanonicalConditionalCenterVersions
import EinsteinRelation.Correctors.LocalMollifierGradientRealization

/-! # The gradient estimate for the common chosen fields

Source: `paper/main.tex:968–973`. The literal conditional canonical-gradient
average in the spatial construction agrees with the local conditional-gradient
realization. Its error estimate therefore uses exactly the same fields, with
no new choice depending on the exponent.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- Every conditional-tail estimate controls the gradient average already
used in the common spatial fields. Source: `paper/main.tex:968–973`. -/
theorem canonicalConditionalMollifierFields_gradient_error
    {d : ℕ} {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 1 ≤ R)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    {p A : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A)
    (htail : eLpNorm (fun ω => euclideanNorm
      (((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp -
        (reducedEnvironmentLaw Q)[fun a =>
          ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) a).ofLp |
          reducedCoefficientObservationSigma
            {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) :
    MemLp (fun ω => euclideanNorm
      ((canonicalConditionalMollifierFields Q i R u S).gradientAverage ω -
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
    eLpNorm (fun ω => euclideanNorm
      ((canonicalConditionalMollifierFields Q i R u S).gradientAverage ω -
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * A) := by
  letI : StandardBorelSpace (FieldPair d) := ReductionImageV3.fieldPair_standardBorel d
  letI := finiteMeasure_mollifierCenterDomain (d := d) R
  let f : FieldPair d → Vec d := fun ω =>
    ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) ω).ofLp
  let J := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  have hfm : Measurable f :=
    J.continuous.measurable.comp (Lp.stronglyMeasurable _).measurable
  have hfi : Integrable f (reducedEnvironmentLaw Q) :=
    J.toContinuousLinearMap.integrable_comp ((Lp.memLp _).integrable (by norm_num))
  let B : Set (Vec d) := {x | euclideanNorm x < 32 * R}
  have hobs : reducedCoefficientObservationSigma B ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : B =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  let g : FieldPair d → Vec d → Vec d := fun ω x => f (translate x ω)
  have hgm (j : Fin d) : StronglyMeasurable
      (fun z : FieldPair d × Vec d => g z.1 z.2 j) :=
    (((measurable_pi_apply j).comp hfm).comp
      (Probability.continuous_translate.measurable.comp measurable_swap)).stronglyMeasurable
  let v : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d := fun z j =>
    conditionalSpatialAverage (reducedCoefficientObservationSigma B)
      (reducedEnvironmentLaw Q) (fun a x => g a x j) (translate z.1.1 z.2) (-z.1.1)
  have hvm : Measurable v := by
    apply measurable_pi_lambda
    intro j
    have hc := (stronglyMeasurable_conditionalSpatialAverage
      (reducedCoefficientObservationSigma B) (reducedEnvironmentLaw Q)
      (fun a x => g a x j) (hgm j)).measurable
    exact hc.comp
      (((measurable_id'' hobs).comp (Probability.continuous_translate.measurable.comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))).prodMk
          (measurable_subtype_coe.comp measurable_fst).neg)
  have hv (y : {y : Vec d // euclideanNorm y ≤ R}) :
      (fun ω => v (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] := by
    have hc (j : Fin d) : (fun ω => v (y, ω) j) =ᵐ[reducedEnvironmentLaw Q]
        (fun ω => (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] ω j) := by
      have hpres : MeasurePreserving (translate (-y.1))
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
        ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
      have hci := (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).integrable_comp hfi
      have he := centered_conditionalSpatialAverage_ae_eq_condExp Q R
        (fun a x => g a x j) (hgm j) y.1 (hpres.integrable_comp_of_integrable hci)
      have hpj := (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_condExp_comm
        (m := reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}) hfi
      apply he.trans
      simpa only [g, translate_add, add_neg_cancel, neg_add_cancel, translate_zero,
        Function.comp_def, ContinuousLinearMap.proj_apply] using hpj.symm
    filter_upwards [ae_all_iff.mpr hc] with ω hω
    exact funext hω
  obtain ⟨v', hv'm, hv'⟩ := exists_local_canonical_mollifier_gradient_realization Q i hR
  obtain ⟨hv'local, hest⟩ := hv'.2
  obtain ⟨hint, hmem, hb⟩ := hest p A hp hA htail
  have hv'ma : Measurable v' := by
    have h33 : reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm x < 33 * R} ≤ borel (FieldPair d) := by
      rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
      exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < 33 * R} =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
    exact hv'm.comp (measurable_fst.prodMk (measurable_snd.mono le_rfl h33))
  let w : {y : Vec d // euclideanNorm y ≤ R} → ℝ :=
    fun y => Calculus.unitMassScaledMollifier d R (-y.1)
  have hwm : Measurable w :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp
      measurable_subtype_coe.neg
  have heq (j : Fin d) :
      (fun ω => ∫ y, w y * v (y, ω) j) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => ∫ y, w y * v' (y, ω) j) := by
    apply ae_integral_eq_of_forall_ae_eq volume (reducedEnvironmentLaw Q)
      _ _ ((hwm.comp measurable_fst).mul ((measurable_pi_apply j).comp hvm))
      ((hwm.comp measurable_fst).mul ((measurable_pi_apply j).comp hv'ma))
    intro y
    filter_upwards [hv y, hv'.1 y] with ω hω hω'
    change w y * v (y, ω) j = w y * v' (y, ω) j
    rw [hω, hω']
  have havg : (canonicalConditionalMollifierFields Q i R u S).gradientAverage =ᵐ[
      reducedEnvironmentLaw Q] (fun ω => ∫ y, w y • v' (y, ω)) := by
    filter_upwards [ae_all_iff.mpr heq, hint] with ω hω hi
    funext j
    change (∫ y, Calculus.unitMassScaledMollifier d R (-y) *
      conditionalSpatialAverage (reducedCoefficientObservationSigma B)
        (reducedEnvironmentLaw Q) (fun a x => g a x j) (translate y ω) (-y)) = _
    rw [mollifier_integral_eq_centerIntegral (zero_lt_one.trans_le hR)]
    change (∫ y, w y * v (y, ω) j) = _
    rw [hω j]
    exact (ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) hi).trans (by rfl)
  have herr : (fun ω => euclideanNorm
      ((canonicalConditionalMollifierFields Q i R u S).gradientAverage ω - f ω)) =ᵐ[
      reducedEnvironmentLaw Q] (fun ω => euclideanNorm ((∫ y, w y • v' (y, ω)) - f ω)) :=
    havg.mono fun ω hω => congrArg (fun a => euclideanNorm (a - f ω)) hω
  exact ⟨(memLp_congr_ae herr).mpr hmem, (eLpNorm_congr_ae herr).trans_le hb⟩

end EinsteinRelation.Correctors
