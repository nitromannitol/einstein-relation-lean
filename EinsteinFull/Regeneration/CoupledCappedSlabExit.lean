import EinsteinFull.Regeneration.CoupledSlabExitTail
import EinsteinFull.Regeneration.CappedSlabPositiveExit

/-!
# Capped slab exits under the regeneration coupling

Geometric survival of a slab under the coupled law provides a deterministic
time cap with an arbitrarily small late-exit probability. A lower bound for
the positive-exit probability then gives positive drift of the capped step.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The geometric coupled survival estimate holds for the annealed path marginal. -/
theorem annealed_path_slab_survival_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (r : ℝ) (N m : ℕ) (hwidth : 2 * r ≤ (N : ℝ) * (8 * (l / lam))) :
    ((annealedCoupledLaw Q.measure K).map (fun q => q.2.1)).real {γ |
      (((m * N : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0∞) <
        coordinateSlabExit γ (Renewal.forceCoord hd) r} ≤ (1 - δ ^ N) ^ m := by
  have h := coupled_coordinate_slab_survival_le hd Q lam h0 h1 l δ hδ hδ1 P K hK
    r N m hwidth
  have hreal := ENNReal.toReal_mono (by finiteness) h
  have hnonneg : 0 ≤ 1 - δ ^ N := sub_nonneg.mpr (pow_le_one₀ hδ hδ1)
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hnonneg] at hreal
  have hevent : MeasurableSet {γ : Path d |
      (((m * N : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0∞) <
        coordinateSlabExit γ (Renewal.forceCoord hd) r} :=
    measurableSet_lt measurable_const (measurable_coordinateSlabExit _ _)
  change (((annealedCoupledLaw Q.measure K).map (fun q => q.2.1)) _).toReal ≤ _
  rw [Measure.map_apply (show Measurable (fun q : FieldPair d × CoupledSample d => q.2.1) from
    measurable_fst.comp measurable_snd) hevent]
  exact hreal

/-- A likely positive exit yields a likely positive capped exit for a suitable grid cap. -/
theorem exists_annealed_positive_capped_slab_exit {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (r : ℝ) (hr : 0 < r) (N : ℕ) (hwidth : 2 * r ≤ (N : ℝ) * (8 * (l / lam)))
    (hpositive : (2 / 3 : ℝ) ≤
      ((annealedCoupledLaw Q.measure K).map (fun q => q.2.1)).real {γ |
        coordinateSlabExit γ (Renewal.forceCoord hd) r ≠ ⊤ ∧
        γ (coordinateSlabExit γ (Renewal.forceCoord hd) r).toNNReal
          (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = r}) :
    ∃ m : ℕ, (3 / 5 : ℝ) ≤
      ((annealedCoupledLaw Q.measure K).map (fun q => q.2.1)).real {γ |
        cappedSlabIncrement γ (Renewal.forceCoord hd) r
          (((m * N : ℕ) : ℝ≥0) * Renewal.regenDelta lam) 0 = 1} := by
  have hq : 1 - δ ^ N < 1 := by have := pow_pos hδ N; linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 15) hq
  refine ⟨m, ?_⟩
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure ((annealedCoupledLaw Q.measure K).map (fun q => q.2.1)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_fst.comp measurable_snd).aemeasurable).2 hprob
  apply cappedSlab_positive_probability_of_exit_bounds _ _ _ hr _ hpositive
  exact (annealed_path_slab_survival_le hd Q lam h0 h1 l δ hδ.le hδ1 P K hK r N m hwidth).trans hm.le

end EinsteinFull.Regeneration
