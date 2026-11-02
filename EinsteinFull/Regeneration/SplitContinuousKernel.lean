import EinsteinFull.Regeneration.SplitSegmentCompatibility
import EinsteinFull.Regeneration.SplitSegmentGluing
import EinsteinRelation.Regeneration.IntervalHistory

/-!
# The continuous path and coin kernel of the canonical split segments

The measurable gluing map sends the joint infinite segment law to the actual
continuous-path/coin carrier. Compatible segments are reproduced on every
closed grid interval, preserving in particular the joint first-interval law.
Identifying the whole path marginal with the original Markov process and
proving stopped locality remain separate obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- Glue the actual sampled segments and retain their entire coin sequence. -/
def gluedSplitSegmentSample {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (s : ℕ → SplitSegmentState d) : CoupledSample d :=
  (glueSplitSegments Δ hΔ (fun n => (s n).2.1), fun n => (s n).2.2)

/-- The simultaneous continuous-path/coin construction is measurable. -/
theorem measurable_gluedSplitSegmentSample {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    Measurable (gluedSplitSegmentSample (d := d) Δ hΔ) := by
  exact ((measurable_glueSplitSegments Δ hΔ).comp
    (Measurable.of_eval (fun n => (measurable_pi_apply n).snd.fst))).prodMk
    (Measurable.of_eval (fun n => (measurable_pi_apply n).snd.snd))

variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

/-- The actual continuous path and entire coin sequence, sampled jointly. -/
def splitContinuousCouplingKernel : CoupledQuenchedLaws d :=
  (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
    (gluedSplitSegmentSample Δ hΔ)

instance isMarkovKernel_splitContinuousCouplingKernel :
    IsMarkovKernel (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor) := by
  unfold splitContinuousCouplingKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_gluedSplitSegmentSample Δ hΔ)

/-- On one event of full measure, the glued path agrees with every actual
sampled segment throughout its closed interval. -/
theorem ae_gluedSplitSegmentSample_interval
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) :
    ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      ∀ (n : ℕ) (u : ℝ≥0), u ≤ Δ →
        (gluedSplitSegmentSample Δ hΔ s).1 (n * Δ + u) = (s n).2.1 u := by
  filter_upwards [ae_splitSegmentSequenceKernel_endpoints Δ δ R i hδ₀ hδ₁ hR P hminor
    hstart a] with s hs
  intro n u hu
  exact glueSplitSegments_interval Δ hΔ (fun n => (s n).2.1) hs.2 n u hu

/-- The continuous coupling starts at its actual input position. -/
theorem ae_splitContinuousCouplingKernel_start
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) :
    ∀ᵐ z ∂splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a,
      z.1 0 = a.1 := by
  rw [splitContinuousCouplingKernel, Kernel.map_apply _
    (measurable_gluedSplitSegmentSample Δ hΔ)]
  apply (ae_map_iff (measurable_gluedSplitSegmentSample Δ hΔ).aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  filter_upwards [ae_splitSegmentSequenceKernel_endpoints Δ δ R i hδ₀ hδ₁ hR P hminor
    hstart a] with s hs
  have h := glueSplitSegments_interval Δ hΔ (fun n => (s n).2.1) hs.2 0 0 Δ.2
  simpa only [gluedSplitSegmentSample, Nat.cast_zero, zero_mul, zero_add] using h.trans hs.1

/-- The full coin projection is exactly the projection of the same joint
segment sequence; no independence is asserted by this projection identity. -/
theorem map_splitContinuousCouplingKernel_coins :
    (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor).map Prod.snd =
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun s n => (s n).2.2) := by
  rw [splitContinuousCouplingKernel, ← Kernel.map_comp_right _
    (measurable_gluedSplitSegmentSample Δ hΔ) measurable_snd]
  rfl

/-- The glued path and first coin retain the exact joint law of the
canonical one-interval split construction at every time in that interval. -/
theorem map_splitContinuousCouplingKernel_first_eval
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (t : ℝ≥0) (ht : t ≤ Δ) :
    (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun z => (z.1 t, z.2 0)) =
      (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor).map
        (fun z => (z.1 t, z.2)) := by
  rw [splitContinuousCouplingKernel, ← Kernel.map_comp_right _
    (measurable_gluedSplitSegmentSample Δ hΔ) (by fun_prop)]
  have heq :
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
          ((fun z : CoupledSample d => (z.1 t, z.2 0)) ∘ gluedSplitSegmentSample Δ hΔ) =
        (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
          (fun s => ((s 0).2.1 t, (s 0).2.2)) := by
    ext a : 1
    rw [Kernel.map_apply _ ((show Measurable
      (fun z : CoupledSample d => (z.1 t, z.2 0)) from by fun_prop).comp
        (measurable_gluedSplitSegmentSample Δ hΔ)), Kernel.map_apply _ (by fun_prop)]
    apply Measure.map_congr
    filter_upwards [ae_gluedSplitSegmentSample_interval Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
      hstart a] with s hs
    apply Prod.ext
    · simpa only [Function.comp_apply, Nat.cast_zero, zero_mul, zero_add] using hs 0 t ht
    · rfl
  rw [heq]
  change (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
    ((fun z : Path d × Bool => (z.1 t, z.2)) ∘ (fun s => (s 0).2)) = _
  rw [Kernel.map_comp_right _ (by fun_prop) (by fun_prop),
    map_splitSegmentSequenceKernel_first]

/-- Every full stopped interval observation agrees with the corresponding
sampled segment and coin, simultaneously for every interval index. -/
theorem ae_gluedSplitSegmentSample_observation
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) :
    ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      ∀ n, intervalObservation Δ n (gluedSplitSegmentSample Δ hΔ s) =
        (intervalPath Δ 0 (s n).2.1, (s n).2.2) := by
  filter_upwards [ae_gluedSplitSegmentSample_interval Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    hstart a] with s hs
  intro n
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    simpa only [intervalObservation, intervalPath_apply, Nat.cast_zero, zero_mul, zero_add]
      using hs n (min t Δ) (min_le_right t Δ)
  · rfl

/-- The full stopped first segment and its coin retain their canonical joint
law, including all path correlations within the interval. -/
theorem map_splitContinuousCouplingKernel_first_observation
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) :
    (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor).map
        (intervalObservation Δ 0) =
      (oneIntervalSplitKernel Δ δ R i hδ₀.le hR P hminor).map
        (fun z => (intervalPath Δ 0 z.1, z.2)) := by
  rw [splitContinuousCouplingKernel, ← Kernel.map_comp_right _
    (measurable_gluedSplitSegmentSample Δ hΔ) (measurable_intervalObservation Δ 0)]
  have heq :
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
          (intervalObservation Δ 0 ∘ gluedSplitSegmentSample Δ hΔ) =
        (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
          (fun s => (intervalPath Δ 0 (s 0).2.1, (s 0).2.2)) := by
    ext a : 1
    have hm : Measurable (fun s : ℕ → SplitSegmentState d =>
        (intervalPath Δ 0 (s 0).2.1, (s 0).2.2)) := by
      have h₀ : Measurable (fun s : ℕ → SplitSegmentState d => s 0) := measurable_pi_apply 0
      exact (((continuous_intervalPath Δ 0).measurable.comp h₀.snd.fst).prodMk h₀.snd.snd)
    rw [Kernel.map_apply _ ((measurable_intervalObservation Δ 0).comp
      (measurable_gluedSplitSegmentSample Δ hΔ)), Kernel.map_apply _ hm]
    exact Measure.map_congr ((ae_gluedSplitSegmentSample_observation Δ hΔ δ R i hδ₀ hδ₁ hR
      P hminor hstart a).mono (fun s hs => hs 0))
  rw [heq]
  change (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
    ((fun z : Path d × Bool => (intervalPath Δ 0 z.1, z.2)) ∘ (fun s => (s 0).2)) = _
  have hm : Measurable (fun z : Path d × Bool => (intervalPath Δ 0 z.1, z.2)) :=
    ((continuous_intervalPath Δ 0).measurable.comp measurable_fst).prodMk measurable_snd
  rw [Kernel.map_comp_right _ (by fun_prop) hm,
    map_splitSegmentSequenceKernel_first]

end EinsteinFull.Regeneration
