import EinsteinRelation.Probability.SlutskyMetric
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Slutsky's theorem with a constant, for metrizable factors

Mathlib's `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, and its variant
`EinsteinRelation.prodMk_of_tendstoInMeasure_const_metric`, need the first factor to be a
seminormed group. Continuous paths `C(ℝ≥0, ℝᵈ)` with the topology of locally uniform convergence
are not. This file proves the theorem for pseudo-metrizable, second-countable factors: if `X n`
converges in distribution to `Z` and `Y n` converges in probability to a constant `c`, then the
pair `(X n, Y n)` converges in distribution to `(Z, c)`. Convergence in probability to `c` is
stated topologically, so it needs no chosen metric.
-/

open MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal

namespace EinsteinRelation

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {l : Filter ι}

/-- Slutsky's theorem with a constant, for pseudo-metric factors. -/
theorem tendstoInDistribution_prodMk_of_dist_tendsto_const
    {E E' : Type*} {mE : MeasurableSpace E} {mE' : MeasurableSpace E'}
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    [PseudoMetricSpace E'] [SecondCountableTopology E'] [BorelSpace E']
    [l.IsCountablyGenerated] {X : ι → Ω → E} {Y : ι → Ω → E'} {Z : Ω → E} {c : E'}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ)
    (hY : ∀ δ : ℝ, 0 < δ → Tendsto (fun n ↦ μ.real {ω | δ ≤ dist (Y n ω) c}) l (𝓝 0))
    (hYm : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c)) (fun _ ↦ μ) μ := by
  have hpair : TendstoInDistribution (fun n ω ↦ (X n ω, c)) l (fun ω ↦ (Z ω, c))
      (fun _ ↦ μ) μ :=
    hXZ.continuous_comp (g := fun x : E ↦ (x, c)) (continuous_id.prodMk continuous_const)
  refine tendstoInDistribution_of_dist_tendsto_zero (fun n ω ↦ (X n ω, Y n ω)) _ hpair ?_ ?_
  · intro δ hδ
    have hset : ∀ n, {ω | δ ≤ dist (X n ω, Y n ω) (X n ω, c)} = {ω | δ ≤ dist (Y n ω) c} := by
      intro n
      ext ω
      simp [Prod.dist_eq]
    simpa only [hset] using hY δ hδ
  · intro i
    exact (hXZ.forall_aemeasurable i).prodMk (hYm i)

/-- Slutsky's theorem with a constant, for pseudo-metrizable second-countable factors. The second
sequence converges to `c` in probability: every neighbourhood of `c` is eventually left with
vanishing probability. -/
theorem tendstoInDistribution_prodMk_of_tendsto_const
    {E E' : Type*} {mE : MeasurableSpace E} {mE' : MeasurableSpace E'}
    [TopologicalSpace E] [PseudoMetrizableSpace E] [SecondCountableTopology E] [BorelSpace E]
    [TopologicalSpace E'] [PseudoMetrizableSpace E'] [SecondCountableTopology E'] [BorelSpace E']
    [l.IsCountablyGenerated] {X : ι → Ω → E} {Y : ι → Ω → E'} {Z : Ω → E} {c : E'}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ)
    (hY : ∀ U ∈ 𝓝 c, Tendsto (fun n ↦ μ {ω | Y n ω ∉ U}) l (𝓝 0))
    (hYm : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c)) (fun _ ↦ μ) μ := by
  letI := pseudoMetrizableSpacePseudoMetric E
  letI := pseudoMetrizableSpacePseudoMetric E'
  refine tendstoInDistribution_prodMk_of_dist_tendsto_const hXZ (fun δ hδ ↦ ?_) hYm
  have hball := hY (Metric.ball c δ) (Metric.ball_mem_nhds c hδ)
  have hreal : Tendsto (fun n ↦ μ.real {ω | Y n ω ∉ Metric.ball c δ}) l (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hball
    rw [ENNReal.toReal_zero] at this
    exact this
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) hreal
  refine measureReal_mono (fun ω hω ↦ ?_)
  simp only [Set.mem_setOf_eq, Metric.mem_ball, not_lt] at hω ⊢
  exact hω

end EinsteinRelation
