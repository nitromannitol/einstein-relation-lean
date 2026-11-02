import EinsteinFull.Calculus.C10TestBlocksSupport
import EinsteinFull.Calculus.C7UnitInitializationSupport

/-! Colored summation of centered complex square-integrable block families. -/

open MeasureTheory ProbabilityTheory
open EinsteinFull.Calculus.C10TestBlocks EinsteinFull.Calculus.S1

namespace EinsteinFull.Blueprint

/-- An absolutely L²-summable centered family with independent pairs of each
color has a literal pointwise sum and the colored square-sum L² bound. -/
@[nolint unusedArguments]
theorem colored_complex_series_L2
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (col : ι → Fin n) (f : ι → Ω → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ)
    (hmean : ∀ i, (∫ ω, f i ω ∂μ) = 0)
    (hind : ∀ i j, col i = col j → i ≠ j → IndepFun (f i) (f j) μ)
    (c : ι → ℝ) (hc : ∀ i, ‖(hf i).toLp (f i)‖ ≤ c i)
    (hs : Summable c) (hs2 : Summable (fun i => c i ^ 2)) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
    MemLp (fun ω => ∑' i, f i ω) 2 μ ∧
    Real.sqrt (∫ ω, ‖∑' i, f i ω‖ ^ 2 ∂μ) ≤
      (n : ℝ) * Real.sqrt (∑' i, c i ^ 2) := by
  let g : ι → Lp ℂ 2 μ := fun i => (hf i).toLp (f i)
  have hgnorm : Summable (fun i => ‖g i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg (g i)) hc hs
  have hgenorm : ∑' i, ‖g i‖ₑ ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.2 hgnorm
  have hfnorm : ∑' i, eLpNorm (f i) 2 μ ≠ ⊤ := by
    simpa only [g, Lp.enorm_toLp] using hgenorm
  obtain ⟨ha, hm⟩ := summable_memLp_tsum hf hfnorm
  refine ⟨ha, hm, ?_⟩
  have hall : ∀ᵐ ω ∂μ, ∀ i, g i ω = f i ω :=
    ae_all_iff.2 fun i => (hf i).coeFn_toLp
  have heq : hm.toLp (fun ω => ∑' i, f i ω) = ∑' i, g i := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, Lp.coeFn_tsum hgenorm, hall]
      with ω hω hωsum hωall
    exact hω.trans ((tsum_congr hωall).symm.trans hωsum.symm)
  change l2Size μ (fun ω => ∑' i, f i ω) ≤ _
  rw [l2Size_eq_norm_toLp hm, heq]
  apply EinsteinFull.UnitInitialization.norm_hasSum_le_colored_sqrt
    col g c hgnorm.of_norm.hasSum ?_ hc hs2
  intro i j hij hne
  exact indepFun_inner_toLp_eq_zero (hf i) (hf j) (hind i j hij hne) (hmean i)

end EinsteinFull.Blueprint
