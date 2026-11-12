import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import EinsteinRelation.Correctors.StationaryLocalL2Square

/-!
# Means of almost-sure limits and subsequence extraction

Source: `paper/main.tex:740-756`; AKM Lemma 6.1, Step 4. Uniform square bounds pass
the mean through an almost-sure limit. An almost-sure joint limit `A m - B n` with
`A` convergent in `L¹` forces `B` to converge almost surely along a subsequence,
and such a limit agrees with any `L¹` limit.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace EinsteinRelation.Correctors

/-- Variables bounded in `L²` are uniformly integrable in `L¹`. -/
theorem unifIntegrable_one_of_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {M : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hbound : ∀ n, eLpNorm (X n) 2 μ ≤ ENNReal.ofReal M) :
    UnifIntegrable X 1 μ := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top hX fun ε hε => ?_
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set C : ℝ≥0 := ⟨M' ^ 2 / ε + 1, by positivity⟩ with hCdef
  have hCpos : (0 : ℝ) < (C : ℝ) := by simp only [hCdef, NNReal.coe_mk]; positivity
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NNReal.coe_pos.mp hCpos).ne'
  refine ⟨C, fun n => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hpt : ∀ x, ‖{x | C ≤ ‖X n x‖₊}.indicator (X n) x‖ₑ ≤ ‖X n x‖ₑ ^ 2 / C := by
    intro x
    by_cases hx : C ≤ ‖X n x‖₊
    · rw [Set.indicator_of_mem (show x ∈ {x | C ≤ ‖X n x‖₊} from hx),
        ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl ENNReal.coe_ne_top), sq]
      exact mul_le_mul_right (by exact_mod_cast hx) _
    · rw [Set.indicator_of_notMem (show x ∉ {x | C ≤ ‖X n x‖₊} from hx), enorm_zero]
      exact zero_le _
  have hMn : eLpNorm (X n) 2 μ ≤ ENNReal.ofReal M' :=
    (hbound n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc (∫⁻ x, ‖{x | C ≤ ‖X n x‖₊}.indicator (X n) x‖ₑ ∂μ)
      ≤ ∫⁻ x, ‖X n x‖ₑ ^ 2 / C ∂μ := lintegral_mono hpt
    _ = (∫⁻ x, ‖X n x‖ₑ ^ 2 ∂μ) / C := by
        simp only [div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hC0)
    _ = eLpNorm (X n) 2 μ ^ 2 / C := by rw [eLpNorm_two_sq_eq_lintegral_enorm_sq]
    _ ≤ ENNReal.ofReal M' ^ 2 / C := by gcongr
    _ = ENNReal.ofReal (M' ^ 2 / C) := by
        rw [← ENNReal.ofReal_pow hM'0, ENNReal.ofReal_div_of_pos hCpos, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hCpos]
        simp only [hCdef, NNReal.coe_mk]
        rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
        linarith

/-- Almost-sure limits of mean-zero variables bounded in `L²` are integrable with mean
zero. -/
theorem integral_eq_zero_of_tendsto_ae_of_eLpNorm_two_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {M : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hbound : ∀ n, eLpNorm (X n) 2 μ ≤ ENNReal.ofReal M)
    (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y μ ∧ ∫ ω, Y ω ∂μ = 0 := by
  have hY : AEStronglyMeasurable Y μ := aestronglyMeasurable_of_tendsto_ae atTop hX hlim
  have hY2 : eLpNorm Y 2 μ ≤ ENNReal.ofReal M :=
    (Lp.eLpNorm_lim_le_liminf_eLpNorm hX Y hlim).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
  have hYm : MemLp Y 2 μ := ⟨hY, hY2.trans_lt ENNReal.ofReal_lt_top⟩
  have hY1 : Integrable Y μ := hYm.integrable one_le_two
  have hXi (n : ℕ) : Integrable (X n) μ :=
    (MemLp.integrable one_le_two ⟨hX n, (hbound n).trans_lt ENNReal.ofReal_lt_top⟩)
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hX
    (memLp_one_iff_integrable.mpr hY1) (unifIntegrable_one_of_eLpNorm_two_le hX hbound) hlim
  have hint := tendsto_integral_of_L1' Y hY1 (Eventually.of_forall hXi) hL1
  simp only [hmean] at hint
  exact ⟨hY1, tendsto_nhds_unique hint tendsto_const_nhds⟩

/-- If `X (m,n) = A m - B n` almost surely, `X` converges almost surely along the
product filter and `A` converges in `L¹`, then `B` converges almost surely along a
subsequence. -/
theorem exists_subseq_ae_tendsto_of_sub {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → ℝ} {A B : ℕ → Ω → ℝ}
    {Y A' : Ω → ℝ} (hA : ∀ m, AEStronglyMeasurable (A m) μ)
    (hA' : AEStronglyMeasurable A' μ)
    (hdec : ∀ m n, ∀ᵐ ω ∂μ, X (m, n) ω = A m ω - B n ω)
    (hX : ∀ᵐ ω ∂μ, Tendsto (fun mn => X mn ω) atTop (𝓝 (Y ω)))
    (hAlim : Tendsto (fun m => eLpNorm (fun ω => A m ω - A' ω) 1 μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun k => B (φ k) ω) atTop (𝓝 (A' ω - Y ω)) := by
  have hmeas : TendstoInMeasure μ A atTop A' :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hA hA' hAlim
  obtain ⟨φ, hφ, hAφ⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hdiag : Tendsto (fun k => (φ k, φ k)) atTop (atTop : Filter (ℕ × ℕ)) := by
    rw [← prod_atTop_atTop_eq]
    exact hφ.tendsto_atTop.prodMk hφ.tendsto_atTop
  filter_upwards [hAφ, hX, ae_all_iff.mpr fun k => hdec (φ k) (φ k)] with ω h1 h2 h3
  have hXk : Tendsto (fun k => X (φ k, φ k) ω) atTop (𝓝 (Y ω)) := h2.comp hdiag
  have heq : (fun k => B (φ k) ω) = fun k => A (φ k) ω - X (φ k, φ k) ω := by
    funext k
    rw [h3 k]
    ring
  rw [heq]
  exact h1.sub hXk

/-- An almost-sure limit along a subsequence agrees with an `L¹` limit. -/
theorem ae_eq_of_subseq_tendsto_ae_of_tendsto_eLpNorm_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {B : ℕ → Ω → ℝ} {Y Z : Ω → ℝ}
    (hB : ∀ n, AEStronglyMeasurable (B n) μ) (hZ : AEStronglyMeasurable Z μ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hY : ∀ᵐ ω ∂μ, Tendsto (fun k => B (φ k) ω) atTop (𝓝 (Y ω)))
    (hZlim : Tendsto (fun n => eLpNorm (fun ω => B n ω - Z ω) 1 μ) atTop (𝓝 0)) :
    Y =ᵐ[μ] Z := by
  have hYm : AEStronglyMeasurable Y μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => hB (φ k)) hY
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_ae (fun k => hB (φ k)) hY)
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun k => hB (φ k)) hZ
      (hZlim.comp hφ.tendsto_atTop))

end EinsteinRelation.Correctors
