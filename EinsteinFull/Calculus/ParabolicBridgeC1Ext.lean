import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# From `C^∞` to `C¹` test functions

A linear identity `∑ ∫ Aᵢ ∂_{wᵢ}φ + ∫ B φ = 0` that holds for all smooth compactly supported
test functions in an open set `Ω` also holds for `C¹` compactly supported test functions, when the
coefficients `Aᵢ`, `B` are integrable on `Ω`.  The proof mollifies `φ`.
-/

open scoped ENNReal Convolution Topology

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A sequence of bumps with outer radius `δ / (n + 2)`. -/
def shrinkBump (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : E) :=
  ⟨δ / (2 * ((n : ℝ) + 2)), δ / ((n : ℝ) + 2), by positivity, by
    have h : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact div_lt_div_of_pos_left hδ h (by linarith)⟩

theorem shrinkBump_rOut (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (shrinkBump δ hδ n : ContDiffBump (0 : E)).rOut = δ / ((n : ℝ) + 2) := rfl

theorem shrinkBump_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (shrinkBump δ hδ n : ContDiffBump (0 : E)).rOut) atTop (𝓝 0) := by
  simp only [shrinkBump_rOut]
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

theorem abs_convolution_normed_le (b : ContDiffBump (0 : E)) (μ : Measure E)
    [μ.IsAddHaarMeasure] {f : E → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M) (z : E) :
    |(b.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) z| ≤ M := by
  have hint : Integrable (b.normed μ) μ := b.integrable_normed
  rw [convolution_def, ← Real.norm_eq_abs]
  have hb : Integrable (fun t => b.normed μ t * M) μ := hint.mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans ?_
  · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (b.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hM _) (b.nonneg_normed t)
  · rw [integral_mul_const, b.integral_normed, one_mul]

/-- Dominated convergence for a weighted integral over `Ω`. -/
theorem tendsto_weighted_integral {μ : Measure E} {Ω : Set E} {a : E → ℝ}
    (ha : IntegrableOn a Ω μ) {f : ℕ → E → ℝ} {f0 : E → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (f n) (μ.restrict Ω)) {C : ℝ}
    (hbd : ∀ n z, |f n z| ≤ C) (hlim : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (f0 z))) :
    Tendsto (fun n => ∫ z in Ω, a z * f n z ∂μ) atTop (𝓝 (∫ z in Ω, a z * f0 z ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => ‖a z‖ * C) ?_ ?_ ?_ ?_
  · exact fun n => ha.aestronglyMeasurable.mul (hmeas n)
  · exact ha.norm.mul_const _
  · intro n
    refine Eventually.of_forall fun z => ?_
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd n z) (abs_nonneg _)
  · exact Eventually.of_forall fun z => (hlim z).const_mul (a z)

/-- A weak identity tested on smooth functions extends to `C¹` test functions. -/
theorem weak_identity_C1_of_smooth (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Set E}
    (hΩ : IsOpen Ω) {ι : Type*} [Fintype ι] (w : ι → E) (A : ι → E → ℝ) (B : E → ℝ)
    (hA : ∀ i, IntegrableOn (A i) Ω μ) (hB : IntegrableOn B Ω μ)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      ∑ i, (∫ z in Ω, A i z * fderiv ℝ φ z (w i) ∂μ) + ∫ z in Ω, B z * φ z ∂μ = 0)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∑ i, (∫ z in Ω, A i z * fderiv ℝ φ z (w i) ∂μ) + ∫ z in Ω, B z * φ z ∂μ = 0 := by
  obtain ⟨δ, hδ, hδΩ⟩ := (show IsCompact (tsupport φ) from hc).exists_cthickening_subset_open hΩ hs
  let b : ℕ → ContDiffBump (0 : E) := shrinkBump δ hδ
  let ψ : ℕ → E → ℝ := fun n => (b n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] φ
  have hlim_r : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := shrinkBump_tendsto δ hδ
  have hloc : ∀ n, LocallyIntegrable ((b n).normed μ) μ := fun n =>
    (b n).integrable_normed.locallyIntegrable
  have hψsm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n =>
    (b n).hasCompactSupport_normed.contDiff_convolution_left _ (b n).contDiff_normed
      hφ.continuous.locallyIntegrable
  have hψcs : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (b n).hasCompactSupport_normed.convolution _ hc
  have hψsub : ∀ n, tsupport (ψ n) ⊆ Ω := by
    intro n
    refine subset_trans ?_ hδΩ
    refine closure_minimal ?_ isClosed_cthickening
    intro x hx
    obtain ⟨u, hu, s, hs', rfl⟩ := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) hx
    rw [(b n).support_normed_eq] at hu
    have hu' : ‖u‖ < (b n).rOut := by simpa using hu
    have hr : (b n).rOut ≤ δ := by
      show δ / ((n : ℝ) + 2) ≤ δ
      exact div_le_self hδ.le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    refine mem_cthickening_of_dist_le (u + s) s δ _ (subset_tsupport φ hs') ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    linarith
  have hder : ∀ n z v, fderiv ℝ (ψ n) z v =
      ((b n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fun y => fderiv ℝ φ y v) z := by
    intro n z v
    have h1 := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hloc n) hφ z
    rw [h1.fderiv]
    exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) (hloc n) (hc.fderiv ℝ)
      (hφ.continuous_fderiv one_ne_zero) z v
  have hψtend : ∀ z, Tendsto (fun n => ψ n z) atTop (𝓝 (φ z)) := fun z =>
    ContDiffBump.convolution_tendsto_right_of_continuous (φ := b) (l := atTop) (μ := μ) hlim_r
      hφ.continuous z
  have hdcont : ∀ v : E, Continuous fun y => fderiv ℝ φ y v := fun v =>
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψtend : ∀ z v, Tendsto (fun n => fderiv ℝ (ψ n) z v) atTop (𝓝 (fderiv ℝ φ z v)) := by
    intro z v
    simp only [hder]
    exact ContDiffBump.convolution_tendsto_right_of_continuous (φ := b) (l := atTop) (μ := μ)
      hlim_r (hdcont v) z
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have hMd : ∀ v : E, ∃ M : ℝ, ∀ y, |fderiv ℝ φ y v| ≤ M := by
    intro v
    obtain ⟨M, hM⟩ := (hdcont v).bounded_above_of_compact_support
      ((hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) (by simp))
    exact ⟨M, fun y => by simpa using hM y⟩
  have hterm : ∀ i, Tendsto (fun n => ∫ z in Ω, A i z * fderiv ℝ (ψ n) z (w i) ∂μ) atTop
      (𝓝 (∫ z in Ω, A i z * fderiv ℝ φ z (w i) ∂μ)) := by
    intro i
    obtain ⟨M, hM⟩ := hMd (w i)
    refine tendsto_weighted_integral (hA i) (C := M) ?_ ?_ (fun z => hdψtend z (w i))
    · intro n
      exact (((hψsm n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable
    · intro n z
      rw [hder]
      exact abs_convolution_normed_le (b n) μ hM z
  have hB' : Tendsto (fun n => ∫ z in Ω, B z * ψ n z ∂μ) atTop
      (𝓝 (∫ z in Ω, B z * φ z ∂μ)) := by
    refine tendsto_weighted_integral hB (C := Mφ) ?_ ?_ hψtend
    · exact fun n => (hψsm n).continuous.aestronglyMeasurable
    · intro n z
      exact abs_convolution_normed_le (b n) μ (fun x => by simpa using hMφ x) z
  have hsum := (tendsto_finsetSum Finset.univ (fun i _ => hterm i)).add hB'
  have hz : (fun n => ∑ i, (∫ z in Ω, A i z * fderiv ℝ (ψ n) z (w i) ∂μ) +
      ∫ z in Ω, B z * ψ n z ∂μ) = fun _ => 0 :=
    funext fun n => h (ψ n) (hψsm n) (hψcs n) (hψsub n)
  rw [hz] at hsum
  exact (tendsto_nhds_unique hsum tendsto_const_nhds)

end EinsteinFull.ParabolicBridge
