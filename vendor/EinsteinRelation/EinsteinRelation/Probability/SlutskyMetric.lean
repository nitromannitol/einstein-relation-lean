import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Slutsky's theorem with a pseudo-metric second factor

Mathlib's `MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` requires the
second factor to be a seminormed group, because its proof forms the difference `Y n - X n` and
measures it with a norm. Random time changes, viewed as elements of a space of continuous paths
with the compact-open distance, form only a pseudo-metric space. This module reruns the same
argument with `dist` in place of the norm of a difference. The first factor keeps the seminormed
group structure, so the statements match Mathlib's except for the second factor.

## Main statements

* `EinsteinRelation.prodMk_of_tendstoInMeasure_const_metric`: Slutsky's theorem for a pair whose
  second component is a pseudo-metric space. The product carries the maximum metric.
* `EinsteinRelation.continuous_comp_prodMk_of_tendstoInMeasure_const_metric`: the continuous
  mapping version of the previous statement.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {l : Filter ι}

set_option backward.isDefEq.respectTransparency.types false in
/-- Convergence in distribution is preserved under a perturbation whose distance to the original
tends to zero in probability. This is `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`
with `dist` in place of the norm of a difference, so the target only needs a pseudo-metric
structure. The convergence in probability hypothesis is stated for the real-valued measure of
the events `{ε ≤ dist (Y n ω) (X n ω)}`. -/
theorem tendstoInDistribution_of_dist_tendsto_zero
    {E : Type*} {mE : MeasurableSpace E} [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] [l.IsCountablyGenerated] {X : ι → Ω → E} (Y : ι → Ω → E) (Z : Ω → E)
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ)
    (hXY : ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ.real {ω | ε ≤ dist (Y n ω) (X n ω)}) l (𝓝 0))
    (hY : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution Y l Z (fun _ ↦ μ) μ := by
  have hZ : AEMeasurable Z μ := hXZ.aemeasurable_limit
  have hX : ∀ i, AEMeasurable (X i) μ := hXZ.forall_aemeasurable
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hY, hZ, ?_⟩
  -- We show convergence in distribution by verifying the convergence of integrals of any bounded
  -- Lipschitz function `F`
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ ω, F ω ∂(μ.map (Y n))) l (𝓝 (∫ ω, F ω ∂(μ.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  -- If `F` is 0-Lipschitz, then it is constant, and all integrals are equal to that constant
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip x₀
    simp only [← hF_lip, integral_const, smul_eq_mul]
    simpa using! tendsto_const_nhds
  -- now `F` is `L`-Lipschitz with `L > 0`
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in l, |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map Z)| < L * ε by
    intro ε hε
    convert! this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have hc : AEMeasurable (fun _ : Ω ↦ ε / 2) μ := measurable_const.aemeasurable
  have hdist (n : ι) : AEMeasurable (fun ω ↦ dist (Y n ω) (X n ω)) μ :=
    AEMeasurable.dist (hY n) (hX n)
  -- We cut the difference into three pieces, two of which are small by the convergence assumptions
  have h_le n : |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map Z)|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ.map Z)| := by
    refine (abs_sub_le (∫ ω, F ω ∂(μ.map (Y n))) (∫ ω, F ω ∂(μ.map (X n)))
      (∫ ω, F ω ∂(μ.map Z))).trans ?_
    gcongr
    -- `⊢ |∫ ω, F ω ∂(μ.map (Y n)) - ∫ ω, F ω ∂(μ.map (X n))|`
    -- `    ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}`
    -- We prove integrability of the functions involved to be able to manipulate the integrals.
    have h_int_Y : Integrable (fun x ↦ F (Y n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Y n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F x₀)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (X n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F x₀‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (X n a) x₀
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F x₀)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Y n a) - F (X n a)‖) μ := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    -- Now we prove the inequality
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Y n a) - F (X n a) ∂μ‖
    _ ≤ ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ := norm_integral_le_integral_norm _
    -- Either `dist (Y n x) (X n x)` is smaller than `ε / 2`, or it is not
    _ = ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ
        + ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, ‖F (Y n a) - F (X n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (hdist n) hc
    -- If it is smaller, we use the Lipschitz property of `F`
    -- If not, we use the boundedness of `F`.
    _ ≤ ∫ a in {x | dist (Y n x) (X n x) < ε / 2}, L * (ε / 2) ∂μ
        + ∫ a in {x | ε / 2 ≤ dist (Y n x) (X n x)}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (hdist n) hc
        · exact fun x hx ↦ by
            have h := hF_lip.dist_le_mul_of_le hx.le
            rwa [dist_eq_norm] at h
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert! hF_bounded _ _
    -- The goal is now a simple computation
    _ = L * (ε / 2) * μ.real {x | dist (Y n x) (X n x) < ε / 2}
        + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  -- We finally show that the right-hand side tends to `L * ε / 2`, which is smaller than `L * ε`
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ.map Z)|) l (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ dist (Y n ω) (X n ω)}
        + |∫ ω, F ω ∂(μ.map (X n)) - ∫ ω, F ω ∂(μ.map Z)|) l (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · exact hXY (ε / 2) (by positivity)
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using! hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- **Slutsky's theorem** with a pseudo-metric second factor: if `X n` converges in distribution
to `Z`, and `Y n` converges in probability to a constant `c`, then the pair `(X n, Y n)`
converges in distribution to `(Z, c)`. -/
theorem prodMk_of_tendstoInMeasure_const_metric
    {E : Type*} {mE : MeasurableSpace E} [SeminormedAddCommGroup E] [SecondCountableTopology E]
    [BorelSpace E] {E' : Type*} {mE' : MeasurableSpace E'} [PseudoMetricSpace E']
    [SecondCountableTopology E'] [BorelSpace E'] [l.IsCountablyGenerated]
    (X : ι → Ω → E) (Y : ι → Ω → E') (Z : Ω → E)
    {c : E'} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ)
    (hY : TendstoInMeasure μ (fun n ↦ Y n) l (fun _ ↦ c))
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω ↦ (X n ω, Y n ω)) l (fun ω ↦ (Z ω, c)) (fun _ ↦ μ) μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := hXZ.forall_aemeasurable
  have hZ : AEMeasurable Z μ := hXZ.aemeasurable_limit
  -- The maximum metric on the product measures the distance from `(x, y)` to `(x, c)` by
  -- the distance from `y` to `c`.
  have hdist (n : ι) (ω : Ω) : dist (X n ω, Y n ω) (X n ω, c) = dist (Y n ω) c := by
    show max (dist (X n ω) (X n ω)) (dist (Y n ω) c) = dist (Y n ω) c
    rw [dist_self]
    exact max_eq_right dist_nonneg
  refine tendstoInDistribution_of_dist_tendsto_zero (X := fun n ω ↦ (X n ω, c))
    (Y := fun n ω ↦ (X n ω, Y n ω)) (Z := fun ω ↦ (Z ω, c)) (μ := μ) (l := l) ?_ ?_
    (by fun_prop)
  · exact hXZ.continuous_comp (g := fun x ↦ (x, c)) (by fun_prop)
  · intro ε hε
    have hYc := (tendstoInMeasure_iff_measureReal_dist.mp hY) ε hε
    simpa only [hdist] using hYc

/-- **Slutsky's theorem** for a continuous function, with a pseudo-metric second factor: if `X n`
converges in distribution to `Z`, `Y n` converges in probability to a constant `c`, and `g` is
continuous, then `g (X n, Y n)` converges in distribution to `g (Z, c)`. -/
theorem continuous_comp_prodMk_of_tendstoInMeasure_const_metric
    {E : Type*} {mE : MeasurableSpace E} [SeminormedAddCommGroup E] [SecondCountableTopology E]
    [BorelSpace E] {E' F : Type*} {mE' : MeasurableSpace E'} [PseudoMetricSpace E']
    [SecondCountableTopology E'] [BorelSpace E'] [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] {g : E × E' → F} (hg : Continuous g) [l.IsCountablyGenerated]
    {X : ι → Ω → E} {Y : ι → Ω → E'} {Z : Ω → E} {c : E'}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ)
    (hY_tendsto : TendstoInMeasure μ (fun n ↦ Y n) l (fun _ ↦ c))
    (hY : ∀ i, AEMeasurable (Y i) μ) :
    TendstoInDistribution (fun n ω ↦ g (X n ω, Y n ω)) l (fun ω ↦ g (Z ω, c)) (fun _ ↦ μ) μ := by
  refine TendstoInDistribution.continuous_comp hg ?_
  exact prodMk_of_tendstoInMeasure_const_metric X Y Z hXZ hY_tendsto hY

end EinsteinRelation
