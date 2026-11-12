import EinsteinRelation.Correctors.AKMHeatKernelUniformTime
import EinsteinRelation.Correctors.AKMHeatKernelPairing
import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Correctors.AKMHeatKernelTimeContinuity
import EinsteinRelation.Correctors.ProbabilityKernelUniformError

/-! # Gaussian probability kernels

Source: `paper/main.tex:777–784,842`; AKM Proposition E.1, the bound (E.7)
and the mass and symmetry properties, printed pp. 500–501. These
positive-time properties of E.1 kernels survive pointwise limits. They are
all that the pairing endpoints use for a kernel that is not known to solve
the equation.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Positive-time continuity, positivity, symmetry, unit mass and the
Gaussian bound (E.7) of AKM Proposition E.1, with the constant function `C`
of (E.7). Source: AKM Proposition E.1, pp. 500–501. -/
def IsGaussianProbabilityKernel {d : ℕ} (K : ℝ) (C : ℝ → ℝ)
    (P : ℝ → Vec d → Vec d → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ × (Vec d × Vec d) => P z.1 z.2.1 z.2.2)
    (Set.Ioi 0 ×ˢ Set.univ) ∧
  (∀ t, 0 < t → ∀ x y, 0 ≤ P t x y) ∧
  (∀ t, 0 < t → ∀ x y, P t x y = P t y x) ∧
  (∀ t, 0 < t → ∀ x,
    Integrable (P t x) volume ∧ (∫ y, P t x y ∂volume) = 1 ∧
    Integrable (fun y => P t y x) volume ∧ (∫ y, P t y x ∂volume) = 1) ∧
  ∀ α : ℝ, 0 < α → α < K⁻¹ → ∀ t : ℝ, 0 < t → ∀ x y : Vec d,
    |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
      Real.exp (-α * euclideanSq (x - y) / (4 * t))

/-- Every E.1 kernel is a Gaussian probability kernel with the same
constant function. Source: AKM Proposition E.1, pp. 500–501. -/
theorem _root_.EinsteinRelation.External.AKM.HeatKernelProperties.isGaussianProbabilityKernel
    {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C) : IsGaussianProbabilityKernel K C P :=
  ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    fun α hα hαK t ht x y => (h.2.2.2.2.2.2.2.1 α hα hαK t ht x y).1⟩

namespace IsGaussianProbabilityKernel

variable {d : ℕ} {K : ℝ} {C : ℝ → ℝ} {P : ℝ → Vec d → Vec d → ℝ}

theorem constant_nonneg (h : IsGaussianProbabilityKernel K C P)
    {α : ℝ} (hα : 0 < α) (hαK : α < K⁻¹) : 0 ≤ C α := by
  have hh := h.2.2.2.2 α hα hαK 1 zero_lt_one 0 0
  simp only [Real.one_rpow, mul_one, sub_self, euclideanSq, dot, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_div, Real.exp_zero] at hh
  exact (abs_nonneg _).trans hh

/-- The Gaussian bound is uniform after any positive time. -/
theorem uniform_bound (h : IsGaussianProbabilityKernel K C P) (hK : 0 < K)
    {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, a ≤ t → ∀ x y : Vec d, |P t x y| ≤ B := by
  let α : ℝ := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hαK : α < K⁻¹ := half_lt_self (inv_pos.mpr hK)
  have hC := h.constant_nonneg hα hαK
  refine ⟨C α * a ^ (-(d : ℝ) / 2), mul_nonneg hC (Real.rpow_nonneg ha.le _), ?_⟩
  intro t ht x y
  have ht0 : 0 < t := ha.trans_le ht
  have hsq : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg ((x-y) j)
  have hexp : Real.exp (-α * euclideanSq (x-y) / (4*t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) hsq) (by positivity)
  calc
    |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
        Real.exp (-α * euclideanSq (x-y) / (4*t)) := h.2.2.2.2 α hα hαK t ht0 x y
    _ ≤ C α * t ^ (-(d : ℝ) / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hC (Real.rpow_nonneg ht0.le _))
    _ ≤ C α * a ^ (-(d : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow_of_nonpos ha ht
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))

theorem space_continuous (h : IsGaussianProbabilityKernel K C P)
    {t : ℝ} (ht : 0 < t) (y : Vec d) : Continuous (fun x => P t x y) := by
  apply continuousOn_univ.mp
  exact h.1.comp
    ((continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn)
    (fun _ _ => ⟨ht, Set.mem_univ _⟩)

theorem time_continuousOn (h : IsGaussianProbabilityKernel K C P) (x y : Vec d) :
    ContinuousOn (fun t => P t x y) (Set.Ioi 0) :=
  h.1.comp ((continuous_id.prodMk (continuous_const :
    Continuous (fun _ : ℝ => (x,y)))).continuousOn)
    (fun _ ht => ⟨ht, Set.mem_univ _⟩)

/-- Each positive-time slice in the first variable is square integrable. -/
theorem slice_memLp (h : IsGaussianProbabilityKernel K C P) (hK : 0 < K)
    {t : ℝ} (ht : 0 < t) (y : Vec d) : MemLp (fun x => P t x y) 2 volume := by
  obtain ⟨B, _, hb⟩ := h.uniform_bound hK ht
  have hi := (h.2.2.2.1 t ht y).2.2.1
  have hm := hi.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hi.const_mul B).mono' (hm.pow 2)
  filter_upwards with x
  have hx := hb t le_rfl x y
  have hp := h.2.1 t ht x y
  change ‖P t x y ^ 2‖ ≤ B * P t x y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two, mul_comm B]
  exact mul_le_mul_of_nonneg_left ((le_abs_self (P t x y)).trans hx) hp

/-- Positive-time continuity is uniform in the free spatial variable, by
the Gaussian tail bound. Source: AKM (E.7). -/
theorem uniform_time_continuity (h : IsGaussianProbabilityKernel K C P)
    (hK : 0 < K) (T : ℝ) (hT : 0 < T) (y : Vec d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 T, ∀ x : Vec d,
      |P t x y - P T x y| < ε := by
  intro ε hε
  obtain ⟨α, hα, hαK⟩ : ∃ α : ℝ, 0 < α ∧ α < K⁻¹ :=
    ⟨K⁻¹ / 2, half_pos (inv_pos.mpr hK), half_lt_self (inv_pos.mpr hK)⟩
  have hb := h.2.2.2.2 α hα hαK
  have hC0 := h.constant_nonneg hα hαK
  have hF : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y) (Set.Ioi 0 ×ˢ Set.univ) :=
    h.1.comp ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨hz.1, Set.mem_univ _⟩)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = α / (8 * T) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact div_pos hα (by linarith)
  have hT8 : (8 * T) ≠ 0 := (by linarith : (0 : ℝ) < 8 * T).ne'
  have hc8 : c * (8 * T) = α := by rw [hcdef]; field_simp
  have hct : ∀ t : ℝ, t < 2 * T → c * (4 * t) ≤ α := by
    intro t ht
    rw [← hc8]
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  have htail : ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, T / 2 < t → t < 2 * T →
      ∀ x : Vec d, x ∉ Metric.closedBall y R → |P t x y| < ε / 2 := by
    have hlim : Tendsto (fun R : ℝ => C α * (T / 2) ^ (-(d : ℝ) / 2) * Real.exp (-(c * R ^ 2)))
        atTop (𝓝 0) := by
      have hsq : Tendsto (fun R : ℝ => c * R ^ 2) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc (tendsto_pow_atTop two_ne_zero)
      have h0 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq).const_mul
        (C α * (T / 2) ^ (-(d : ℝ) / 2))
      rw [mul_zero] at h0
      exact h0
    obtain ⟨R, hR0, hRlt⟩ : ∃ R : ℝ, 0 ≤ R ∧
        C α * (T / 2) ^ (-(d : ℝ) / 2) * Real.exp (-(c * R ^ 2)) < ε / 2 := by
      obtain ⟨R, hR⟩ := ((hlim.eventually (gt_mem_nhds (half_pos hε))).and
        (eventually_ge_atTop (0 : ℝ))).exists
      exact ⟨R, hR.2, hR.1⟩
    refine ⟨R, hR0, fun t ht1 ht2 x hx => ?_⟩
    have ht0 : 0 < t := by linarith
    have hq := akm_heatKernel_sq_le_euclideanSq_of_not_mem_closedBall x y hR0 hx
    have hpow : t ^ (-(d : ℝ) / 2) ≤ (T / 2) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (half_pos hT) ht1.le
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))
    have hexp : Real.exp (-α * euclideanSq (x - y) / (4 * t)) ≤ Real.exp (-(c * R ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * t)]
      nlinarith [mul_le_mul_of_nonneg_left (hct t ht2) (sq_nonneg R),
        mul_le_mul_of_nonneg_left hq hα.le]
    have hbound : |P t x y| ≤ C α * (T / 2) ^ (-(d : ℝ) / 2) * Real.exp (-(c * R ^ 2)) :=
      (hb t ht0 x y).trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0) hexp
        (Real.exp_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg (half_pos hT).le _)))
    exact lt_of_le_of_lt hbound hRlt
  obtain ⟨R, hR0, htail'⟩ := htail
  have hKc : IsCompact (Set.Icc (T / 2) (2 * T) ×ˢ Metric.closedBall y R) :=
    isCompact_Icc.prod (isCompact_closedBall y R)
  have hFc : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y)
      (Set.Icc (T / 2) (2 * T) ×ˢ Metric.closedBall y R) :=
    hF.mono fun z hz => ⟨lt_of_lt_of_le (half_pos hT) hz.1.1, Set.mem_univ _⟩
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hFc) ε hε
  filter_upwards [Ioo_mem_nhds (by linarith : T / 2 < T) (by linarith : T < 2 * T),
    Metric.ball_mem_nhds T hδ] with t ht1 ht2 x
  by_cases hx : x ∈ Metric.closedBall y R
  · have hdist : dist (t, x) (T, x) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp ht2) (by simpa using hδ)
    have htI : t ∈ Set.Icc (T / 2) (2 * T) := ⟨ht1.1.le, ht1.2.le⟩
    have hTI : T ∈ Set.Icc (T / 2) (2 * T) := ⟨by linarith, by linarith⟩
    have hU := hδP (t, x) ⟨htI, hx⟩ (T, x) ⟨hTI, hx⟩ hdist
    rw [Real.dist_eq] at hU
    exact hU
  · have h1 := htail' t ht1.1 ht1.2 x hx
    have h2 := htail' T (by linarith) (by linarith) x hx
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    rw [abs_lt]
    constructor <;> linarith

end IsGaussianProbabilityKernel

/-- Heat smoothing of a bounded continuous function converges to its
value at each point. -/
theorem tendsto_heatKernelConvolution_zero_of_bounded {d : ℕ} {g : Vec d → ℝ}
    (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (y : Vec d) :
    Tendsto (fun t => heatKernelConvolution t g y) (𝓝[>] 0) (𝓝 (g y)) := by
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Vec d))) (l := 𝓝[>] (0 : ℝ))
    (F := fun t z => euclideanHeatKernel 1 z * g (Real.sqrt t • z + y))
    (f := fun z => euclideanHeatKernel 1 z * g y)
    (fun z => euclideanHeatKernel 1 z * B)
    (Eventually.of_forall fun t => ((continuous_euclideanHeatKernel 1).mul
      (hg.comp ((continuous_const.smul continuous_id).add continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ae_of_all _ fun z => by
      rw [norm_mul, Real.norm_of_nonneg (euclideanHeatKernel_nonneg zero_le_one _)]
      exact mul_le_mul_of_nonneg_left (hB _) (euclideanHeatKernel_nonneg zero_le_one _))
    ((integrable_euclideanHeatKernel (d := d) zero_lt_one).mul_const B)
    (ae_of_all _ fun z => by
      have ht : Tendsto (fun t : ℝ => Real.sqrt t • z + y) (𝓝[>] 0) (𝓝 y) := by
        simpa using ((Real.continuous_sqrt.tendsto 0).mono_left inf_le_left).smul_const z
          |>.add_const y
      exact tendsto_const_nhds.mul (hg.continuousAt.tendsto.comp ht))
  simp only [integral_mul_const, integral_euclideanHeatKernel zero_lt_one, one_mul] at hdom
  exact hdom.congr' (eventually_mem_nhdsWithin.mono fun _ ht =>
    (heatKernelConvolution_eq_scaled ht g y).symm)

namespace IsGaussianProbabilityKernel

variable {d : ℕ} {K : ℝ} {C : ℝ → ℝ} {P : ℝ → Vec d → Vec d → ℝ}

/-- The Gaussian majorant of (E.7) is a multiple of the Euclidean heat
kernel at time `t/α`. -/
theorem _root_.EinsteinRelation.Correctors.gaussian_majorant_eq_euclideanHeatKernel
    {α t : ℝ} (hα : 0 < α) (ht : 0 < t) (w : Vec d) :
    t ^ (-(d : ℝ) / 2) * Real.exp (-α * euclideanSq w / (4 * t)) =
      (4 * Real.pi / α) ^ ((d : ℝ) / 2) * euclideanHeatKernel (t / α) w := by
  have hc : 0 < 4 * Real.pi / α := by positivity
  have hpow : t ^ (-(d : ℝ) / 2) =
      (4 * Real.pi / α) ^ ((d : ℝ) / 2) * (4 * Real.pi * (t / α)) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (t / α) = (4 * Real.pi / α) * t by ring,
      Real.mul_rpow hc.le ht.le, ← mul_assoc, ← Real.rpow_add hc,
      show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_mul]
  have hexp : -α * euclideanSq w / (4 * t) = -(euclideanSq w) / (4 * (t / α)) := by
    field_simp
  rw [hpow, hexp]
  unfold euclideanHeatKernel
  ring

/-- The Gaussian bound (E.7) dominates the kernel by a scaled Euclidean
heat kernel. -/
theorem abs_le_euclideanHeatKernel (h : IsGaussianProbabilityKernel K C P)
    {α : ℝ} (hα : 0 < α) (hαK : α < K⁻¹) {t : ℝ} (ht : 0 < t) (x y : Vec d) :
    |P t x y| ≤ C α * (4 * Real.pi / α) ^ ((d : ℝ) / 2) *
      euclideanHeatKernel (t / α) (x - y) := by
  have hb := h.2.2.2.2 α hα hαK t ht x y
  rw [mul_assoc, gaussian_majorant_eq_euclideanHeatKernel hα ht] at hb
  linarith only [hb]

/-- Without the Gaussian factor, the bound (E.7) is a power of time. -/
theorem abs_le_rpow (h : IsGaussianProbabilityKernel K C P)
    {α : ℝ} (hα : 0 < α) (hαK : α < K⁻¹) {t : ℝ} (ht : 0 < t) (x y : Vec d) :
    |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) := by
  have hsq : 0 ≤ euclideanSq (x-y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg ((x-y) j)
  have hexp : Real.exp (-α * euclideanSq (x-y) / (4*t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) hsq) (by positivity)
  calc
    |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
        Real.exp (-α * euclideanSq (x-y) / (4*t)) := h.2.2.2.2 α hα hαK t ht x y
    _ ≤ C α * t ^ (-(d : ℝ) / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
        (mul_nonneg (h.constant_nonneg hα hαK) (Real.rpow_nonneg ht.le _))

theorem space_continuous_right (h : IsGaussianProbabilityKernel K C P)
    {t : ℝ} (ht : 0 < t) (x : Vec d) : Continuous (fun y => P t x y) := by
  apply continuousOn_univ.mp
  exact h.1.comp
    ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
    (fun _ _ => ⟨ht, Set.mem_univ _⟩)

/-- On a positive-time strip, the scalar energy is at most the strip length
times the uniform bound, since the kernel has unit mass. -/
theorem strip_sq_integral_le (h : IsGaussianProbabilityKernel K C P)
    {α : ℝ} (hα : 0 < α) (hαK : α < K⁻¹) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (y : Vec d) :
    (∫ z in Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)), P z.1 z.2 y ^ 2) ≤
      (b - a) * (C α * a ^ (-(d : ℝ) / 2)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioo a b)
  let μ : Measure (ℝ × Vec d) := ν.prod volume
  have hμ : μ = volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d))) := by
    change (volume.restrict (Set.Ioo a b)).prod volume =
      ((volume : Measure ℝ).prod volume).restrict (Set.Ioo a b ×ˢ Set.univ)
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hc : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y) (Set.Ioo a b ×ˢ Set.univ) :=
    h.1.comp ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨ha.trans hz.1.1, Set.mem_univ _⟩)
  have hm : AEStronglyMeasurable (fun z : ℝ × Vec d => P z.1 z.2 y) μ := by
    rw [hμ]
    exact hc.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have ht : ∀ᵐ t ∂ν, 0 < t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ha.trans ht.1
  haveI : IsFiniteMeasure ν := by dsimp only [ν]; infer_instance
  have hi : Integrable (fun z : ℝ × Vec d => P z.1 z.2 y) μ := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [ht] with t ht
      exact (h.2.2.2.1 t ht y).2.2.1
    · apply (integrable_const (1 : ℝ)).congr
      filter_upwards [ht] with t ht
      have heq : (∫ x, ‖P t x y‖ ∂volume) = 1 := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (h.2.1 t ht _ _)] using
          (h.2.2.2.1 t ht y).2.2.2
      exact heq.symm
  have hbound : ∀ᵐ z ∂μ, P z.1 z.2 y ^ 2 ≤ (C α * a ^ (-(d : ℝ) / 2)) * P z.1 z.2 y := by
    rw [hμ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with z hz
    have hz0 : 0 < z.1 := ha.trans hz.1.1
    have hp := h.2.1 z.1 hz0 z.2 y
    have hpow : z.1 ^ (-(d : ℝ) / 2) ≤ a ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos ha hz.1.1.le
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))
    have hle : P z.1 z.2 y ≤ C α * a ^ (-(d : ℝ) / 2) :=
      (le_abs_self _).trans ((h.abs_le_rpow hα hαK hz0 z.2 y).trans
        (mul_le_mul_of_nonneg_left hpow (h.constant_nonneg hα hαK)))
    rw [sq]
    exact mul_le_mul_of_nonneg_right hle hp
  have hint2 : Integrable (fun z : ℝ × Vec d => P z.1 z.2 y ^ 2) μ :=
    (hi.const_mul (C α * a ^ (-(d : ℝ) / 2))).mono' (hm.pow 2) (by
      filter_upwards [hbound] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz)
  have hmass : (fun t => ∫ x, P t x y ∂volume) =ᵐ[ν] fun _ => (1 : ℝ) := by
    filter_upwards [ht] with t ht
    exact (h.2.2.2.1 t ht y).2.2.2
  rw [← hμ]
  calc
    (∫ z, P z.1 z.2 y ^ 2 ∂μ) ≤ ∫ z, (C α * a ^ (-(d : ℝ) / 2)) * P z.1 z.2 y ∂μ :=
      integral_mono_ae hint2 (hi.const_mul _) hbound
    _ = (C α * a ^ (-(d : ℝ) / 2)) * ∫ t, (∫ x, P t x y ∂volume) ∂ν := by
      rw [integral_const_mul, integral_prod _ hi]
    _ = (C α * a ^ (-(d : ℝ) / 2)) * (b - a) := by
      rw [integral_congr_ae hmass, integral_const, smul_eq_mul, mul_one]
      congr 1
      simp [ν, Measure.real, Real.volume_Ioo, hab]
    _ = (b - a) * (C α * a ^ (-(d : ℝ) / 2)) := mul_comm _ _

/-- The kernel concentrates at the diagonal: against bounded continuous
data it converges to the value at the point. Source: AKM (E.7) and the
unit mass in Proposition E.1. -/
theorem tendsto_integral_mul_of_bounded_continuous
    (h : IsGaussianProbabilityKernel K C P) (hK : 0 < K)
    {g : Vec d → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, |g z| ≤ M) (x : Vec d) :
    Tendsto (fun s => ∫ z, P s z x * g z) (𝓝[>] 0) (𝓝 (g x)) := by
  let α : ℝ := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hαK : α < K⁻¹ := half_lt_self (inv_pos.mpr hK)
  let c := C α * (4 * Real.pi / α) ^ ((d : ℝ) / 2)
  have he : Continuous (fun z => |g z - g x|) := (hg.sub continuous_const).abs
  have heB : ∀ z, ‖|g z - g x|‖ ≤ 2 * M := fun z => by
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (by linarith [hM z, hM x])
  have hτ : Tendsto (fun s : ℝ => s / α) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_id.div_const α).tendsto 0).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact div_pos hs hα
  have hlim : Tendsto (fun s => c * heatKernelConvolution (s / α) (fun z => |g z - g x|) x)
      (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((tendsto_heatKernelConvolution_zero_of_bounded he heB x).comp hτ).const_mul c
    convert h0 using 2
    simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 0 < s := hs
  have hi := (h.2.2.2.1 s hs x).2.2.1
  have hig : Integrable (fun z => P s z x * g z) volume :=
    hi.mul_bdd hg.aestronglyMeasurable (ae_of_all _ fun z => (Real.norm_eq_abs _).le.trans (hM z))
  have hie : Integrable (fun z => P s z x * |g z - g x|) volume :=
    hi.mul_bdd he.aestronglyMeasurable (ae_of_all _ heB)
  have hsub : (∫ z, P s z x * g z) - g x = ∫ z, P s z x * (g z - g x) := by
    have h1 : (∫ z, P s z x * g x) = g x := by
      rw [integral_mul_const, (h.2.2.2.1 s hs x).2.2.2, one_mul]
    have h2 := integral_sub hig (hi.mul_const (g x))
    rw [h1] at h2
    rw [← h2]
    congr 1
    funext z
    ring
  have hτ0 : s / α ≠ 0 := (div_pos hs hα).ne'
  have hφi : Integrable (fun z => euclideanHeatKernel (s / α) (z - x)) volume :=
    (integrable_euclideanHeatKernel (div_pos hs hα)).comp_sub_right x
  have hbi : Integrable (fun z => |g z - g x| * euclideanHeatKernel (s / α) (z - x)) volume := by
    have := hφi.bdd_mul he.aestronglyMeasurable (ae_of_all _ heB)
    exact this
  rw [hsub, heatKernelConvolution, if_neg hτ0, ← integral_const_mul]
  calc
    ‖∫ z, P s z x * (g z - g x)‖ ≤ ∫ z, ‖P s z x * (g z - g x)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ z, P s z x * |g z - g x| := by
      congr 1
      funext z
      rw [norm_mul, Real.norm_of_nonneg (h.2.1 s hs z x), Real.norm_eq_abs]
    _ ≤ ∫ z, c * (|g z - g x| * euclideanHeatKernel (s / α) (z - x)) := by
      apply integral_mono hie (hbi.const_mul c)
      intro z
      have hp := (le_abs_self _).trans (h.abs_le_euclideanHeatKernel hα hαK hs z x)
      calc
        P s z x * |g z - g x| ≤
            (c * euclideanHeatKernel (s / α) (z - x)) * |g z - g x| :=
          mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ = c * (|g z - g x| * euclideanHeatKernel (s / α) (z - x)) := by ring

/-- The pairing of two Gaussian probability kernels is continuous between
its endpoints. Source: AKM Proposition E.1 proof, p. 510. -/
theorem pairing_continuousOn {Q : ℝ → Vec d → Vec d → ℝ} {C' : ℝ → ℝ}
    (hP : IsGaussianProbabilityKernel K C P) (hQ : IsGaussianProbabilityKernel K C' Q)
    (hK : 0 < K) (T : ℝ) (x y : Vec d) :
    ContinuousOn (fun s => ∫ z, P s z y * Q (T-s) z x ∂volume) (Set.Ioo 0 T) := by
  intro s hs
  let l := nhdsWithin s (Set.Ioo 0 T)
  have hsT : 0 < T-s := sub_pos.mpr hs.2
  obtain ⟨B, _, hB⟩ := hQ.uniform_bound hK hsT
  have hqc := hQ.space_continuous hsT x
  have hfixed := akm_mass_one_kernel_average_continuousOn
    (fun z => hP.time_continuousOn z y)
    (fun t ht => (hP.2.2.2.1 t ht y).2.2.1)
    (fun t ht z => hP.2.1 t ht z y)
    (fun t ht => (hP.2.2.2.1 t ht y).2.2.2)
    hqc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hB (T-s) le_rfl z x))
  have hfixedlim : Tendsto (fun r => ∫ z, P r z y * Q (T-s) z x ∂volume) l
      (𝓝 (∫ z, P s z y * Q (T-s) z x ∂volume)) :=
    ((hfixed s hs.1).mono (fun _ hr => hr.1)).tendsto
  have hsub : Tendsto (fun r : ℝ => T-r) l (𝓝 (T-s)) :=
    tendsto_const_nhds.sub continuousWithinAt_id.tendsto
  have hp : ∀ᶠ r in l, Integrable (fun z => P r z y) volume ∧
      (∀ᵐ z ∂volume, 0 ≤ P r z y) ∧ (∫ z, P r z y ∂volume) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ⟨(hP.2.2.2.1 r hr.1 y).2.2.1,
      Filter.Eventually.of_forall (fun z => hP.2.1 r hr.1 z y),
      (hP.2.2.2.1 r hr.1 y).2.2.2⟩
  have he : ∀ᶠ r in l,
      AEStronglyMeasurable (fun z => Q (T-r) z x - Q (T-s) z x) volume := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hQ.space_continuous (sub_pos.mpr hr.2) x).aestronglyMeasurable.sub
      hqc.aestronglyMeasurable
  have herr := akm_probability_kernel_uniform_error hp he (by
    intro ε hε
    exact hsub.eventually (hQ.uniform_time_continuity hK (T-s) hsT x ε hε))
  have hlim := herr.add hfixedlim
  apply (show Tendsto _ l _ from ?_)
  simpa only [zero_add] using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hi : Integrable (fun z => P r z y * Q (T-r) z x) volume :=
      (hP.slice_memLp hK hr.1 y).integrable_mul (hQ.slice_memLp hK (sub_pos.mpr hr.2) x)
    have hi₀ : Integrable (fun z => P r z y * Q (T-s) z x) volume :=
      (hP.slice_memLp hK hr.1 y).integrable_mul (hQ.slice_memLp hK hsT x)
    have heq : (∫ z, P r z y * (Q (T-r) z x-Q (T-s) z x) ∂volume) =
        (∫ z, P r z y * Q (T-r) z x ∂volume) -
          ∫ z, P r z y * Q (T-s) z x ∂volume := by
      rw [← integral_sub hi hi₀]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => mul_sub _ _ _
    rw [heq]
    ring)

/-- At the initial endpoint the pairing of two Gaussian probability kernels
converges to the second kernel. Source: AKM Proposition E.1 proof, p. 510. -/
theorem pairing_initial {Q : ℝ → Vec d → Vec d → ℝ} {C' : ℝ → ℝ}
    (hP : IsGaussianProbabilityKernel K C P) (hQ : IsGaussianProbabilityKernel K C' Q)
    (hK : 0 < K) {T : ℝ} (hT : 0 < T) (x y : Vec d) :
    Tendsto (fun s => ∫ z, P s z y * Q (T-s) z x ∂volume)
      (𝓝[>] 0) (𝓝 (Q T y x)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hlt : ∀ᶠ s in l, s < T := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)
  have hsub : Tendsto (fun s : ℝ => T-s) l (𝓝 T) := by
    have hid : Tendsto (fun s : ℝ => s) l (𝓝 0) := continuousWithinAt_id.tendsto
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => T) l (𝓝 T)).sub hid
  have hqc := hQ.space_continuous hT x
  obtain ⟨B, _, hB⟩ := hQ.uniform_bound hK hT
  have hini := hP.tendsto_integral_mul_of_bounded_continuous hK hqc
    (fun z => hB T le_rfl z x) y
  have hp : ∀ᶠ s in l, Integrable (fun z => P s z y) volume ∧
      (∀ᵐ z ∂volume, 0 ≤ P s z y) ∧ (∫ z, P s z y ∂volume) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨(hP.2.2.2.1 s hs y).2.2.1,
      Filter.Eventually.of_forall (fun z => hP.2.1 s hs z y),
      (hP.2.2.2.1 s hs y).2.2.2⟩
  have he : ∀ᶠ s in l,
      AEStronglyMeasurable (fun z => Q (T-s) z x - Q T z x) volume := by
    filter_upwards [hlt] with s hs
    exact (hQ.space_continuous (sub_pos.mpr hs) x).aestronglyMeasurable.sub
      hqc.aestronglyMeasurable
  have herr := akm_probability_kernel_uniform_error hp he (by
    intro ε hε
    exact hsub.eventually (hQ.uniform_time_continuity hK T hT x ε hε))
  have hlim := herr.add hini
  simpa only [zero_add] using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin, hlt] with s hs hsT
    have hi : Integrable (fun z => P s z y * Q (T-s) z x) volume :=
      (hP.slice_memLp hK hs y).integrable_mul (hQ.slice_memLp hK (sub_pos.mpr hsT) x)
    have hi₀ : Integrable (fun z => P s z y * Q T z x) volume :=
      (hP.slice_memLp hK hs y).integrable_mul (hQ.slice_memLp hK hT x)
    have heq : (∫ z, P s z y * (Q (T-s) z x-Q T z x) ∂volume) =
        (∫ z, P s z y * Q (T-s) z x ∂volume) -
          ∫ z, P s z y * Q T z x ∂volume := by
      rw [← integral_sub hi hi₀]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => mul_sub _ _ _
    rw [heq]
    ring)

end IsGaussianProbabilityKernel

end EinsteinRelation.Correctors
