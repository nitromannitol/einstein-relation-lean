import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Locally uniform scaling limit of an inverse clock

Deterministic input to the covariance half of the time-change identities
(`paper/main.tex`, lines 228–233). For an order isomorphism `A` of `ℝ≥0` with
`A t / t → m > 0`, the rescaled inverses `ε ^ 2 * A⁻¹(ε⁻¹ ^ 2 * t)` converge to `t / m`
locally uniformly as `ε → 0⁺`. The statement is for an arbitrary order isomorphism, so it
applies to the physical clock `physicalPathClockOrderIso`.

The slope `A⁻¹ s / s` tends to `m⁻¹` at infinity. For `t ≥ δ` the rescaled time
`ε⁻¹ ^ 2 * t` is large, so the slope estimate applies. For `t ≤ δ` monotonicity of `A⁻¹`
bounds the rescaled value by its value at `δ`, which the pointwise limit at `δ` controls.
-/

open Filter Topology
open scoped NNReal

namespace EinsteinRelation

/-- The inverse of a linearly growing order isomorphism has slope `m⁻¹` at infinity. -/
private lemma inverse_slope_tendsto {A : ℝ≥0 ≃o ℝ≥0} {m : ℝ} (hm : 0 < m)
    (hA : Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop (𝓝 m)) :
    Tendsto (fun s : ℝ≥0 => (A.symm s : ℝ) / (s : ℝ)) atTop (𝓝 m⁻¹) := by
  have hBtop : Tendsto (fun s : ℝ≥0 => A.symm s) atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun b => ⟨A b, fun s hs => ?_⟩
    exact A.le_symm_apply.mpr hs
  have h1 : Tendsto (fun s : ℝ≥0 => (A (A.symm s) : ℝ) / ((A.symm s : ℝ≥0) : ℝ)) atTop
      (𝓝 m) :=
    hA.comp hBtop
  refine Tendsto.congr (fun s => ?_) (h1.inv₀ hm.ne')
  show ((A (A.symm s) : ℝ) / ((A.symm s : ℝ≥0) : ℝ))⁻¹ = (A.symm s : ℝ) / (s : ℝ)
  rw [A.apply_symm_apply, inv_div]

/-- Rescaling identity: for `ε > 0` and `t ≠ 0`, the rescaled value `ε ^ 2 * B (ε⁻¹ ^ 2 * t)`
equals `t` times the slope `B s / s` at the rescaled time `s = ε⁻¹ ^ 2 * t`. -/
private lemma scaled_inverse_eq (B : ℝ≥0 → ℝ≥0) {ε : ℝ} (hε : 0 < ε) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ε ^ 2 * (B ((ε⁻¹ ^ 2).toNNReal * t) : ℝ) =
      (t : ℝ) * ((B ((ε⁻¹ ^ 2).toNNReal * t) : ℝ) / (((ε⁻¹ ^ 2).toNNReal * t : ℝ≥0) : ℝ)) := by
  have hs : (((ε⁻¹ ^ 2).toNNReal * t : ℝ≥0) : ℝ) = ε⁻¹ ^ 2 * (t : ℝ) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal (ε⁻¹ ^ 2) (sq_nonneg ε⁻¹)]
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hε' : ε ≠ 0 := hε.ne'
  rw [hs]
  field_simp
  try ring

/-- Scalar estimate: if `t ≤ T + 1` and `|x| < η / (T + 1)`, then `t * |x| < η`. -/
private lemma mul_abs_lt_of_le_of_abs_lt {t T η x : ℝ} (htT : t ≤ T + 1) (hT : 0 < T + 1)
    (hx : |x| < η / (T + 1)) : t * |x| < η := by
  have hT' : T + 1 ≠ 0 := hT.ne'
  calc t * |x| ≤ (T + 1) * |x| := mul_le_mul_of_nonneg_right htT (abs_nonneg x)
    _ < (T + 1) * (η / (T + 1)) := mul_lt_mul_of_pos_left hx hT
    _ = η := mul_div_cancel₀ η hT'

/-- Locally uniform scaling limit of the inverse of a linearly growing order isomorphism:
`ε ^ 2 * A⁻¹(ε⁻¹ ^ 2 * t) → t / m` as `ε → 0⁺`, locally uniformly in `t ∈ ℝ≥0`. -/
theorem inverse_scaling_tendsto_locallyUniformly {A : ℝ≥0 ≃o ℝ≥0} {m : ℝ} (hm : 0 < m)
    (hA : Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop (𝓝 m)) :
    TendstoLocallyUniformly
      (fun (ε : ℝ) (t : ℝ≥0) => ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * t) : ℝ))
      (fun t => (t : ℝ) / m) (𝓝[>] 0) := by
  have hslope := inverse_slope_tendsto hm hA
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  -- The rescaled time `ε⁻¹ ^ 2 * δ` diverges as `ε → 0⁺`.
  have hc : ∀ δ : ℝ≥0, 0 < δ →
      Tendsto (fun ε : ℝ => (ε⁻¹ ^ 2).toNNReal * δ) (𝓝[>] 0) atTop := by
    intro δ hδ
    have h1 : Tendsto (fun ε : ℝ => ε⁻¹ ^ 2) (𝓝[>] 0) atTop :=
      (tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
    exact (Real.tendsto_toNNReal_atTop.comp h1).atTop_mul_const hδ
  -- Pointwise limit at each fixed positive time.
  have hpt : ∀ δ : ℝ≥0, 0 < δ →
      Tendsto (fun ε : ℝ => ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * δ) : ℝ)) (𝓝[>] 0)
        (𝓝 ((δ : ℝ) / m)) := by
    intro δ hδ
    have hlim : Tendsto (fun ε : ℝ => (δ : ℝ) * ((A.symm ((ε⁻¹ ^ 2).toNNReal * δ) : ℝ) /
        (((ε⁻¹ ^ 2).toNNReal * δ : ℝ≥0) : ℝ))) (𝓝[>] 0) (𝓝 ((δ : ℝ) * m⁻¹)) :=
      tendsto_const_nhds.mul (hslope.comp (hc δ hδ))
    rw [← div_eq_mul_inv (δ : ℝ) m] at hlim
    refine hlim.congr' ?_
    filter_upwards [hpos] with ε hε
    exact (scaled_inverse_eq A.symm hε hδ.ne').symm
  -- Uniform estimate on `[0, T]`, for every positive accuracy `η`.
  have hmain : ∀ η : ℝ, 0 < η → ∀ T : ℝ≥0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
        dist (ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * t) : ℝ)) ((t : ℝ) / m) < η := by
    intro η hη T
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
    have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by linarith
    obtain ⟨δ, hδpos, hδcoe⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ) = η * m / 8 := by
      refine ⟨⟨η * m / 8, (div_pos (mul_pos hη hm) (by norm_num)).le⟩, ?_, rfl⟩
      exact NNReal.coe_pos.mp (div_pos (mul_pos hη hm) (by norm_num))
    have hδm : (δ : ℝ) / m = η / 8 := by
      rw [hδcoe, div_eq_iff hm.ne']
      ring
    obtain ⟨S, hS⟩ := eventually_atTop.mp
      ((Metric.tendsto_nhds.mp hslope) (η / ((T : ℝ) + 1)) (div_pos hη hT1))
    have hcS : ∀ᶠ ε in 𝓝[>] (0 : ℝ), S ≤ (ε⁻¹ ^ 2).toNNReal * δ :=
      (hc δ hδpos).eventually_ge_atTop S
    have hpt' := (Metric.tendsto_nhds.mp (hpt δ hδpos)) (η / 2) (by linarith)
    filter_upwards [hpos, hcS, hpt'] with ε hε hcSε hδε
    intro t ht
    obtain ⟨-, htT⟩ := ht
    rw [Real.dist_eq]
    have hδε' : |ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * δ) : ℝ) - (δ : ℝ) / m| < η / 2 := by
      rw [← Real.dist_eq]
      exact hδε
    obtain ⟨hδ1, hδ2⟩ := abs_lt.mp hδε'
    rcases le_total t δ with htδ | htδ
    · -- Small times: monotonicity of `A⁻¹` bounds the rescaled value by its value at `δ`.
      have hmono : (A.symm ((ε⁻¹ ^ 2).toNNReal * t) : ℝ) ≤
          (A.symm ((ε⁻¹ ^ 2).toNNReal * δ) : ℝ) :=
        NNReal.coe_le_coe.mpr (A.symm.monotone (mul_le_mul_of_nonneg_left htδ zero_le))
      have hFle : ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * t) : ℝ) ≤
          ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * δ) : ℝ) :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg ε)
      have hFnonneg : 0 ≤ ε ^ 2 * (A.symm ((ε⁻¹ ^ 2).toNNReal * t) : ℝ) :=
        mul_nonneg (sq_nonneg ε) (NNReal.coe_nonneg _)
      have hble : (t : ℝ) / m ≤ (δ : ℝ) / m :=
        div_le_div_of_nonneg_right (NNReal.coe_le_coe.mpr htδ) hm.le
      have hbnonneg : 0 ≤ (t : ℝ) / m := div_nonneg (NNReal.coe_nonneg t) hm.le
      rw [abs_lt]
      constructor <;> linarith
    · -- Large times: the rescaled time lies beyond the threshold `S`.
      have htne : t ≠ 0 := (lt_of_lt_of_le hδpos htδ).ne'
      have hSt : S ≤ (ε⁻¹ ^ 2).toNNReal * t :=
        le_trans hcSε (mul_le_mul_of_nonneg_left htδ zero_le)
      have hx := hS _ hSt
      rw [Real.dist_eq] at hx
      have htT' : (t : ℝ) ≤ (T : ℝ) + 1 := by
        have := NNReal.coe_le_coe.mpr htT
        linarith
      have hfac : ∀ y : ℝ, (t : ℝ) * y - (t : ℝ) / m = (t : ℝ) * (y - m⁻¹) :=
        fun y => by ring
      rw [scaled_inverse_eq A.symm hε htne, hfac, abs_mul, abs_of_nonneg (NNReal.coe_nonneg t)]
      exact mul_abs_lt_of_le_of_abs_lt htT' hT1 hx
  refine Metric.tendstoLocallyUniformly_iff.mpr fun η hη x =>
    ⟨Set.Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩
  filter_upwards [hmain η hη (x + 1)] with ε hε
  intro t ht
  rw [dist_comm]
  exact hε t ⟨zero_le,(Set.mem_Iio.mp ht).le⟩

end EinsteinRelation
