import EinsteinRelation.Correctors.AKMHeatKernelSmoothing
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! # Bounded fields paired with compact regularizations

Source: AKM (9.2), p. 347; `paper/main.tex:777–782,840`.
Fubini transfers smoothing to a bounded field; dominated convergence
then removes it without assuming smoothness of the field.
-/

open MeasureTheory Filter
open scoped Topology Convolution
namespace EinsteinRelation.Correctors

/-- Transfer an even scalar convolution across an integrable pairing. -/
theorem akm_integral_mul_convolution_swap {d : ℕ} {f h ρ : Vec d → ℝ}
    (hh : Integrable h volume) (hρ : Integrable ρ volume)
    (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ B) (heven : ∀ x, ρ (-x) = ρ x) :
    (∫ x, f x * (∫ y, h y * ρ (x-y) ∂volume) ∂volume) =
      ∫ y, h y * (∫ z, ρ z * f (y-z) ∂volume) ∂volume := by
  have hi := hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρ
  have hbf : ∀ᵐ z : Vec d × Vec d ∂volume.prod volume, ‖f z.1‖ ≤ B :=
    Measure.quasiMeasurePreserving_fst.ae hb
  have hip : Integrable (fun z : Vec d × Vec d =>
      f z.1 * (h z.2 * ρ (z.1-z.2))) (volume.prod volume) :=
    hi.bdd_mul hf.comp_fst hbf
  calc
    _ = ∫ x, ∫ y, f x * (h y * ρ (x-y)) ∂volume ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, f x * (h y * ρ (x-y)) ∂volume ∂volume :=
      integral_integral_swap hip
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      have hc := integral_sub_left_eq_self
        (fun x : Vec d => f x * (h y * ρ (x-y))) volume y
      rw [← hc, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      simp only [sub_sub_cancel_left, heven]
      ring

/-- Bounded data convolved against normalized compact kernels remain bounded. -/
theorem akm_bounded_mollification_bound {d : ℕ} {f ρ : Vec d → ℝ}
    (hρ : Integrable ρ volume) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : (∫ x, ρ x ∂volume) = 1)
    (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ B) (x : Vec d) :
    ‖∫ y, ρ y * f (x-y) ∂volume‖ ≤ |B| := by
  have hf' := hf.comp_quasiMeasurePreserving
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  have hb' : ∀ᵐ y ∂volume, ‖f (x-y)‖ ≤ |B| :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae
      (hb.mono (fun y hy => hy.trans (le_abs_self B)))
  have hi : Integrable (fun y => ρ y * f (x-y)) volume := hρ.mul_bdd hf' hb'
  calc
    _ ≤ ∫ y, ‖ρ y * f (x-y)‖ ∂volume := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ρ y * |B| ∂volume := by
      apply integral_mono_ae hi.norm (hρ.mul_const |B|)
      filter_upwards [hb'] with y hy
      simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ0 y)] using
        mul_le_mul_of_nonneg_left hy (hρ0 y)
    _ = |B| := by rw [integral_mul_const, hρ1, one_mul]

/-- The bounded-field pairing with any integrable datum converges under
standard compact mollification. -/
theorem akm_bounded_mollification_pairing_tendsto {d : ℕ} {f h : Vec d → ℝ}
    (hh : Integrable h volume) (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ B) :
    Tendsto (fun n => ∫ x, h x *
      (∫ y, (akmTraceBump d n).normed volume y * f (x-y) ∂volume) ∂volume)
      atTop (𝓝 (∫ x, h x * f x ∂volume)) := by
  have hloc : LocallyIntegrable f volume :=
    (memLp_top_of_bound hf B hb).locallyIntegrable (by simp)
  have hm n : Continuous (fun x =>
      ∫ y, (akmTraceBump d n).normed volume y * f (x-y) ∂volume) :=
    (akmTraceBump d n).hasCompactSupport_normed.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (show ContDiff ℝ (⊤ : ℕ∞) ((akmTraceBump d n).normed volume) from
        (akmTraceBump d n).contDiff_normed).continuous hloc
  have hbound n x := akm_bounded_mollification_bound
    ((show ContDiff ℝ (⊤ : ℕ∞) ((akmTraceBump d n).normed volume) from
        (akmTraceBump d n).contDiff_normed).continuous.integrable_of_hasCompactSupport
      (akmTraceBump d n).hasCompactSupport_normed)
    (akmTraceBump d n).nonneg_normed (akmTraceBump d n).integral_normed hf hb x
  have hconv : ∀ᵐ x ∂volume, Tendsto (fun n =>
      ∫ y, (akmTraceBump d n).normed volume y * f (x-y) ∂volume) atTop (𝓝 (f x)) := by
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := akmTraceBump d) (K := 2)
      (show Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (𝓝 0) from
        tendsto_one_div_add_atTop_nhds_zero_nat) ?_ hloc
    exact Eventually.of_forall (fun n => by dsimp [akmTraceBump]; linarith)
  apply tendsto_integral_of_dominated_convergence (fun x => ‖h x‖ * |B|)
    (fun n => hh.aestronglyMeasurable.mul (hm n).aestronglyMeasurable)
    (hh.norm.mul_const |B|)
  · intro n
    filter_upwards with x
    simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_left (hbound n x) (norm_nonneg (h x))
  · filter_upwards [hconv] with x hx
    exact hx.const_mul (h x)

end EinsteinRelation.Correctors
