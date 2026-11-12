import EinsteinRelation.Correctors.SpatialGradientTimeMinkowski
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Passing local RMS moments through an almost-sure spatial limit

Source: `paper/main.tex:800–808,842–849`. Two applications of Fatou's
lemma retain high stochastic moments of a spatial L2 norm. Finiteness of
the extended spatial energy is proved before using a real RMS integral.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Uniform stochastic moments of local spatial RMS norms pass to a
spatial almost-everywhere limit. Local L2 membership of the limit is part
of the conclusion. Source: `paper/main.tex:800–808,842–849`. -/
theorem spatial_rms_moment_le_of_ae_tendsto
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (Q : Measure Ω) (ν : Measure X) [SFinite ν]
    (f : ℕ → Ω × X → E) (g : Ω × X → E)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    {p C : ℝ} (hp : 0 < p)
    (hlocal : ∀ n, ∀ᵐ ω ∂Q, MemLp (fun x => f n (ω,x)) 2 ν)
    (hbound : ∀ n, eLpNorm (fun ω => Real.sqrt (∫ x, ‖f n (ω,x)‖^2 ∂ν))
      (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C)
    (hlim : ∀ᵐ ω ∂Q, ∀ᵐ x ∂ν,
      Tendsto (fun n => f n (ω,x)) atTop (𝓝 (g (ω,x)))) :
    (∀ᵐ ω ∂Q, MemLp (fun x => g (ω,x)) 2 ν) ∧
      MemLp (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖^2 ∂ν)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖^2 ∂ν)) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal C := by
  have hm {F : Ω × X → E} (hF : Measurable F) :
      Measurable (fun ω => eLpNorm (fun x => F (ω,x)) 2 ν) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    exact ((hF.enorm.pow_const _).lintegral_prod_right').pow_const _
  have he {F : X → E} (hF : MemLp F 2 ν) :
      ‖Real.sqrt (∫ x, ‖F x‖^2 ∂ν)‖ₑ = eLpNorm F 2 ν := by
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), eLpNorm_two_eq_ofReal_spatial_rms ν hF]
  have hpow {F : Ω → ℝ} :
      (eLpNorm F (ENNReal.ofReal p) Q)^p = ∫⁻ ω, ‖F ω‖ₑ^p ∂Q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  have hinner : ∀ᵐ ω ∂Q, (eLpNorm (fun x => g (ω,x)) 2 ν)^p ≤
      liminf (fun n => (eLpNorm (fun x => f n (ω,x)) 2 ν)^p) atTop := by
    filter_upwards [hlim] with ω hω
    have h := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
      (fun n => ((hf n).comp measurable_prodMk_left).aestronglyMeasurable) _ hω
    have hpowlim : (liminf (fun n => eLpNorm (fun x => f n (ω,x)) 2 ν) atTop)^p =
        liminf (fun n => (eLpNorm (fun x => f n (ω,x)) 2 ν)^p) atTop := by
      exact (ENNReal.orderIsoRpow p hp).liminf_apply (by isBoundedDefault)
        (by isBoundedDefault) (by isBoundedDefault) (by isBoundedDefault)
    exact (ENNReal.rpow_le_rpow h hp.le).trans_eq hpowlim
  have hi : (∫⁻ ω, (eLpNorm (fun x => g (ω,x)) 2 ν)^p ∂Q) ≤ (ENNReal.ofReal C)^p := by
    refine (lintegral_mono_ae hinner).trans
      ((lintegral_liminf_le fun n => (hm (hf n)).pow_const p).trans ?_)
    apply liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    have hn := ENNReal.rpow_le_rpow (hbound n) hp.le
    rw [hpow] at hn
    exact (lintegral_congr_ae ((hlocal n).mono fun ω hω =>
      congrArg (fun a : ℝ≥0∞ => a^p) (he hω))).symm.trans_le hn
  have hlocalg : ∀ᵐ ω ∂Q, MemLp (fun x => g (ω,x)) 2 ν := by
    filter_upwards [ae_lt_top ((hm hg).pow_const p)
      (hi.trans_lt (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)).ne]
      with ω hω
    refine ⟨(hg.comp measurable_prodMk_left).aestronglyMeasurable, ?_⟩
    have hroot := ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hp.le) hω.ne
    rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one] at hroot
  have hgm : Measurable (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖^2 ∂ν)) :=
    ((hg.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hb : eLpNorm (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖^2 ∂ν))
      (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C := by
    apply (ENNReal.rpow_le_rpow_iff hp).mp
    rw [hpow]
    exact (lintegral_congr_ae (hlocalg.mono fun ω hω =>
      congrArg (fun a : ℝ≥0∞ => a^p) (he hω))).trans_le hi
  exact ⟨hlocalg, ⟨hgm.aestronglyMeasurable, hb.trans_lt ENNReal.ofReal_lt_top⟩, hb⟩

end EinsteinRelation.Correctors
