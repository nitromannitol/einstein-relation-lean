import EinsteinFull.Calculus.S3AnnuliSupport
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# `L²` Lévy upward theorem for complex classes

Generic support for `p:tail#sum`: for an increasing sequence of sub-σ-algebras `𝓕 n` of a
probability space with `⨆ n, 𝓕 n = m0`, the `L²` conditional expectations `condExpL2 (𝓕 n) U`
of a complex class converge to `U` in `L²`. Bounded measurable functions are treated by Lévy's
almost-sure theorem for the real and imaginary parts plus uniform integrability; a general class
is approximated by simple functions, using that conditional expectation is an `L²` contraction.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinFull.AnnuliSupport

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : ℕ → MeasurableSpace Ω}

/-- Lévy's theorem in `L²` for a bounded complex function measurable for `m0 = ⨆ 𝓕 n`. -/
theorem tendsto_eLpNorm_condExp_bounded (hmono : Monotone 𝓕) (hm : ∀ n, 𝓕 n ≤ m0)
    (hsup : ⨆ n, 𝓕 n = m0) (h : Ω → ℂ) (hh : Measurable[m0] h) (R : ℝ)
    (hR : ∀ ω, ‖h ω‖ ≤ R) :
    Tendsto (fun n => eLpNorm (μ[h | 𝓕 n] - h) 2 μ) atTop (𝓝 0) := by
  let ℱ : Filtration ℕ m0 := ⟨𝓕, hmono, hm⟩
  have hhM : Measurable[⨆ n, 𝓕 n] h := by rw [hsup]; exact hh
  have hreM : Measurable[⨆ n, 𝓕 n] (fun ω => (h ω).re) := Complex.measurable_re.comp hhM
  have himM : Measurable[⨆ n, 𝓕 n] (fun ω => (h ω).im) := Complex.measurable_im.comp hhM
  have hre0 : Measurable (fun ω => (h ω).re) := Complex.measurable_re.comp hh
  have him0 : Measurable (fun ω => (h ω).im) := Complex.measurable_im.comp hh
  have hbre : ∀ᵐ ω ∂μ, ‖(h ω).re‖ ≤ R :=
    Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm (h ω)).trans (hR ω)
  have hbim : ∀ᵐ ω ∂μ, ‖(h ω).im‖ ≤ R :=
    Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm (h ω)).trans (hR ω)
  have hire : Integrable (fun ω => (h ω).re) μ :=
    Integrable.of_bound hre0.aestronglyMeasurable R hbre
  have himi : Integrable (fun ω => (h ω).im) μ :=
    Integrable.of_bound him0.aestronglyMeasurable R hbim
  have hae_re : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[fun ω => (h ω).re | 𝓕 n]) ω) atTop
      (𝓝 ((h ω).re)) :=
    hire.tendsto_ae_condExp (ℱ := ℱ) hreM.stronglyMeasurable
  have hae_im : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[fun ω => (h ω).im | 𝓕 n]) ω) atTop
      (𝓝 ((h ω).im)) :=
    himi.tendsto_ae_condExp (ℱ := ℱ) himM.stronglyMeasurable
  have hint : Integrable h μ :=
    Integrable.of_bound hh.aestronglyMeasurable R (Filter.Eventually.of_forall hR)
  have hcre : ∀ n, ∀ᵐ ω ∂μ, ((μ[h | 𝓕 n]) ω).re = (μ[fun ω => (h ω).re | 𝓕 n]) ω :=
    fun n => Complex.reCLM.comp_condExp_comm (m := 𝓕 n) hint
  have hcim : ∀ n, ∀ᵐ ω ∂μ, ((μ[h | 𝓕 n]) ω).im = (μ[fun ω => (h ω).im | 𝓕 n]) ω :=
    fun n => Complex.imCLM.comp_condExp_comm (m := 𝓕 n) hint
  rw [← ae_all_iff] at hcre hcim
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[h | 𝓕 n]) ω) atTop (𝓝 (h ω)) := by
    filter_upwards [hae_re, hae_im, hcre, hcim] with ω h1 h2 h3 h4
    have h1' : Tendsto (fun n => ((μ[h | 𝓕 n]) ω).re) atTop (𝓝 ((h ω).re)) :=
      h1.congr fun n => (h3 n).symm
    have h2' : Tendsto (fun n => ((μ[h | 𝓕 n]) ω).im) atTop (𝓝 ((h ω).im)) :=
      h2.congr fun n => (h4 n).symm
    have h5 := ((Complex.continuous_ofReal.tendsto _).comp h1').add
      (((Complex.continuous_ofReal.tendsto _).comp h2').mul_const Complex.I)
    have e : ∀ z : ℂ, ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I = z :=
      fun z => Complex.re_add_im z
    simp only [Function.comp_def, e] at h5
    exact h5
  have hmem : MemLp h 2 μ := MemLp.of_bound hh.aestronglyMeasurable R
    (Filter.Eventually.of_forall hR)
  have hmeasn : ∀ n, AEStronglyMeasurable (μ[h | 𝓕 n]) μ := fun n =>
    (stronglyMeasurable_condExp.mono (hm n)).aestronglyMeasurable
  have hui : UnifIntegrable (fun n => μ[h | 𝓕 n]) 2 μ := by
    refine unifIntegrable_of one_le_two (by simp) hmeasn ?_
    intro ε _
    refine ⟨R.toNNReal + 1, fun n => ?_⟩
    have hG : ∀ᵐ ω ∂μ, ‖(μ[h | 𝓕 n]) ω‖ ≤ R :=
      ae_bdd_norm_condExp_of_ae_bdd_norm (f := h) (m := 𝓕 n) (Filter.Eventually.of_forall hR)
    have hz : {ω | R.toNNReal + 1 ≤ ‖(μ[h | 𝓕 n]) ω‖₊}.indicator (μ[h | 𝓕 n]) =ᵐ[μ] 0 := by
      filter_upwards [hG] with ω hω
      have hnot : ω ∉ {ω | R.toNNReal + 1 ≤ ‖(μ[h | 𝓕 n]) ω‖₊} := by
        intro hmem'
        have h1 : ((R.toNNReal + 1 : NNReal) : ℝ) ≤ ‖(μ[h | 𝓕 n]) ω‖ :=
          NNReal.coe_le_coe.mpr hmem'
        push_cast at h1
        have h2 := Real.le_coe_toNNReal R
        linarith
      exact Set.indicator_of_notMem hnot _
    show eLpNorm ({ω | R.toNNReal + 1 ≤ ‖(μ[h | 𝓕 n]) ω‖₊}.indicator (μ[h | 𝓕 n])) 2 μ ≤ ε
    rw [eLpNorm_congr_ae hz, eLpNorm_zero]
    exact zero_le
  exact tendsto_Lp_finite_of_tendsto_ae one_le_two (by simp) hmeasn hmem hui hae

@[nolint unusedArguments]
theorem norm_sub_eq_toReal_of_ae (A B : Lp ℂ 2 μ) (f : Ω → ℂ)
    (h : ∀ᵐ ω ∂μ, (A : Ω → ℂ) ω - (B : Ω → ℂ) ω = f ω) :
    ‖A - B‖ = (eLpNorm f 2 μ).toReal := by
  rw [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub A B, h] with ω h1 h2
  rw [h1, Pi.sub_apply]
  exact h2

/-- `L²` Lévy upward theorem for `condExpL2` on complex classes. -/
theorem tendsto_condExpL2 (hmono : Monotone 𝓕) (hm : ∀ n, 𝓕 n ≤ m0) (hsup : ⨆ n, 𝓕 n = m0)
    (U : Lp ℂ 2 μ) :
    Tendsto (fun n => (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ)) atTop (𝓝 U) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨S, hS⟩ := Metric.denseRange_iff.1
    (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) (p := 2) (by simp)) U (ε / 3) (by positivity)
  set S' : Lp ℂ 2 μ := (S : Lp ℂ 2 μ) with hS'
  set s := Lp.simpleFunc.toSimpleFunc S with hs
  obtain ⟨R, hR⟩ := s.exists_forall_norm_le
  have hlim := tendsto_eLpNorm_condExp_bounded (μ := μ) hmono hm hsup (s : Ω → ℂ) s.measurable R hR
  have hlim' : Tendsto (fun n => (eLpNorm (μ[(s : Ω → ℂ) | 𝓕 n] - (s : Ω → ℂ)) 2 μ).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simpa [Function.comp_def] using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim' (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hSae : (S' : Ω → ℂ) =ᵐ[μ] (s : Ω → ℂ) := (Lp.simpleFunc.toSimpleFunc_eq_toFun S).symm
  have hc1 : ‖(condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) - S'‖ < ε / 3 := by
    have e : ‖(condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) - S'‖ =
        (eLpNorm (μ[(s : Ω → ℂ) | 𝓕 n] - (s : Ω → ℂ)) 2 μ).toReal := by
      apply norm_sub_eq_toReal_of_ae
      filter_upwards [condExpL2_ae_eq (hm n) S', condExp_congr_ae (m := 𝓕 n) hSae, hSae]
        with ω h1 h2 h3
      rw [h1, h2, h3, Pi.sub_apply]
    rw [e]
    have := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at this
  have hc2 : ‖(condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ)‖ < ε / 3 := by
    have h1 : ‖(condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ)‖ ≤ ‖U - S'‖ := by
      rw [Submodule.norm_coe]
      exact norm_condExpL2_le (hm n) _
    rw [← dist_eq_norm] at h1
    exact lt_of_le_of_lt h1 hS
  have hc3 : ‖S' - U‖ < ε / 3 := by
    rw [← dist_eq_norm, dist_comm]
    exact hS
  have hsplit : (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ) - U =
      ((condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ) +
        ((condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) - S')) + (S' - U) := by
    have e : (condExpL2 ℂ ℂ (hm n) U : Lp ℂ 2 μ) =
        (condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ) + (condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) := by
      rw [← Submodule.coe_add, ← map_add, sub_add_cancel]
    rw [e]
    abel
  rw [dist_eq_norm, hsplit]
  calc ‖((condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ) +
        ((condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) - S')) + (S' - U)‖
      ≤ ‖(condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ) +
        ((condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) - S')‖ + ‖S' - U‖ := norm_add_le _ _
    _ ≤ (‖(condExpL2 ℂ ℂ (hm n) (U - S') : Lp ℂ 2 μ)‖ +
        ‖(condExpL2 ℂ ℂ (hm n) S' : Lp ℂ 2 μ) - S'‖) + ‖S' - U‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add hc2 hc1) hc3
    _ = ε := by ring

end EinsteinFull.AnnuliSupport
