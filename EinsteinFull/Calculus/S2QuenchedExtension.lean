import EinsteinFull.Calculus.S2QuenchedDominationKernel
import EinsteinFull.Calculus.S2L2ApproxSupport
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# From bounded continuous tests to every `L²` class (quenched identification)

Abstract setting of `S2QuenchedDominationKernel`: `(Ξ, Q)` a probability space, `r : Ξ → Ω`
measurable, `κ` a Markov kernel, `T` a bounded operator on complex `L²(Q.map r)` with
`T f ∘ r = ∫ f dκ` almost surely for every bounded continuous complex `f`. Then for every
`F ∈ L²(Q.map r)`, almost surely in `ω`, `F` is `κ ω`-integrable and
`T F (r ω) = ∫ F dκ ω`.
-/

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

variable {Ξ Ω : Type*} [MeasurableSpace Ξ] [TopologicalSpace Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- `L²` norm of a bounded continuous complex function, through extended norms. -/
theorem eLpNorm_two_cb (ν : Measure Ω) (g : Ω →ᵇ ℂ) :
    eLpNorm (g : Ω → ℂ) 2 ν = (∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    g.continuous.measurable.aestronglyMeasurable]
  simp_rw [ENNReal.toReal_ofNat, ENNReal.rpow_two]

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- The `L¹(κ ∘ₘ Q)` norm of a bounded continuous complex test is controlled by the `L²` norm. -/
theorem lintegral_enorm_bind_le (Q : Measure Ξ) [IsProbabilityMeasure Q] (r : Ξ → Ω)
    (hr : Measurable r) (κ : Kernel Ξ Ω) [IsMarkovKernel κ]
    (T : MeasureTheory.Lp ℂ 2 (Q.map r) →L[ℂ] MeasureTheory.Lp ℂ 2 (Q.map r)) (M : ℝ≥0)
    (hT : ‖T‖ ≤ M)
    (hid : ∀ (f : Ω →ᵇ ℂ) (F : MeasureTheory.Lp ℂ 2 (Q.map r)),
      F =ᵐ[Q.map r] (fun x => f x) →
      (fun ω => T F (r ω)) =ᵐ[Q] fun ω => ∫ x, f x ∂κ ω)
    (g : Ω →ᵇ ℂ) :
    ∫⁻ x, ‖g x‖ₑ ∂(Measure.bind Q κ) ≤ (M : ℝ≥0∞) * eLpNorm (g : Ω → ℂ) 2 (Q.map r) := by
  let f : Ω →ᵇ ℝ≥0 := g.comp (fun z : ℂ => ‖z‖₊) (C := 1) lipschitzWith_one_nnnorm
  have h := lintegral_bind_le_of_apply Q r hr κ T M hT hid f
  rw [eLpNorm_two_cb]
  exact h

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- The `L²` distance between a class and a bounded continuous function. -/
theorem enorm_sub_toLp (ν : Measure Ω) [IsFiniteMeasure ν] (F : MeasureTheory.Lp ℂ 2 ν)
    (g : Ω →ᵇ ℂ) :
    ‖F - BoundedContinuousFunction.toLp 2 ν ℂ g‖ₑ = eLpNorm ((F : Ω → ℂ) - (g : Ω → ℂ)) 2 ν := by
  rw [MeasureTheory.Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_sub F (BoundedContinuousFunction.toLp 2 ν ℂ g),
    BoundedContinuousFunction.coeFn_toLp 2 ν ℂ g] with x h1 h2
  rw [h1]
  simp only [Pi.sub_apply, h2]

/-- **Quenched identification on every `L²` class**, from the identification on bounded
continuous complex tests. -/
theorem quenched_apply_eq_integral (Q : Measure Ξ) [IsProbabilityMeasure Q] (r : Ξ → Ω)
    (hr : Measurable r) (κ : Kernel Ξ Ω) [IsMarkovKernel κ]
    (T : MeasureTheory.Lp ℂ 2 (Q.map r) →L[ℂ] MeasureTheory.Lp ℂ 2 (Q.map r)) (M : ℝ≥0)
    (hT : ‖T‖ ≤ M)
    (hid : ∀ (f : Ω →ᵇ ℂ) (F : MeasureTheory.Lp ℂ 2 (Q.map r)),
      F =ᵐ[Q.map r] (fun x => f x) →
      (fun ω => T F (r ω)) =ᵐ[Q] fun ω => ∫ x, f x ∂κ ω)
    (F : MeasureTheory.Lp ℂ 2 (Q.map r)) :
    ∀ᵐ ω ∂Q, Integrable (fun x => F x) (κ ω) ∧ T F (r ω) = ∫ x, F x ∂κ ω := by
  haveI : IsProbabilityMeasure (Q.map r) := inferInstance
  haveI : IsProbabilityMeasure (Measure.bind Q κ) :=
    inferInstanceAs (IsProbabilityMeasure (κ ∘ₘ Q))
  have hμν := bind_absolutelyContinuous_of_apply Q r hr κ T M hT hid
  have hB := lintegral_enorm_bind_le Q r hr κ T M hT hid
  obtain ⟨h, hL1, hL2⟩ := exists_cb_seq_lintegral (Measure.bind Q κ) (Q.map r) hμν
    (M : ℝ≥0∞) ENNReal.coe_ne_top hB F
  have hFmeas : StronglyMeasurable (F : Ω → ℂ) := MeasureTheory.Lp.stronglyMeasurable F
  -- finiteness of the annealed `L¹` norm
  have hfin : ∫⁻ x, ‖F x‖ₑ ∂(Measure.bind Q κ) ≠ ∞ := by
    obtain ⟨n, hn⟩ := (hL1.eventually (gt_mem_nhds zero_lt_one)).exists
    have hhn : ∫⁻ x, ‖h n x‖ₑ ∂(Measure.bind Q κ) < ∞ :=
      ((h n).integrable (Measure.bind Q κ)).2
    have hle : ∫⁻ x, ‖F x‖ₑ ∂(Measure.bind Q κ) ≤
        ∫⁻ x, ‖F x - h n x‖ₑ ∂(Measure.bind Q κ) + ∫⁻ x, ‖h n x‖ₑ ∂(Measure.bind Q κ) := by
      have hm : Measurable fun x => ‖h n x‖ₑ :=
        (continuous_enorm.comp (h n).continuous).measurable
      calc ∫⁻ x, ‖F x‖ₑ ∂(Measure.bind Q κ)
          ≤ ∫⁻ x, (‖F x - h n x‖ₑ + ‖h n x‖ₑ) ∂(Measure.bind Q κ) := by
            refine lintegral_mono fun x => ?_
            calc ‖F x‖ₑ = ‖(F x - h n x) + h n x‖ₑ := by rw [sub_add_cancel]
              _ ≤ _ := enorm_add_le _ _
        _ = _ := lintegral_add_right _ hm
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨(hn.trans ENNReal.one_lt_top).ne, hhn.ne⟩) hle
  have hFe : Measurable fun x => ‖F x‖ₑ := hFmeas.measurable.enorm
  have hlint : ∫⁻ ω, ∫⁻ x, ‖F x‖ₑ ∂κ ω ∂Q ≠ ∞ := by
    rw [← Measure.lintegral_bind κ.aemeasurable hFe.aemeasurable]
    exact hfin
  have hae_lt : ∀ᵐ ω ∂Q, ∫⁻ x, ‖F x‖ₑ ∂κ ω < ∞ := ae_lt_top hFe.lintegral_kernel hlint
  have hint : ∀ᵐ ω ∂Q, Integrable (fun x => F x) (κ ω) := hae_lt.mono fun ω hω =>
    ⟨hFmeas.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 hω⟩
  -- the approximating classes
  have hFn : ∀ n, BoundedContinuousFunction.toLp 2 (Q.map r) ℂ (h n) =ᵐ[Q.map r]
      fun x => h n x := fun n => BoundedContinuousFunction.coeFn_toLp 2 (Q.map r) ℂ (h n)
  have hidn : ∀ n, ∀ᵐ ω ∂Q, T (BoundedContinuousFunction.toLp 2 (Q.map r) ℂ (h n)) (r ω) =
      ∫ x, h n x ∂κ ω := fun n => hid (h n) _ (hFn n)
  have hmeasE : Measurable fun ω => ‖T F (r ω) - ∫ x, F x ∂κ ω‖ₑ :=
    (((MeasureTheory.Lp.stronglyMeasurable (T F)).measurable.comp hr).sub
      hFmeas.integral_kernel.measurable).enorm
  have hclaim : ∀ n, ∫⁻ ω, ‖T F (r ω) - ∫ x, F x ∂κ ω‖ₑ ∂Q ≤
      (M : ℝ≥0∞) * eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 (Q.map r) +
        ∫⁻ x, ‖F x - h n x‖ₑ ∂(Measure.bind Q κ) := fun n => by
    set Fn : MeasureTheory.Lp ℂ 2 (Q.map r) :=
      BoundedContinuousFunction.toLp 2 (Q.map r) ℂ (h n) with hFndef
    have hpt : ∀ᵐ ω ∂Q, ‖T F (r ω) - ∫ x, F x ∂κ ω‖ₑ ≤
        ‖T F (r ω) - T Fn (r ω)‖ₑ + ∫⁻ x, ‖F x - h n x‖ₑ ∂κ ω := by
      filter_upwards [hint, hidn n] with ω hωi hωn
      have hhn : Integrable (fun x => h n x) (κ ω) := (h n).integrable (κ ω)
      have e1 : T F (r ω) - ∫ x, F x ∂κ ω =
          (T F (r ω) - T Fn (r ω)) + ((∫ x, h n x ∂κ ω) - ∫ x, F x ∂κ ω) := by
        rw [hωn]; ring
      rw [e1]
      refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [← integral_sub hhn hωi]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun x => ?_
      rw [← enorm_neg (F x - h n x), neg_sub]
    have hmeasψ : Measurable fun x => ‖T F x - T Fn x‖ₑ :=
      ((MeasureTheory.Lp.stronglyMeasurable (T F)).sub
        (MeasureTheory.Lp.stronglyMeasurable (T Fn))).measurable.enorm
    have hmeasψr : Measurable fun ω => ‖T F (r ω) - T Fn (r ω)‖ₑ := hmeasψ.comp hr
    have hmapψ : ∫⁻ ω, ‖T F (r ω) - T Fn (r ω)‖ₑ ∂Q = ∫⁻ x, ‖T F x - T Fn x‖ₑ ∂(Q.map r) :=
      (lintegral_map hmeasψ hr).symm
    have hψ : ∫⁻ x, ‖T F x - T Fn x‖ₑ ∂(Q.map r) ≤
        (M : ℝ≥0∞) * eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 (Q.map r) := by
      calc ∫⁻ x, ‖T F x - T Fn x‖ₑ ∂(Q.map r)
          = ∫⁻ x, ‖(T F - T Fn : MeasureTheory.Lp ℂ 2 (Q.map r)) x‖ₑ ∂(Q.map r) := by
            refine lintegral_congr_ae ?_
            filter_upwards [MeasureTheory.Lp.coeFn_sub (T F) (T Fn)] with x hx
            rw [hx]
            rfl
        _ ≤ ‖T F - T Fn‖ₑ * (Q.map r) Set.univ ^ (1 / 2 : ℝ) :=
            lintegral_enorm_le_enorm_mul _ _
        _ = ‖T (F - Fn)‖ₑ := by
            rw [map_sub, Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ,
              measure_univ, ENNReal.one_rpow, mul_one]
        _ ≤ (M : ℝ≥0∞) * ‖F - Fn‖ₑ := enorm_apply_le _ T M hT _
        _ = (M : ℝ≥0∞) * eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 (Q.map r) := by
            rw [enorm_sub_toLp]
    calc ∫⁻ ω, ‖T F (r ω) - ∫ x, F x ∂κ ω‖ₑ ∂Q
        ≤ ∫⁻ ω, (‖T F (r ω) - T Fn (r ω)‖ₑ + ∫⁻ x, ‖F x - h n x‖ₑ ∂κ ω) ∂Q :=
          lintegral_mono_ae hpt
      _ = ∫⁻ ω, ‖T F (r ω) - T Fn (r ω)‖ₑ ∂Q + ∫⁻ ω, ∫⁻ x, ‖F x - h n x‖ₑ ∂κ ω ∂Q :=
          lintegral_add_left hmeasψr _
      _ = ∫⁻ x, ‖T F x - T Fn x‖ₑ ∂(Q.map r) + ∫⁻ x, ‖F x - h n x‖ₑ ∂(Measure.bind Q κ) := by
          have hbind : ∫⁻ x, ‖F x - h n x‖ₑ ∂(Measure.bind Q κ) =
              ∫⁻ ω, ∫⁻ x, ‖F x - h n x‖ₑ ∂κ ω ∂Q :=
            Measure.lintegral_bind κ.aemeasurable
              (hFmeas.measurable.sub (h n).continuous.measurable).enorm.aemeasurable
          rw [hmapψ, hbind]
      _ ≤ _ := add_le_add hψ le_rfl
  have hlim : Tendsto (fun n => (M : ℝ≥0∞) * eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 (Q.map r) +
      ∫⁻ x, ‖F x - h n x‖ₑ ∂(Measure.bind Q κ)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hL2 (Or.inr (ENNReal.coe_ne_top (r := M)))
    simpa only [mul_zero, add_zero] using h1.add hL1
  have hzero : ∫⁻ ω, ‖T F (r ω) - ∫ x, F x ∂κ ω‖ₑ ∂Q = 0 :=
    le_antisymm (ge_of_tendsto' hlim hclaim) zero_le
  have hae0 := (lintegral_eq_zero_iff hmeasE).1 hzero
  filter_upwards [hint, hae0] with ω hi hz
  exact ⟨hi, sub_eq_zero.1 (enorm_eq_zero.1 hz)⟩

end EinsteinFull
