import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! If a jointly integrable family `y ↦ F(y, ·)` consists (almost surely in `y`) of
functions that are a.e. equal to `G`-measurable ones, then its integral over `y` is
a.e. equal to a `G`-measurable function. Only `L¹` is used (duality against indicators
and the pull-out property of the conditional expectation); no measurable
representative in `(y, ω)` is needed. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

variable {Y Ω : Type*} [MeasurableSpace Y] {G : MeasurableSpace Ω} {m0 : MeasurableSpace Ω}

/-- Pairing with a bounded function against a `G`-measurable integrable function
only sees the conditional expectation of the bounded function. -/
theorem integral_mul_eq_integral_condExp_mul {μ : Measure Ω} [IsFiniteMeasure μ]
    (hG : G ≤ m0) {ψ g : Ω → ℝ} (hψ : Integrable ψ μ)
    (hg : StronglyMeasurable[G] g) (hψg : Integrable (ψ * g) μ) :
    ∫ ω, ψ ω * g ω ∂μ = ∫ ω, (μ[ψ | G]) ω * g ω ∂μ := by
  have h1 := condExp_mul_of_stronglyMeasurable_right hg hψg hψ
  have h2 : ∫ ω, (μ[ψ * g | G]) ω ∂μ = ∫ ω, (ψ * g) ω ∂μ := integral_condExp hG
  rw [integral_congr_ae h1] at h2
  simpa only [Pi.mul_apply] using h2.symm

theorem local_integral_aeEq_measurable {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Y} [SFinite ν] (hG : G ≤ m0)
    {F : Y × Ω → ℝ} (hF : Integrable F (ν.prod μ))
    (hloc : ∀ᵐ y ∂ν, ∃ g : Ω → ℝ, StronglyMeasurable[G] g ∧
      (fun ω => F (y, ω)) =ᵐ[μ] g) :
    ∃ H : Ω → ℝ, StronglyMeasurable[G] H ∧ (fun ω => ∫ y, F (y, ω) ∂ν) =ᵐ[μ] H := by
  classical
  have hslice : ∀ᵐ y ∂ν, Integrable (fun ω => F (y, ω)) μ := hF.prod_right_ae
  obtain ⟨H, hH⟩ : ∃ H : Ω → ℝ, H = fun ω => ∫ y, F (y, ω) ∂ν := ⟨_, rfl⟩
  have hHint : Integrable H μ := by rw [hH]; exact hF.integral_prod_right
  rw [← hH]
  refine ⟨μ[H | G], stronglyMeasurable_condExp, ?_⟩
  have hh'int : Integrable (μ[H | G]) μ := integrable_condExp
  -- exchange the integral over `y` with a bounded pairing
  have swap : ∀ φ : Ω → ℝ, AEStronglyMeasurable φ μ → (∀ᵐ ω ∂μ, ‖φ ω‖ ≤ 1) →
      ∫ ω, φ ω * H ω ∂μ = ∫ y, ∫ ω, φ ω * F (y, ω) ∂μ ∂ν := by
    intro φ hφ hbd
    have hint : Integrable (fun p : Y × Ω => φ p.2 * F p) (ν.prod μ) :=
      Integrable.bdd_mul (c := 1) hF
        (hφ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
        (Measure.quasiMeasurePreserving_snd.ae hbd)
    have hint' : Integrable (Function.uncurry fun (ω : Ω) (y : Y) => φ ω * F (y, ω))
        (μ.prod ν) := hint.swap
    calc ∫ ω, φ ω * H ω ∂μ = ∫ ω, ∫ y, φ ω * F (y, ω) ∂ν ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          rw [hH]
          simp only
          rw [integral_const_mul]
      _ = ∫ y, ∫ ω, φ ω * F (y, ω) ∂μ ∂ν := integral_integral_swap hint'
  -- the bounded pairing only sees the conditional expectation
  have key : ∀ ψ : Ω → ℝ, Measurable ψ → (∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ 1) →
      ∫ ω, ψ ω * H ω ∂μ = ∫ ω, (μ[ψ | G]) ω * H ω ∂μ := by
    intro ψ hψm hψbd
    have hψint : Integrable ψ μ :=
      Integrable.of_bound hψm.aestronglyMeasurable 1 hψbd
    have htbd : ∀ᵐ ω ∂μ, ‖(μ[ψ | G]) ω‖ ≤ 1 := by
      have h1 : ∀ᵐ ω ∂μ, |ψ ω| ≤ 1 := by
        filter_upwards [hψbd] with ω hω using by simpa only [Real.norm_eq_abs] using hω
      filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := G) h1] with ω hω
      simpa only [Real.norm_eq_abs] using hω
    have htaem : AEStronglyMeasurable (μ[ψ | G]) μ :=
      ((stronglyMeasurable_condExp (m := G) (f := ψ)).mono hG).aestronglyMeasurable
    rw [swap ψ hψm.aestronglyMeasurable hψbd, swap (μ[ψ | G]) htaem htbd]
    refine integral_congr_ae ?_
    filter_upwards [hslice, hloc] with y hy hy'
    obtain ⟨g, hgm, hg⟩ := hy'
    have hgint : Integrable g μ := hy.congr hg
    have hψg : Integrable (ψ * g) μ :=
      Integrable.bdd_mul (c := 1) hgint hψm.aestronglyMeasurable hψbd
    have e1 := integral_mul_eq_integral_condExp_mul hG hψint hgm hψg
    have e2 : ∫ ω, ψ ω * F (y, ω) ∂μ = ∫ ω, ψ ω * g ω ∂μ :=
      integral_congr_ae (hg.mono fun ω hω => by simp only [hω])
    have e3 : ∫ ω, (μ[ψ | G]) ω * F (y, ω) ∂μ = ∫ ω, (μ[ψ | G]) ω * g ω ∂μ :=
      integral_congr_ae (hg.mono fun ω hω => by simp only [hω])
    rw [e2, e3]
    exact e1
  -- pairing `H` and its conditional expectation with a bounded function agrees
  have hgen : ∀ ψ : Ω → ℝ, Measurable ψ → (∀ᵐ ω ∂μ, ‖ψ ω‖ ≤ 1) →
      ∫ ω, ψ ω * H ω ∂μ = ∫ ω, ψ ω * (μ[H | G]) ω ∂μ := by
    intro ψ hψm hψbd
    have hψint : Integrable ψ μ :=
      Integrable.of_bound hψm.aestronglyMeasurable 1 hψbd
    have htbd : ∀ᵐ ω ∂μ, ‖(μ[ψ | G]) ω‖ ≤ 1 := by
      have h1 : ∀ᵐ ω ∂μ, |ψ ω| ≤ 1 := by
        filter_upwards [hψbd] with ω hω using by simpa only [Real.norm_eq_abs] using hω
      filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := G) h1] with ω hω
      simpa only [Real.norm_eq_abs] using hω
    have htm : StronglyMeasurable[G] (μ[ψ | G]) := stronglyMeasurable_condExp
    have hψh' : Integrable (ψ * μ[H | G]) μ :=
      Integrable.bdd_mul (c := 1) hh'int hψm.aestronglyMeasurable hψbd
    have a1 := integral_mul_eq_integral_condExp_mul hG hψint
      (stronglyMeasurable_condExp (m := G) (f := H)) hψh'
    have htH : Integrable (μ[ψ | G] * H) μ :=
      Integrable.bdd_mul (c := 1) hHint (htm.mono hG).aestronglyMeasurable htbd
    have a2 : ∫ ω, (μ[ψ | G]) ω * (μ[H | G]) ω ∂μ = ∫ ω, (μ[ψ | G]) ω * H ω ∂μ := by
      have p := condExp_mul_of_stronglyMeasurable_left htm htH hHint
      have q : ∫ ω, (μ[μ[ψ | G] * H | G]) ω ∂μ = ∫ ω, (μ[ψ | G] * H) ω ∂μ :=
        integral_condExp hG
      rw [integral_congr_ae p] at q
      simpa only [Pi.mul_apply] using q
    calc ∫ ω, ψ ω * H ω ∂μ = ∫ ω, (μ[ψ | G]) ω * H ω ∂μ := key ψ hψm hψbd
      _ = ∫ ω, (μ[ψ | G]) ω * (μ[H | G]) ω ∂μ := a2.symm
      _ = ∫ ω, ψ ω * (μ[H | G]) ω ∂μ := a1.symm
  -- orthogonality of `H - μ[H | G]` against indicators
  have hK : Integrable (H - μ[H | G]) μ := hHint.sub hh'int
  have hzero : H - μ[H | G] =ᵐ[μ] 0 := by
    refine hK.ae_eq_zero_of_forall_setIntegral_eq_zero ?_
    intro s hs _
    have hψm : Measurable (s.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hs
    have hψbd : ∀ᵐ ω ∂μ, ‖s.indicator (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
      refine Filter.Eventually.of_forall fun ω => ?_
      simp only [Set.indicator, Real.norm_eq_abs]
      split_ifs <;> simp
    have hψH : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * H ω) μ :=
      Integrable.bdd_mul (c := 1) hHint hψm.aestronglyMeasurable hψbd
    have hψh' : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * (μ[H | G]) ω) μ :=
      Integrable.bdd_mul (c := 1) hh'int hψm.aestronglyMeasurable hψbd
    have e1 : ∫ ω in s, (H - μ[H | G]) ω ∂μ =
        ∫ ω, (s.indicator (fun _ => (1 : ℝ)) ω * H ω -
          s.indicator (fun _ => (1 : ℝ)) ω * (μ[H | G]) ω) ∂μ := by
      rw [← integral_indicator hs]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Set.indicator, Pi.sub_apply]
      split_ifs <;> simp
    rw [e1, integral_sub hψH hψh', hgen _ hψm hψbd, sub_self]
  filter_upwards [hzero] with ω hω
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hω

end EinsteinFull.Calculus.S1
