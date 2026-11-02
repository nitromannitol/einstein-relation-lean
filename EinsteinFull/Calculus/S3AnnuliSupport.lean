import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Conditional expectations of complex `L²` classes

Generic support for `p:tail#annuli`: `condExpL2` on `Lp ℂ 2 μ` agrees a.e. with `condExp`, is
a contraction in every `L^p`, preserves the integral and real-valuedness, and approximates the
function when a measurable approximant is available.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.AnnuliSupport

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {m : MeasurableSpace Ω}

theorem condExpL2_ae_eq (hm : m ≤ m0) (U : Lp ℂ 2 μ) :
    (condExpL2 ℂ ℂ hm U : Ω → ℂ) =ᵐ[μ] μ[(U : Ω → ℂ) | m] := by
  have h := (Lp.memLp U).condExpL2_ae_eq_condExp (𝕜 := ℂ) hm
  rwa [Lp.toLp_coeFn U (Lp.memLp U)] at h

theorem ae_norm_condExpL2_sub_le {m' : MeasurableSpace Ω} (hm : m ≤ m0) (hm' : m' ≤ m)
    (U : Lp ℂ 2 μ) (V : Ω → ℂ) (hV : Measurable[m'] V) {ε : ℝ}
    (hUV : ∀ᵐ ω ∂μ, ‖U ω - V ω‖ ≤ ε) :
    ∀ᵐ ω ∂μ, ‖(condExpL2 ℂ ℂ hm U : Ω → ℂ) ω - U ω‖ ≤ 2 * ε := by
  have hUint : Integrable (U : Ω → ℂ) μ := MemLp.integrable one_le_two (Lp.memLp U)
  have hVm : StronglyMeasurable[m] V := (hV.stronglyMeasurable).mono hm'
  have hVm0 : AEStronglyMeasurable[m0] V μ := (hVm.mono hm).aestronglyMeasurable
  have hVint : Integrable V μ := by
    refine Integrable.mono' (g := fun ω => ‖(U : Ω → ℂ) ω‖ + ε)
      (hUint.norm.add (integrable_const ε)) hVm0 ?_
    filter_upwards [hUV] with ω hω
    calc ‖V ω‖ = ‖U ω - (U ω - V ω)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖U ω‖ + ‖U ω - V ω‖ := norm_sub_le _ _
      _ ≤ ‖U ω‖ + ε := by linarith
  have hcV : μ[V | m] = V := condExp_of_stronglyMeasurable hm hVm hVint
  have h1 := condExp_sub hUint hVint m
  have h2 : ∀ᵐ ω ∂μ, ‖(μ[((U : Ω → ℂ) - V) | m]) ω‖ ≤ ε :=
    ae_bdd_norm_condExp_of_ae_bdd_norm (f := (U : Ω → ℂ) - V) (m := m) hUV
  filter_upwards [condExpL2_ae_eq hm U, h1, h2, hUV] with ω hE h1 h2 h3
  have e : (μ[((U : Ω → ℂ) - V) | m]) ω = (μ[(U : Ω → ℂ) | m]) ω - V ω := by
    rw [h1]; simp [hcV]
  have h4 : ‖(μ[(U : Ω → ℂ) | m]) ω - V ω‖ ≤ ε := by rwa [e] at h2
  rw [hE]
  calc ‖(μ[(U : Ω → ℂ) | m]) ω - U ω‖
      = ‖((μ[(U : Ω → ℂ) | m]) ω - V ω) + (V ω - U ω)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(μ[(U : Ω → ℂ) | m]) ω - V ω‖ + ‖V ω - U ω‖ := norm_add_le _ _
    _ ≤ ε + ε := add_le_add h4 (by rw [norm_sub_rev]; exact h3)
    _ = 2 * ε := by ring

theorem eLpNorm_condExpL2_le (hm : m ≤ m0) (U : Lp ℂ 2 μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (condExpL2 ℂ ℂ hm U : Ω → ℂ) p μ ≤ eLpNorm (U : Ω → ℂ) p μ := by
  rw [eLpNorm_congr_ae (condExpL2_ae_eq hm U)]
  exact eLpNorm_condExp_le_eLpNorm _ hp

theorem memLp_condExpL2 (hm : m ≤ m0) (U : Lp ℂ 2 μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hU : MemLp (U : Ω → ℂ) p μ) : MemLp (condExpL2 ℂ ℂ hm U : Ω → ℂ) p μ :=
  MemLp.ae_eq (condExpL2_ae_eq hm U).symm (hU.condExp hp (m := m))

theorem integral_condExpL2 (hm : m ≤ m0) (U : Lp ℂ 2 μ) :
    ∫ ω, (condExpL2 ℂ ℂ hm U : Ω → ℂ) ω ∂μ = ∫ ω, (U : Ω → ℂ) ω ∂μ := by
  rw [integral_congr_ae (condExpL2_ae_eq hm U)]
  exact integral_condExp hm

/-- The conditional expectation of an a.e. real class is the real conditional expectation of
its real part. -/
theorem condExpL2_real (hm : m ≤ m0) (U : Lp ℂ 2 μ) (hU : ∀ᵐ ω ∂μ, (U ω).im = 0) :
    (fun ω => ((μ[fun ω => (U ω).re | m] ω : ℝ) : ℂ)) =ᵐ[μ] (condExpL2 ℂ ℂ hm U : Ω → ℂ) := by
  have hUint : Integrable (U : Ω → ℂ) μ := MemLp.integrable one_le_two (Lp.memLp U)
  have hint : Integrable (fun ω => (U ω).re) μ := by
    simpa using Complex.reCLM.integrable_comp hUint
  have h1 := Complex.ofRealCLM.comp_condExp_comm (m := m) hint
  have h2 : (Complex.ofRealCLM ∘ fun ω => (U ω).re) =ᵐ[μ] (U : Ω → ℂ) := by
    filter_upwards [hU] with ω hω
    exact Complex.ext (by simp) (by simp [hω])
  have h3 := condExp_congr_ae (m := m) h2
  exact h1.trans (h3.trans (condExpL2_ae_eq hm U).symm)

omit [IsFiniteMeasure μ] in
theorem eLpNorm_toReal_le_of_ae_norm_le [IsProbabilityMeasure μ] {f : Ω → ℂ}
    (hf : AEStronglyMeasurable[m0] f μ) {p : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) : (eLpNorm f p μ).toReal ≤ C := by
  have h1 := eLpNorm_le_of_ae_bound (p := p) hf h
  rw [measure_univ, ENNReal.one_rpow, one_mul] at h1
  exact ENNReal.toReal_le_of_le_ofReal hC h1

end EinsteinFull.AnnuliSupport
