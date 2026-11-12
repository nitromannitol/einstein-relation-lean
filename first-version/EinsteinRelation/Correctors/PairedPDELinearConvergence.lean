import EinsteinRelation.Correctors.PairedPDEQuadraticConvergence

/-! # Linear operations in strong L² approximation

Source: `paper/main.tex:832–840`. Bounded cutoffs and addition preserve the
actual spatial derivative limits.
-/

open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-- Fixed bounded multiplication preserves strong L² limits.
Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_fixed_mul_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u w : X → ℝ} {us : ℕ → X → ℝ}
    (hu : MemLp u 2 μ) (hus : ∀ k, MemLp (us k) 2 μ)
    (hw : MemLp w ∞ μ)
    (hlim : Tendsto (fun k => eLpNorm (fun x => us k x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => w x * us k x - w x * u x) 2 μ)
      atTop (𝓝 0) := by
  have hb := ENNReal.Tendsto.const_mul hlim (Or.inr hw.eLpNorm_ne_top)
  rw [mul_zero] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le _) (fun k => ?_)
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub] using
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (2 : ℝ≥0∞) ((hus k).sub hu).1 w

/-- Addition preserves actual strong L² limits.
Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_add_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u v : X → ℝ} {us vs : ℕ → X → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hus : ∀ k, MemLp (us k) 2 μ) (hvs : ∀ k, MemLp (vs k) 2 μ)
    (hulim : Tendsto (fun k => eLpNorm (fun x => us k x - u x) 2 μ) atTop (𝓝 0))
    (hvlim : Tendsto (fun k => eLpNorm (fun x => vs k x - v x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => (us k x + vs k x) - (u x + v x)) 2 μ)
      atTop (𝓝 0) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k => (hus k).add (hvs k)) _
    (hu.add hv)).mp
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' us hus u hu).mpr hulim
  have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' vs hvs v hv).mpr hvlim
  simpa only [MemLp.toLp_add] using hF.add hG

/-- Restricting the measure preserves a vanishing strong seminorm.
Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_eLpNorm_of_measure_le {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) {p : ℝ≥0∞} {fs : ℕ → X → ℝ}
    (hlim : Tendsto (fun k => eLpNorm (fs k) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fs k) p ν) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun _ => eLpNorm_mono_measure _ hν)

end EinsteinRelation.Correctors
