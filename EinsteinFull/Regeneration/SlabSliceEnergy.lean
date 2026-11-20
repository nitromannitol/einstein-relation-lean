import PDEFoundation.Monotonicity.Core.RellichSphere
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import PDEFoundation.Sobolev.OneDimensional.ContinuousWeakIncrement

/-!
# Lower energy bounds from coordinate slices

Cauchy–Schwarz on almost every line and Fubini give the quantitative energy
lower bound in Gantert–Mathieu–Piatnitski, equation (4.12).
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A one-dimensional integral bounds the squared `L²` energy. -/
theorem sq_integral_le_length_mul_integral_sq (L : ℝ) (hL : 0 ≤ L)
    (g : ℝ → ℝ) (hg : IntegrableOn g (Ioc 0 L))
    (hg2 : IntegrableOn (fun t => g t ^ 2) (Ioc 0 L)) :
    (∫ t in Ioc 0 L, g t) ^ 2 ≤ L * ∫ t in Ioc 0 L, g t ^ 2 := by
  let μ := (volume : Measure ℝ).restrict (Ioc 0 L)
  let : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have h := PDE.integral_mul_sq_le (μ := μ) (f := fun _ : ℝ => 1) (g := g)
    (by simp) hg2
    (by simpa only [one_mul] using (show Integrable g μ from hg))
  simpa [μ, Real.volume_Ioc, max_eq_left hL] using h

/-- Uniform lower bounds on line integrals give a lower bound on total squared energy. -/
theorem slab_energy_lower_of_slice_integrals {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L c : ℝ) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (g : ℝ × Z → ℝ)
    (hg : Integrable g ((volume.restrict (Ioc 0 L)).prod ν))
    (hg2 : Integrable (fun p => g p ^ 2) ((volume.restrict (Ioc 0 L)).prod ν))
    (hbound : ∀ᵐ z ∂ν, c ≤ |∫ t in Ioc 0 L, g (t, z)|) :
    c ^ 2 * ν.real univ ≤ L * ∫ p, g p ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by
  have hpoint : ∀ᵐ z ∂ν, c ^ 2 ≤ L * ∫ t in Ioc 0 L, g (t, z) ^ 2 := by
    filter_upwards [hg.prod_left_ae, hg2.prod_left_ae, hbound] with z hgi hgi2 hz
    have hcs := sq_integral_le_length_mul_integral_sq L hL (fun t => g (t, z)) hgi hgi2
    have hsq : c ^ 2 ≤ |∫ t in Ioc 0 L, g (t, z)| ^ 2 :=
      pow_le_pow_left₀ hc hz 2
    have hsq' : c ^ 2 ≤ (∫ t in Ioc 0 L, g (t, z)) ^ 2 := by
      simpa only [sq_abs] using hsq
    exact hsq'.trans hcs
  have hinner : Integrable (fun z => ∫ t in Ioc 0 L, g (t, z) ^ 2) ν := hg2.integral_prod_right
  calc
    c ^ 2 * ν.real univ = ∫ _z, c ^ 2 ∂ν := by simp [measureReal_def, mul_comm]
    _ ≤ ∫ z, L * (∫ t in Ioc 0 L, g (t, z) ^ 2) ∂ν :=
      integral_mono_ae (integrable_const _) (hinner.const_mul L) hpoint
    _ = L * ∫ p, g p ^ 2 ∂((volume.restrict (Ioc 0 L)).prod ν) := by
      rw [integral_const_mul, integral_prod_symm _ hg2]

/-- A coercive energy density inherits the lower bound supplied by the line integrals. -/
theorem slab_coercive_energy_lower_of_slice_integrals {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L c lam : ℝ)
    (hL : 0 ≤ L) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (g ρ : ℝ × Z → ℝ)
    (hg : Integrable g ((volume.restrict (Ioc 0 L)).prod ν))
    (hg2 : Integrable (fun p => g p ^ 2) ((volume.restrict (Ioc 0 L)).prod ν))
    (hρ : Integrable ρ ((volume.restrict (Ioc 0 L)).prod ν))
    (hbound : ∀ᵐ z ∂ν, c ≤ |∫ t in Ioc 0 L, g (t, z)|)
    (hcoercive : ∀ᵐ p ∂((volume.restrict (Ioc 0 L)).prod ν), lam * g p ^ 2 ≤ ρ p) :
    lam * (c ^ 2 * ν.real univ) ≤ L * ∫ p, ρ p ∂((volume.restrict (Ioc 0 L)).prod ν) := by
  have hslice := slab_energy_lower_of_slice_integrals ν L c hL hc g hg hg2 hbound
  have henergy := integral_mono_ae (hg2.const_mul lam) hρ hcoercive
  rw [integral_const_mul] at henergy
  have h1 := mul_le_mul_of_nonneg_left hslice hlam
  have h2 := mul_le_mul_of_nonneg_left henergy hL
  nlinarith

/-- An `L²` coordinate derivative supplies the integrability in the coercive slice bound. -/
theorem slab_coercive_energy_lower_of_L2_slices {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L c lam : ℝ)
    (hL : 0 ≤ L) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (g ρ : ℝ × Z → ℝ)
    (hg : MemLp g 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hρ : Integrable ρ ((volume.restrict (Ioc 0 L)).prod ν))
    (hbound : ∀ᵐ z ∂ν, c ≤ |∫ t in Ioc 0 L, g (t, z)|)
    (hcoercive : ∀ᵐ p ∂((volume.restrict (Ioc 0 L)).prod ν), lam * g p ^ 2 ≤ ρ p) :
    lam * (c ^ 2 * ν.real univ) ≤ L * ∫ p, ρ p ∂((volume.restrict (Ioc 0 L)).prod ν) := by
  let : IsFiniteMeasure (volume.restrict (Ioc 0 L) : Measure ℝ) := by infer_instance
  let : IsFiniteMeasure ((volume.restrict (Ioc 0 L)).prod ν) := by infer_instance
  exact slab_coercive_energy_lower_of_slice_integrals ν L c lam hL hc hlam g ρ
    (hg.integrable (by norm_num)) hg.integrable_sq hρ hbound hcoercive

/-- Continuous weak slices convert an endpoint gap into the slab energy lower bound. -/
theorem slab_coercive_energy_lower_of_weak_slices {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L c lam : ℝ)
    (hL : 0 < L) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (u g ρ : ℝ × Z → ℝ)
    (hg : MemLp g 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hρ : Integrable ρ ((volume.restrict (Ioc 0 L)).prod ν))
    (hslice : ∀ᵐ z ∂ν,
      ContinuousOn (fun t => u (t, z)) (Icc 0 L) ∧
      MemLp (fun t => u (t, z)) 2 (volume.restrict (Ioo 0 L)) ∧
      MemLp (fun t => g (t, z)) 2 (volume.restrict (Icc 0 L)) ∧
      PDE.HasWeakDerivOnIoo 0 L (fun t => u (t, z)) (fun t => g (t, z)) ∧
      c ≤ |u (L, z) - u (0, z)|)
    (hcoercive : ∀ᵐ p ∂((volume.restrict (Ioc 0 L)).prod ν), lam * g p ^ 2 ≤ ρ p) :
    lam * (c ^ 2 * ν.real univ) ≤ L * ∫ p, ρ p ∂((volume.restrict (Ioc 0 L)).prod ν) := by
  apply slab_coercive_energy_lower_of_L2_slices ν L c lam hL.le hc hlam g ρ hg hρ
  · filter_upwards [hslice] with z ⟨hu, huLp, hgLp, hweak, hgap⟩
    have hinc := PDE.ContinuousOn.increment_eq_intervalIntegral_of_hasWeakDerivOnIoo
      hL hu huLp hgLp hweak (s := 0) (t := L) (by simp [hL.le]) (by simp [hL.le])
    rw [intervalIntegral.integral_of_le hL.le] at hinc
    simpa only [← hinc] using hgap
  · exact hcoercive

/-- Product square-integrability gives square-integrable sections almost everywhere. -/
theorem memLp_slab_slice_ae {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasure ν] (L : ℝ) (f : ℝ × Z → ℝ)
    (hf : MemLp f 2 ((volume.restrict (Ioc 0 L)).prod ν)) :
    ∀ᵐ z ∂ν, MemLp (fun t => f (t, z)) 2 (volume.restrict (Ioc 0 L)) := by
  have hmeas := hf.aestronglyMeasurable.prodMk_right
  have hint := hf.integrable_sq
  filter_upwards [hmeas, hint.prod_left_ae] with z hzmeas hzint
  exact (memLp_two_iff_integrable_sq hzmeas).2 hzint

/-- Product `L²` control supplies the square-integrability of continuous weak slices. -/
theorem slab_coercive_energy_lower_of_weak_slices_of_memLp
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν] (L c lam : ℝ)
    (hL : 0 < L) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (u g ρ : ℝ × Z → ℝ)
    (hu : MemLp u 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hg : MemLp g 2 ((volume.restrict (Ioc 0 L)).prod ν))
    (hρ : Integrable ρ ((volume.restrict (Ioc 0 L)).prod ν))
    (hslice : ∀ᵐ z ∂ν,
      ContinuousOn (fun t => u (t, z)) (Icc 0 L) ∧
      PDE.HasWeakDerivOnIoo 0 L (fun t => u (t, z)) (fun t => g (t, z)) ∧
      c ≤ |u (L, z) - u (0, z)|)
    (hcoercive : ∀ᵐ p ∂((volume.restrict (Ioc 0 L)).prod ν), lam * g p ^ 2 ≤ ρ p) :
    lam * (c ^ 2 * ν.real univ) ≤ L * ∫ p, ρ p ∂((volume.restrict (Ioc 0 L)).prod ν) := by
  apply slab_coercive_energy_lower_of_weak_slices ν L c lam hL hc hlam u g ρ hg hρ
  · filter_upwards [hslice, memLp_slab_slice_ae ν L u hu,
      memLp_slab_slice_ae ν L g hg] with z ⟨hcont, hweak, hgap⟩ huz hgz
    refine ⟨hcont, ?_, ?_, hweak, hgap⟩
    · rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    · rwa [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  · exact hcoercive

end EinsteinFull.Regeneration
