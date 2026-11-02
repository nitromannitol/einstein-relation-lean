import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Frozen.SmoothWithBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Time rescaling of physical evolutions. Multiplying the coefficient field by
`κ > 0` multiplies the physical generator by `κ`, so the evolution of the
rescaled field at time `s` is the original evolution at time `κ s`. With
`κ = 1/2` this moves unit times to the times at least two where the point-kernel
bounds hold. -/

open MeasureTheory Filter
open scoped NNReal Topology BigOperators

namespace EinsteinFull
open EinsteinRelation

/-- The weak forward generator graph of a rescaled field. -/
theorem clr_generatorPair_smul_iff {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (κ : ℝ) (hκ : κ ≠ 0) (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexGeneratorPair (fun x => κ • a x) i ζ f g ↔
      IsPhysicalComplexGeneratorPair a i ζ f ((κ : ℂ)⁻¹ • g) := by
  have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have hent (x : Vec d) (j k : Fin d) :
      (((κ • a x) j k : ℝ) : ℂ) = (κ : ℂ) * (a x j k : ℂ) := by
    rw [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have hint (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      (∫ x, ((κ : ℂ)⁻¹ • g) x * v x) = (κ : ℂ)⁻¹ * ∫ x, g x * v x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul ((κ : ℂ)⁻¹) g] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  constructor
  · rintro ⟨Gf, hGf, hw⟩
    refine ⟨Gf, hGf, fun v Gv hv => ?_⟩
    rw [hint, hw v Gv hv]
    simp only [hent]
    have h1 : (∫ x, ∑ j, ∑ k, (κ : ℂ) * (a x j k : ℂ) * Gf k x * Gv j x) =
        (κ : ℂ) * ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * Gf k x * Gv j x := by
      rw [← integral_const_mul]
      congr 1; funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∫ x, (∑ j, (κ : ℂ) * (a x j i : ℂ) * Gf j x) * v x) =
        (κ : ℂ) * ∫ x, (∑ j, (a x j i : ℂ) * Gf j x) * v x := by
      rw [← integral_const_mul]
      congr 1; funext x
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2]
    field_simp
  · rintro ⟨Gf, hGf, hw⟩
    refine ⟨Gf, hGf, fun v Gv hv => ?_⟩
    have h := hw v Gv hv
    rw [hint] at h
    simp only [hent]
    have h1 : (∫ x, ∑ j, ∑ k, (κ : ℂ) * (a x j k : ℂ) * Gf k x * Gv j x) =
        (κ : ℂ) * ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * Gf k x * Gv j x := by
      rw [← integral_const_mul]
      congr 1; funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : (∫ x, (∑ j, (κ : ℂ) * (a x j i : ℂ) * Gf j x) * v x) =
        (κ : ℂ) * ∫ x, (∑ j, (a x j i : ℂ) * Gf j x) * v x := by
      rw [← integral_const_mul]
      congr 1; funext x
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2]
    have h' : (∫ x, g x * v x) = (κ : ℂ) * ((κ : ℂ)⁻¹ * ∫ x, g x * v x) := by
      rw [← mul_assoc, mul_inv_cancel₀ hκc, one_mul]
    rw [h', h]
    ring

/-- The weak transpose generator graph of a rescaled field. -/
theorem clr_transposeGeneratorPair_smul_iff {d : ℕ} (a : Vec d → Mat d) (i : Fin d)
    (ζ : ℂ) (κ : ℝ) (hκ : κ ≠ 0) (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexTransposeGeneratorPair (fun x => κ • a x) i ζ f g ↔
      IsPhysicalComplexTransposeGeneratorPair a i ζ f ((κ : ℂ)⁻¹ • g) := by
  have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
  have hent (x : Vec d) (j k : Fin d) :
      (((κ • a x) j k : ℝ) : ℂ) = (κ : ℂ) * (a x j k : ℂ) := by
    rw [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have hint (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      (∫ x, ((κ : ℂ)⁻¹ • g) x * v x) = (κ : ℂ)⁻¹ * ∫ x, g x * v x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul ((κ : ℂ)⁻¹) g] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have h1 (Gf Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      (∫ x, ∑ j, ∑ k, (κ : ℂ) * (a x k j : ℂ) * Gf k x * Gv j x) =
        (κ : ℂ) * ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * Gf k x * Gv j x := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h2 (Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      (∫ x, f x * (∑ j, (κ : ℂ) * (a x j i : ℂ) * Gv j x)) =
        (κ : ℂ) * ∫ x, f x * (∑ j, (a x j i : ℂ) * Gv j x) := by
    rw [← integral_const_mul]
    congr 1; funext x
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rintro ⟨Gf, hGf, hw⟩
    refine ⟨Gf, hGf, fun v Gv hv => ?_⟩
    rw [hint, hw v Gv hv]
    simp only [hent]
    rw [h1, h2]
    field_simp
  · rintro ⟨Gf, hGf, hw⟩
    refine ⟨Gf, hGf, fun v Gv hv => ?_⟩
    have h := hw v Gv hv
    rw [hint] at h
    simp only [hent]
    rw [h1, h2]
    have h' : (∫ x, g x * v x) = (κ : ℂ) * ((κ : ℂ)⁻¹ * ∫ x, g x * v x) := by
      rw [← mul_assoc, mul_inv_cancel₀ hκc, one_mul]
    rw [h', h]
    ring

/-- Reparametrizing time by a positive factor preserves right limits at zero. -/
theorem clr_tendsto_rescale {E : Type*} (κ : ℝ≥0) (hκ : 0 < κ)
    (φ : ℝ≥0 → E) (l : Filter E) :
    Tendsto (fun s => φ (κ * s)) (𝓝[>] (0 : ℝ≥0)) l ↔ Tendsto φ (𝓝[>] (0 : ℝ≥0)) l := by
  have hmap (c : ℝ≥0) (hc : 0 < c) : Tendsto (fun s : ℝ≥0 => c * s) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc' : Continuous (fun s : ℝ≥0 => c * s) := by fun_prop
      have h := hc'.tendsto (0 : ℝ≥0)
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hc hs
  constructor
  · intro h
    have h2 := h.comp (hmap κ⁻¹ (inv_pos.mpr hκ))
    refine h2.congr (fun s => ?_)
    simp only [Function.comp_apply, ← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul]
  · intro h
    exact h.comp (hmap κ hκ)

/-- Time rescaling of a physical forward evolution and its transpose. -/
theorem clr_physical_time_rescale {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))} (κ : ℝ≥0) (hκ : 0 < κ)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag) :
    IsPhysicalComplexSemigroup (fun x => (κ : ℝ) • a x) i ζ (fun s => P (κ * s)) ∧
    IsPhysicalComplexTransposeSemigroup (fun x => (κ : ℝ) • a x) i ζ
      (fun s => P (κ * s)) (fun s => Pdag (κ * s)) := by
  have hκr : (κ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hκ)
  have hκc : ((κ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκr
  have hcoef (s : ℝ≥0) : (((s : ℝ) : ℂ))⁻¹ = ((κ : ℝ) : ℂ) * ((((κ * s : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
    by_cases hs : s = 0
    · subst hs; simp
    · have hs' : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
      push_cast
      field_simp
  have hgen {T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))} (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
      Tendsto (fun s : ℝ≥0 => ((s : ℝ) : ℂ)⁻¹ • (T (κ * s) f - f)) (𝓝[>] 0) (𝓝 g) ↔
        Tendsto (fun s : ℝ≥0 => ((s : ℝ) : ℂ)⁻¹ • (T s f - f)) (𝓝[>] 0)
          (𝓝 ((((κ : ℝ) : ℂ))⁻¹ • g)) := by
    have heq : (fun s : ℝ≥0 => ((s : ℝ) : ℂ)⁻¹ • (T (κ * s) f - f)) =
        fun s => ((κ : ℝ) : ℂ) • ((fun u : ℝ≥0 => ((u : ℝ) : ℂ)⁻¹ • (T u f - f)) (κ * s)) := by
      funext s
      simp only [smul_smul, hcoef s]
    rw [heq]
    constructor
    · intro h
      have h1 := h.const_smul ((((κ : ℝ) : ℂ))⁻¹)
      simp only [inv_smul_smul₀ hκc] at h1
      exact (clr_tendsto_rescale κ hκ _ _).mp h1
    · intro h
      have h1 := ((clr_tendsto_rescale κ hκ _ _).mpr h).const_smul (((κ : ℝ) : ℂ))
      simpa only [smul_inv_smul₀ hκc] using h1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hP.1
  · intro s t
    simp only [mul_add]
    exact hP.2.1 _ _
  · intro f
    exact (hP.2.2.1 f).comp (continuous_const.mul continuous_id)
  · intro f g
    rw [hgen, hP.2.2.2, clr_generatorPair_smul_iff a i ζ (κ : ℝ) hκr]
  · simpa using hPdag.1
  · intro s t
    simp only [mul_add]
    exact hPdag.2.1 _ _
  · intro f
    exact (hPdag.2.2.1 f).comp (continuous_const.mul continuous_id)
  · intro f g
    rw [hgen, hPdag.2.2.2.1, clr_transposeGeneratorPair_smul_iff a i ζ (κ : ℝ) hκr]
  · intro t f g
    exact hPdag.2.2.2.2 (κ * t) f g

end EinsteinFull
