import EinsteinRelation.Correctors.UniformAnisotropicBandMass
import EinsteinRelation.Correctors.AnisotropicBandSharpMoments

/-! # Uniform sharp moments for anisotropic Poisson bands

Source: `paper/main.tex:1033–1041`. Both the mass estimates and the actual
stationary heat transfer are uniform before choosing the coordinate map.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- The Laplacian masses are uniform over all bounded coordinate maps
(`paper/main.tex:1033–1035`). -/
theorem anisotropicBand_uniform_laplacian_bound {d : ℕ} (hd : 2 ≤ d)
    {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(T (unitVector i)) j| ≤ b) →
      ∀ cs : List (Fin d), cs.length = n → ∀ r : ℝ, 0 < r →
      (∫ x : Vec d, |coordLaplacian (coordinateIterate cs (anisotropicBandKernel T r)) x|) ≤
        C / r ^ n := by
  obtain ⟨A, hA, hbound⟩ := anisotropicBandKernel_uniform_derivative_bound hd hb (n + 2)
  refine ⟨1 + d * A, by positivity, fun T hT cs hcs r hr => ?_⟩
  have hK := KernelCalculus.contDiff_coordinateIterate (anisotropicBandKernel_contDiff hd T hr) cs
  have hKc := KernelCalculus.hasCompactSupport_coordinateIterate
    (anisotropicBandKernel_hasCompactSupport hd T hr) cs
  apply (integral_abs_coordLaplacian_le hK hKc).trans
  have hs (i : Fin d) :
      (∫ x : Vec d, |coordinateIterate [i, i] (coordinateIterate cs (anisotropicBandKernel T r)) x|)
        ≤ A / r ^ n := by
    have hh := hbound T hT ([i, i] ++ cs) (by simp [hcs]) r hr
    change (∫ x : Vec d, |coordinateIterate ([i, i] ++ cs) (anisotropicBandKernel T r) x|) ≤ _
    convert hh using 1
    rw [pow_add]
    field_simp [hr.ne']
  calc
    _ ≤ ∑ _i : Fin d, A / r ^ n := Finset.sum_le_sum fun i _ => hs i
    _ = ((d : ℝ) * A) / r ^ n := by simp [mul_div_assoc]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le _)

/-- Uniform sharp moments of every derivative of a fixed order of the
actual anisotropic bands (`paper/main.tex:1033–1041`). -/
theorem eLpNorm_anisotropicBand_uniform_le {d : ℕ} (hd : 2 ≤ d)
    {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Vec d ≃L[ℝ] Vec d),
      (∀ i j : Fin d, |(T (unitVector i)) j| ≤ b) →
      ∀ cs : List (Fin d), cs.length = n →
      ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q],
      IsStationary Q → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M r R : ℝ), 0 < M → 0 < r → 0 < R → r ≤ R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      eLpNorm (horizontalMollify (coordinateIterate cs (anisotropicBandKernel T r)) f) p Q ≤
        ENNReal.ofReal (C * M * (r / r ^ n)) := by
  obtain ⟨A, hA, hmass⟩ := anisotropicBandKernel_uniform_derivative_bound hd hb n
  obtain ⟨B, hB, hlap⟩ := anisotropicBand_uniform_laplacian_bound hd hb n
  refine ⟨2 * A + 3 * B, by positivity,
    fun T hT cs hcs Q _ hQ p hp hpt M r R hM hr hR hrR f hf hheat => ?_⟩
  have hK := KernelCalculus.contDiff_coordinateIterate (anisotropicBandKernel_contDiff hd T hr) cs
  have hKc := KernelCalculus.hasCompactSupport_coordinateIterate
    (anisotropicBandKernel_hasCompactSupport hd T hr) cs
  have ht := horizontalMollify_heatTransfer_ae hQ hK hKc hf
    (integrable_of_heatSmoothed_bound hp hf hheat) (sq_pos_of_pos hr)
  exact eLpNorm_convolution_le_of_heatTransfer hQ hp hpt hK.continuous.measurable
    (hK.continuous.integrable_of_hasCompactSupport hKc)
    (contDiff_coordLaplacian hK).continuous.measurable (integrable_coordLaplacian_of_smooth hK hKc)
    hA hB hM hr hR (pow_pos hr n) hrR
    (hmass T hT cs hcs r hr) (hlap T hT cs hcs r hr) hf hheat ht

end EinsteinRelation.Correctors
