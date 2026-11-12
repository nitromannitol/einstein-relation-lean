import EinsteinRelation.Correctors.AnisotropicDyadicKernels
import EinsteinRelation.Correctors.RadialBandSharpMoments

/-! # Sharp moments of the anisotropic Poisson bands

Source: `paper/main.tex:1033–1041`. The actual stationary heat-transfer
identity gives the one-power gain for every anisotropic band derivative.
The constants here are for a fixed coordinate map; uniformity over elliptic
coordinate maps is a separate quantitative obligation.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
variable {d : ℕ}

/-- For a fixed coordinate map, the Laplacian of a derivative band kernel has scaling
`r^(-k)` (`paper/main.tex:1033–1035`). -/
theorem anisotropicBand_laplacian_derivative_bound (hd : 2 ≤ d)
    (T : Vec d ≃L[ℝ] Vec d) (cs : List (Fin d)) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r →
      Integrable (coordLaplacian (coordinateIterate cs (anisotropicBandKernel T r))) volume ∧
      (∫ x, |coordLaplacian (coordinateIterate cs (anisotropicBandKernel T r)) x|) ≤
        B / r ^ cs.length := by
  choose C hC hbound using fun i : Fin d =>
    anisotropicBandKernel_derivative_bounds hd T ([i, i] ++ cs)
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨(∑ i, C i) + 1, by linarith, fun r hr => ?_⟩
  have hK := KernelCalculus.contDiff_coordinateIterate (anisotropicBandKernel_contDiff hd T hr) cs
  have hKc := KernelCalculus.hasCompactSupport_coordinateIterate
    (anisotropicBandKernel_hasCompactSupport hd T hr) cs
  refine ⟨integrable_coordLaplacian_of_smooth hK hKc,
    (integral_abs_coordLaplacian_le hK hKc).trans ?_⟩
  have heq (i : Fin d) : coordinateIterate [i, i] (coordinateIterate cs (anisotropicBandKernel T r)) =
      coordinateIterate ([i, i] ++ cs) (anisotropicBandKernel T r) := rfl
  have hscale (i : Fin d) : r ^ 2 / r ^ ([i, i] ++ cs).length = 1 / r ^ cs.length := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd]
    rw [pow_add]
    field_simp [hr.ne']
  simp_rw [heq, fun i => (hbound i r hr).2, hscale]
  simp only [mul_one_div, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le _)

/-- The actual anisotropic derivative convolution has sharp scale
`r^(1-k)` for a fixed coordinate map (`paper/main.tex:1033–1041`). -/
theorem eLpNorm_anisotropicBand_le (hd : 2 ≤ d)
    (T : Vec d ≃L[ℝ] Vec d) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q],
      IsStationary Q → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M r R : ℝ), 0 < M → 0 < r → 0 < R → r ≤ R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      eLpNorm (horizontalMollify (coordinateIterate cs (anisotropicBandKernel T r)) f) p Q ≤
        ENNReal.ofReal (C * M * (r / r ^ cs.length)) := by
  obtain ⟨A, hA, hAbound⟩ := anisotropicBandKernel_derivative_bounds hd T cs
  obtain ⟨B, hB, hBbound⟩ := anisotropicBand_laplacian_derivative_bound hd T cs
  refine ⟨2 * (A + 1) + 3 * B, by positivity,
    fun Q _ hQ p hp hpt M r R hM hr hR hrR f hf hheat => ?_⟩
  have hK := KernelCalculus.contDiff_coordinateIterate (anisotropicBandKernel_contDiff hd T hr) cs
  have hmass : (∫ x, |coordinateIterate cs (anisotropicBandKernel T r) x|) ≤
      (A + 1) * (r ^ 2 / r ^ cs.length) := by
    rw [(hAbound r hr).2]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have htransfer := horizontalMollify_heatTransfer_ae hQ hK
    (KernelCalculus.hasCompactSupport_coordinateIterate
      (anisotropicBandKernel_hasCompactSupport hd T hr) cs)
    hf (integrable_of_heatSmoothed_bound hp hf hheat) (sq_pos_of_pos hr)
  exact eLpNorm_convolution_le_of_heatTransfer hQ hp hpt hK.continuous.measurable
    (hAbound r hr).1 (contDiff_coordLaplacian hK).continuous.measurable
    (hBbound r hr).1 (by positivity) hB hM hr hR (by positivity) hrR
    hmass (hBbound r hr).2 hf hheat htransfer


end EinsteinRelation.Correctors
