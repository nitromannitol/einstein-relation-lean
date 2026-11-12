import EinsteinRelation.Correctors.RadialDyadicKernels
import EinsteinRelation.Correctors.HeatTransferMomentBound

/-! # Derivative moment bounds for radial dyadic bands

Source: `paper/main.tex:1033–1041`. The all-order kernel scaling controls
the Laplacian of each derivative kernel. Combined with heat transfer, it
gives the scale `r / r^k` for the corresponding stationary convolution.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The Laplacian of a compact smooth kernel is integrable
(`paper/main.tex:1030–1035`). -/
theorem integrable_coordLaplacian_of_smooth {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) :
    Integrable (coordLaplacian K) volume :=
  integrable_finset_sum _ fun i _ => KernelCalculus.integrable_coordinateIterate hK hKc [i, i]

/-- The spatial Laplacian of a compact smooth kernel is smooth
(`paper/main.tex:1030–1035`). -/
theorem contDiff_coordLaplacian {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) : ContDiff ℝ (⊤ : ℕ∞) (coordLaplacian K) :=
  ContDiff.sum fun i _ => KernelCalculus.contDiff_coordinateIterate hK [i, i]

/-- The `L¹` mass of the Laplacian is bounded by the sum of the masses of
the pure second derivatives (`paper/main.tex:1033–1035`). -/
theorem integral_abs_coordLaplacian_le {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) :
    (∫ x, |coordLaplacian K x|) ≤ ∑ i : Fin d, ∫ x, |coordinateIterate [i, i] K x| := by
  have hi (i : Fin d) := KernelCalculus.integrable_coordinateIterate hK hKc [i, i]
  rw [← integral_finset_sum _ fun i _ => (hi i).abs]
  apply integral_mono (integrable_coordLaplacian_of_smooth hK hKc).abs
    (integrable_finset_sum _ fun i _ => (hi i).abs)
  intro x
  exact Finset.abs_sum_le_sum_abs _ _

/-- The Laplacian of a derivative band kernel has the required scaling
`r^(-k)` (`paper/main.tex:1033–1035`). -/
theorem radialBand_laplacian_derivative_bound (hd : 2 ≤ d) (cs : List (Fin d)) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r →
      Integrable (coordLaplacian (coordinateIterate cs (radialBandKernel d r))) volume ∧
      (∫ x, |coordLaplacian (coordinateIterate cs (radialBandKernel d r)) x|) ≤
        B / r ^ cs.length := by
  choose C hC hbound using fun i : Fin d =>
    radialBandKernel_derivative_bounds hd ([i, i] ++ cs)
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨(∑ i, C i) + 1, by linarith, fun r hr => ?_⟩
  have hK := KernelCalculus.contDiff_coordinateIterate (radialBandKernel_contDiff hd hr) cs
  have hKc := KernelCalculus.hasCompactSupport_coordinateIterate
    (radialBandKernel_hasCompactSupport hd hr) cs
  refine ⟨integrable_coordLaplacian_of_smooth hK hKc,
    (integral_abs_coordLaplacian_le hK hKc).trans ?_⟩
  have heq (i : Fin d) : coordinateIterate [i, i] (coordinateIterate cs (radialBandKernel d r)) =
      coordinateIterate ([i, i] ++ cs) (radialBandKernel d r) := rfl
  have hscale (i : Fin d) : r ^ 2 / r ^ ([i, i] ++ cs).length = 1 / r ^ cs.length := by
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd]
    rw [pow_add]
    field_simp [hr.ne']
  simp_rw [heq, fun i => (hbound i r hr).2, hscale]
  simp only [mul_one_div, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le _)

/-- The radial derivative band has the sharp moment scale once its
heat-transfer identity is supplied (`paper/main.tex:1033–1041`). The
remaining time-integrated identity is an internal proof obligation. -/
theorem eLpNorm_radialBand_le_of_heatTransfer (hd : 2 ≤ d) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Measure (FieldPair d)) [SFinite Q],
      IsStationary Q → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M r R : ℝ), 0 < M → 0 < r → 0 < R → r ≤ R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      (horizontalMollify (coordinateIterate cs (radialBandKernel d r)) f =ᵐ[Q] fun ω =>
        horizontalMollify (coordinateIterate cs (radialBandKernel d r)) (heatSmoothed (r ^ 2) f) ω -
          ∫ t in (0 : ℝ)..r ^ 2,
            horizontalMollify (coordLaplacian (coordinateIterate cs (radialBandKernel d r)))
              (heatSmoothed t f) ω) →
      eLpNorm (horizontalMollify (coordinateIterate cs (radialBandKernel d r)) f) p Q ≤
        ENNReal.ofReal (C * M * (r / r ^ cs.length)) := by
  obtain ⟨A, hA, hAbound⟩ := radialBandKernel_derivative_bounds hd cs
  obtain ⟨B, hB, hBbound⟩ := radialBand_laplacian_derivative_bound hd cs
  refine ⟨2 * (A + 1) + 3 * B, by positivity,
    fun Q _ hQ p hp hpt M r R hM hr hR hrR f hf hheat htransfer => ?_⟩
  have hK := KernelCalculus.contDiff_coordinateIterate (radialBandKernel_contDiff hd hr) cs
  have hmass : (∫ x, |coordinateIterate cs (radialBandKernel d r) x|) ≤
      (A + 1) * (r ^ 2 / r ^ cs.length) := by
    rw [(hAbound r hr).2]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  exact eLpNorm_convolution_le_of_heatTransfer hQ hp hpt hK.continuous.measurable
    (hAbound r hr).1 (contDiff_coordLaplacian hK).continuous.measurable
    (hBbound r hr).1 (by positivity) hB hM hr hR (by positivity) hrR
    hmass (hBbound r hr).2 hf hheat htransfer

end EinsteinRelation.Correctors
