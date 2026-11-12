import EinsteinRelation.Correctors.RadialBandSharpMoments

/-! # Sharp moments of the large-scale averaging remainder

Source: `paper/main.tex:1041–1042`. The same heat-transfer argument applied
to the normalized averaging kernel gives the inverse-scale remainder bound.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Exact dilation of the normalized radial averaging kernel
(`paper/main.tex:1003–1007`). -/
theorem radialAverage_eq_scaled {r : ℝ} (hr : 0 < r) :
    radialAverage d r = fun x : Vec d => (r ^ d)⁻¹ * radialAverage d 1 (r⁻¹ • x) := by
  funext x
  simp only [radialAverage, scaledProfile, one_pow, inv_one, one_mul,
    TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr), div_eq_inv_mul]

/-- Exact derivative `L¹` scaling for the averaging kernel
(`paper/main.tex:1041–1042`). -/
theorem integral_abs_coordinateIterate_radialAverage {r : ℝ} (hr : 0 < r)
    (cs : List (Fin d)) :
    (∫ x : Vec d, |coordinateIterate cs (radialAverage d r) x|) =
      (r ^ cs.length)⁻¹ * ∫ x : Vec d, |coordinateIterate cs (radialAverage d 1) x| := by
  rw [radialAverage_eq_scaled hr,
    KernelCalculus.coordinateIterate_const_mul_comp_smul
      (radialAverage_contDiff (by norm_num : (0 : ℝ) < 1))]
  simp only [abs_mul, abs_inv, abs_pow, abs_of_pos hr]
  rw [integral_const_mul]
  have hchange := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x : Vec d => |coordinateIterate cs (radialAverage d 1) x|) r⁻¹
  simp only [Module.finrank_pi, Fintype.card_fin, inv_pow, inv_inv, smul_eq_mul,
    abs_of_pos (pow_pos hr d)] at hchange
  rw [hchange, inv_pow]
  field_simp

/-- Every averaging-kernel derivative has a uniform dilation bound
(`paper/main.tex:1041–1042`). -/
theorem radialAverage_derivative_bounds (d : ℕ) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      Integrable (coordinateIterate cs (radialAverage d r)) volume ∧
      (∫ x, |coordinateIterate cs (radialAverage d r) x|) ≤ C / r ^ cs.length := by
  let A : ℝ := ∫ x, |coordinateIterate cs (radialAverage d 1) x|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  refine ⟨A + 1, by positivity, fun r hr => ⟨?_, ?_⟩⟩
  · exact KernelCalculus.integrable_coordinateIterate (radialAverage_contDiff hr)
      (radialAverage_hasCompactSupport hr) cs
  · rw [integral_abs_coordinateIterate_radialAverage hr]
    change (r ^ cs.length)⁻¹ * A ≤ (A + 1) / r ^ cs.length
    rw [div_eq_mul_inv, mul_comm _ A]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The Laplacian of the averaging kernel has `L¹` mass of order `R⁻²`
(`paper/main.tex:1041–1042`). -/
theorem radialAverage_laplacian_bound (d : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 0 < R →
      (∫ x : Vec d, |coordLaplacian (radialAverage d R) x|) ≤ B / R ^ 2 := by
  choose C hC hbound using fun i : Fin d => radialAverage_derivative_bounds d [i, i]
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨1 + ∑ i, C i, by linarith, fun R hR => ?_⟩
  apply (integral_abs_coordLaplacian_le (radialAverage_contDiff hR)
    (radialAverage_hasCompactSupport hR)).trans
  calc
    _ ≤ ∑ i, C i / R ^ 2 := Finset.sum_le_sum fun i _ => (hbound i R hR).2
    _ = (∑ i, C i) / R ^ 2 := (Finset.sum_div _ _ _).symm
    _ ≤ (1 + ∑ i, C i) / R ^ 2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The actual large-scale radial averaging remainder has inverse-scale
moments from scalar averaging alone (`paper/main.tex:1041–1042`). -/
theorem eLpNorm_radialAverage_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q],
      IsStationary Q → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
      ∀ (M R : ℝ), 0 < M → 0 < R →
      ∀ (f : FieldPair d → ℝ), Measurable f →
      (∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) →
      eLpNorm (horizontalMollify (radialAverage d R) f) p Q ≤ ENNReal.ofReal (C * M / R) := by
  obtain ⟨B, hB, hbound⟩ := radialAverage_laplacian_bound d
  refine ⟨4 + 3 * B, by positivity,
    fun Q _ hQ p hp hpt M R hM hR f hf hheat => ?_⟩
  have hK := radialAverage_contDiff (d := d) hR
  have hKc := radialAverage_hasCompactSupport (d := d) hR
  have hmass : (∫ x : Vec d, |radialAverage d R x|) ≤ 2 * (R ^ 2 / R ^ 2) := by
    simp only [abs_of_nonneg (radialAverage_nonneg d R hR _),
      integral_radialAverage hR, div_self (pow_ne_zero 2 hR.ne')]
    norm_num
  have htransfer := horizontalMollify_heatTransfer_ae hQ hK hKc hf
    (integrable_of_heatSmoothed_bound hp hf hheat) (sq_pos_of_pos hR)
  have hb := eLpNorm_convolution_le_of_heatTransfer hQ hp hpt hK.continuous.measurable
    (hK.continuous.integrable_of_hasCompactSupport hKc)
    (contDiff_coordLaplacian hK).continuous.measurable (integrable_coordLaplacian_of_smooth hK hKc)
    (by norm_num : (0 : ℝ) < 2) hB hM hR hR (sq_pos_of_pos hR) le_rfl
    hmass (hbound R hR) hf hheat htransfer
  convert hb using 1
  congr 1
  field_simp
  ring

end EinsteinRelation.Correctors
