import EinsteinFull.Calculus.S2LateScalarSupport

/-!
# Support for the early clock smoothing (clause 2)

Decision-independent estimates for `e:clock-early`: the forced homogeneous average of a
difference `W^ζ_τ - W^0_τ` is controlled by the unforced Gaussian average at half the
propagation time, exactly the form supplied by `e:clock-average`.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

theorem norm_smul_forced_average_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {s : ℝ}
    (hs : 0 < s) (ξ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖ξ • homogeneousAverage Q ⟨0, by omega⟩ s hs ξ f‖ ≤
      ‖ξ‖ * (Real.exp (sourceReducedBound Λ₀ * ‖ξ‖ ^ 2 * s) *
        ‖gaussianAverage hd Q (s / 2) (half_pos hs) f‖) := by
  rw [norm_smul, Blueprint.UnforcedIdentification.homogeneousAverage_half_split hd Q s hs ξ f]
  exact mul_le_mul_of_nonneg_left
    (norm_outer_half_le Q s hs ξ (gaussianAverage hd Q (s / 2) (half_pos hs) f) hd)
    (norm_nonneg _)

theorem half_rpow_le {T τ : ℝ} (hT : 0 < T) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T / 2) (d : ℕ) :
    ((T - τ) / 2) ^ (-(d : ℝ) / 4) ≤ (4 : ℝ) ^ ((d : ℝ) / 4) * T ^ (-((d : ℝ) / 4)) := by
  have hle : T / 4 ≤ (T - τ) / 2 := by linarith
  have hxpos : 0 < T / 4 := by positivity
  have hpos : 0 < (T - τ) / 2 := by linarith
  rw [show -(d : ℝ) / 4 = -((d : ℝ) / 4) by ring, Real.rpow_neg hpos.le, Real.rpow_neg hT.le]
  calc (((T - τ) / 2) ^ ((d : ℝ) / 4))⁻¹ ≤ ((T / 4) ^ ((d : ℝ) / 4))⁻¹ :=
      inv_anti₀ (Real.rpow_pos_of_pos hxpos _) (Real.rpow_le_rpow hxpos.le hle (by positivity))
    _ = _ := by
      rw [Real.div_rpow hT.le (by norm_num), inv_div]
      ring

/-- Clause 2 of `e:clock-early` from the half-time Gaussian average bound of `e:clock-average`. -/
theorem clock_forced_difference_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {T τ Cc : ℝ}
    (hT : 0 < T) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T / 2) (hs : 0 < T - τ) (hCc : 0 ≤ Cc)
    (f : Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ)
    (hg : ‖gaussianAverage hd Q ((T - τ) / 2) (half_pos hs) f‖ ≤
      Cc * ‖ζ‖ * Real.sqrt τ * ((T - τ) / 2) ^ (-(d : ℝ) / 4)) :
    ‖ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - τ) hs ζ f‖ ≤
      Cc * (4 : ℝ) ^ ((d : ℝ) / 4) *
        Real.exp ((sourceReducedBound Λ₀ + 1) * ‖ζ‖ ^ 2 * T) *
          T ^ (-(1 / 2 + (d : ℝ) / 4)) * Real.sqrt (τ / T) := by
  have hK := sourceReducedBound_pos_of_law Q
  have hr : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hrr : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have hsq : Real.sqrt τ = Real.sqrt (τ / T) * Real.sqrt T := by
    rw [Real.sqrt_div hτ0, div_mul_cancel₀ _ hr.ne']
  have h1 := norm_smul_forced_average_le hd Q hs ζ f
  have he : Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * (T - τ)) ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hpow := half_rpow_le hT hτ0 hτT d
  have hy : 0 ≤ (4 : ℝ) ^ ((d : ℝ) / 4) * T ^ (-((d : ℝ) / 4)) := by positivity
  have hxe : ‖ζ‖ ^ 2 * T ≤ Real.exp (‖ζ‖ ^ 2 * T) := by
    have := Real.add_one_le_exp (‖ζ‖ ^ 2 * T)
    linarith
  have hexp : Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) * Real.exp (‖ζ‖ ^ 2 * T) =
      Real.exp ((sourceReducedBound Λ₀ + 1) * ‖ζ‖ ^ 2 * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hTa : T ^ (-(1 / 2 + (d : ℝ) / 4)) = (Real.sqrt T)⁻¹ * T ^ (-((d : ℝ) / 4)) := by
    rw [show -(1 / 2 + (d : ℝ) / 4) = -(1 / 2 : ℝ) + -((d : ℝ) / 4) by ring,
      Real.rpow_add hT, Real.rpow_neg hT.le (1 / 2 : ℝ), ← Real.sqrt_eq_rpow]
  have hnorm : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have hmid : ‖ζ‖ * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * (T - τ)) *
        ‖gaussianAverage hd Q ((T - τ) / 2) (half_pos hs) f‖) ≤
      ‖ζ‖ * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) *
        (Cc * ‖ζ‖ * Real.sqrt τ * ((4 : ℝ) ^ ((d : ℝ) / 4) * T ^ (-((d : ℝ) / 4))))) := by
    apply mul_le_mul_of_nonneg_left _ hnorm
    apply mul_le_mul he _ (norm_nonneg _) (Real.exp_pos _).le
    exact hg.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  refine h1.trans (hmid.trans ?_)
  have hid : ‖ζ‖ * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) *
        (Cc * ‖ζ‖ * Real.sqrt τ * ((4 : ℝ) ^ ((d : ℝ) / 4) * T ^ (-((d : ℝ) / 4))))) =
      Cc * (4 : ℝ) ^ ((d : ℝ) / 4) * Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) *
        (‖ζ‖ ^ 2 * T) * ((Real.sqrt T)⁻¹ * T ^ (-((d : ℝ) / 4))) * Real.sqrt (τ / T) := by
    have key : T * (Real.sqrt T)⁻¹ = Real.sqrt T := by
      rw [mul_inv_eq_iff_eq_mul₀ hr.ne']
      exact (Real.mul_self_sqrt hT.le).symm
    rw [hsq]
    linear_combination (-(Cc * (4 : ℝ) ^ ((d : ℝ) / 4) *
      Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) * ‖ζ‖ ^ 2 * Real.sqrt (τ / T) *
        T ^ (-((d : ℝ) / 4)))) * key
  rw [hid, hTa, ← hexp]
  have hq : 0 ≤ Cc * (4 : ℝ) ^ ((d : ℝ) / 4) * Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T) *
      ((Real.sqrt T)⁻¹ * T ^ (-((d : ℝ) / 4))) * Real.sqrt (τ / T) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hxe hq]

end EinsteinFull
