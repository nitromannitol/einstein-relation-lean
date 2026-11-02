import EinsteinFull.Calculus.C5ClockDerivativeKernelDecay
import EinsteinFull.Work.W4.HomogeneousGaussianTimeIntegralSupport

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

/-- The actual homogeneous clock propagation changes by the relative time increment. -/
theorem clock_homogeneous_time_replacement

    : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (T τ : ℝ) (hT : 0 < T) (ht : 0 < T - τ),
      2 ≤ T → 0 ≤ τ → 2 * τ ≤ T → ∀ ζ : ℂ,
      ‖ζ • (homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht ζ (centeredComplexLp Q μ) -
          homogeneousAverage Q ⟨0, by omega⟩ T hT ζ (centeredComplexLp Q μ))‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4)) * (τ / T) := by
  intro d hd D
  obtain ⟨A, hA, hrate⟩ := clock_gaussian_time_derivative_decay d D
  have hforce (T z : ℝ) (hT : 0 < T) (hz : 0 ≤ z) :
      z * (T⁻¹ + z ^ 2) ≤
        Real.exp (2 * z ^ 2 * T) * T ^ (-(3 / 2 : ℝ)) := by
    let x := z * Real.sqrt T
    have hx : 0 ≤ x := mul_nonneg hz (Real.sqrt_nonneg T)
    have hx2 : x ^ 2 = z ^ 2 * T := by
      dsimp only [x]
      rw [mul_pow, Real.sq_sqrt hT.le]
    have he : 1 + x ^ 2 ≤ Real.exp (x ^ 2) := by
      linarith only [Real.add_one_le_exp (x ^ 2)]
    have hxe : x ≤ Real.exp (x ^ 2) := by
      have : x ≤ 1 + x ^ 2 := by nlinarith only [sq_nonneg (x - 1 / 2)]
      exact this.trans he
    have hp : x * (1 + x ^ 2) ≤ Real.exp (2 * z ^ 2 * T) := by
      calc
        _ ≤ Real.exp (x ^ 2) * Real.exp (x ^ 2) :=
          mul_le_mul hxe he (by positivity) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, hx2]; congr 1; ring
    have hr : Real.sqrt T * T ^ (-(3 / 2 : ℝ)) = T⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT]
      convert Real.rpow_neg_one T using 1; norm_num
    calc
      _ = (x * (1 + x ^ 2)) * T ^ (-(3 / 2 : ℝ)) := by
        rw [hx2]
        dsimp only [x]
        calc
          _ = z * (1 + z ^ 2 * T) * T⁻¹ := by field_simp
          _ = _ := by rw [← hr]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hT.le _)
  let p := (d : ℝ) / 4
  let B := 2 * A * (2 : ℝ) ^ p
  let C := B + A + 3
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q hQ μ hμ T τ hT ht hT2 hτ hhalf ζ
  have hinter (t : ℝ) (hmem : t ∈ Set.Icc (T - τ) T) :
      ‖ζ‖ * ‖homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ ζ
        (centeredComplexLp Q μ) t‖ ≤
        B * Real.exp ((A + 2) * ‖ζ‖ ^ 2 * T) * T ^ (-(3 / 2 + p)) := by
    have htt : 0 < t := ht.trans_le hmem.1
    have hlow : T / 2 ≤ t := by linarith [hmem.1]
    have hi : t⁻¹ ≤ 2 * T⁻¹ := by
      have := inv_anti₀ (half_pos hT) hlow
      simpa only [inv_div, inv_inv, div_eq_mul_inv, mul_inv_rev, inv_inv] using this
    have htinv : t⁻¹ + ‖ζ‖ ^ 2 ≤ 2 * (T⁻¹ + ‖ζ‖ ^ 2) := by
      nlinarith only [hi, sq_nonneg ‖ζ‖]
    have hpow : t ^ (-p) ≤ (2 : ℝ) ^ p * T ^ (-p) := by
      calc
        _ ≤ (T / 2) ^ (-p) := Real.rpow_le_rpow_of_nonpos (half_pos hT) hlow (neg_nonpos.mpr hp)
        _ = _ := by
          rw [Real.div_rpow hT.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          simp only [div_inv_eq_mul]
          ring
    have hexp : Real.exp (A * ‖ζ‖ ^ 2 * t) ≤
        Real.exp (A * ‖ζ‖ ^ 2 * T) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hmem.2 (by positivity)
    calc
      _ ≤ ‖ζ‖ * (A * (t⁻¹ + ‖ζ‖ ^ 2) *
          Real.exp (A * ‖ζ‖ ^ 2 * t) * t ^ (-p)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [p, neg_div] using hrate Q hQ μ hμ ⟨0, by omega⟩ ζ t htt) (norm_nonneg _)
      _ ≤ ‖ζ‖ * (A * (2 * (T⁻¹ + ‖ζ‖ ^ 2)) *
          Real.exp (A * ‖ζ‖ ^ 2 * T) * ((2 : ℝ) ^ p * T ^ (-p))) := by
        gcongr
      _ = B * (‖ζ‖ * (T⁻¹ + ‖ζ‖ ^ 2)) *
          Real.exp (A * ‖ζ‖ ^ 2 * T) * T ^ (-p) := by dsimp only [B]; ring
      _ ≤ B * (Real.exp (2 * ‖ζ‖ ^ 2 * T) * T ^ (-(3 / 2 : ℝ))) *
          Real.exp (A * ‖ζ‖ ^ 2 * T) * T ^ (-p) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT.le _)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hforce T ‖ζ‖ hT (norm_nonneg _)) hB
      _ = _ := by
        rw [show (A + 2) * ‖ζ‖ ^ 2 * T =
          2 * ‖ζ‖ ^ 2 * T + A * ‖ζ‖ ^ 2 * T by ring, Real.exp_add,
          show -(3 / 2 + p) = -(3 / 2 : ℝ) + -p by ring, Real.rpow_add hT]
        ring
  let f : ℝ → Lp ℂ 2 (reducedLaw Q) := fun t => ζ •
    homogeneousGaussianEvolution Q ⟨0, by omega⟩ ζ
      ⟨max t 0, le_max_right _ _⟩ (centeredComplexLp Q μ)
  have hdiff (t : ℝ) (htt : 0 < t) : HasDerivAt f
      (ζ • homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ ζ
        (centeredComplexLp Q μ) t) t := by
    simpa only [f, homogeneousGaussianEvolutionTimeDerivative, dite_eq_left htt] using!
      (hasDerivAt_homogeneousGaussianEvolution_time Q ⟨0, by omega⟩ ζ
        (centeredComplexLp Q μ) t htt).const_smul ζ
  have hbound (t : ℝ) (hmem : t ∈ Set.Icc (T - τ) T) :
      ‖deriv f t‖ ≤ C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(3 / 2 + p)) := by
    rw [(hdiff t (ht.trans_le hmem.1)).deriv, norm_smul]
    refine (hinter t hmem).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT.le _)
    apply mul_le_mul _ _ (Real.exp_pos _).le hC.le
    · dsimp only [C]; linarith
    · apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (sq_nonneg ‖ζ‖)) hT.le
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t hmem => (hdiff t (ht.trans_le hmem.1)).differentiableAt)
    hbound (convex_Icc (T - τ) T)
    (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  have he (t : ℝ) (htt : 0 < t) : f t = ζ •
      homogeneousAverage Q ⟨0, by omega⟩ t htt ζ (centeredComplexLp Q μ) := by
    dsimp only [f]
    erw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ ζ _
      (by simpa only [max_eq_left htt.le] using! htt)]
    simp only [max_eq_left htt.le]
    rfl
  rw [he T hT, he (T - τ) ht, ← smul_sub] at h
  simp only [show T - (T - τ) = τ by ring,
    Real.norm_eq_abs, abs_of_nonneg hτ] at h
  have hpowers : T ^ (-(3 / 2 + p)) =
      T ^ (-(1 / 2 + (d : ℝ) / 4)) * T⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hT]
    congr 1
    dsimp only [p]
    ring
  calc
    _ ≤ _ := by simpa only [norm_smul, norm_sub_rev] using h
    _ = _ := by rw [hpowers]; ring


end EinsteinFull.Blueprint
