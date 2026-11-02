import EinsteinFull.Calculus.C14ClockUnforcedGaussianSmoothing
import EinsteinFull.Calculus.S2ClockEarlySupport

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem clock_early_ratio_bound {T τ : ℝ} (hT : 0 < T) (hτ : 0 ≤ τ)
    (hτT : 5 * τ ≤ T) :
    τ / ((T - τ) / 2) + Real.sqrt (τ / ((T - τ) / 2)) ≤
      6 * Real.sqrt (τ / T) := by
  have hs : 0 < (T - τ) / 2 := by linarith
  have hcomp : T / 4 ≤ (T - τ) / 2 := by linarith
  have hr : 0 ≤ τ / T := div_nonneg hτ hT.le
  have hr1 : τ / T ≤ 1 := (div_le_one hT).mpr (by linarith)
  have hrsqrt : τ / T ≤ Real.sqrt (τ / T) :=
    Real.le_sqrt hr hr |>.mpr (by nlinarith only [hr, hr1])
  have hq : τ / ((T - τ) / 2) ≤ 4 * (τ / T) := by
    calc
      _ ≤ τ / (T / 4) := div_le_div_of_nonneg_left hτ (by positivity) hcomp
      _ = _ := by ring
  have hsq : Real.sqrt (τ / ((T - τ) / 2)) ≤ 2 * Real.sqrt (τ / T) := by
    calc
      _ ≤ Real.sqrt (4 * (τ / T)) := Real.sqrt_le_sqrt hq
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  linarith

private theorem clock_early_force_bound {T z : ℝ} (hT : 0 < T) :
    z ≤ Real.exp (z ^ 2 * T) * (Real.sqrt T)⁻¹ := by
  let x := z * Real.sqrt T
  have hx2 : x ^ 2 = z ^ 2 * T := by
    dsimp only [x]
    rw [mul_pow, Real.sq_sqrt hT.le]
  have hxe : x ≤ Real.exp (z ^ 2 * T) := by
    have hx : x ≤ 1 + x ^ 2 := by nlinarith only [sq_nonneg (x - 1 / 2)]
    have he : 1 + x ^ 2 ≤ Real.exp (x ^ 2) := by
      linarith only [Real.add_one_le_exp (x ^ 2)]
    exact hx.trans (by simpa only [hx2] using he)
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  calc
    z = x * (Real.sqrt T)⁻¹ := by dsimp only [x]; field_simp [hs.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hxe (inv_nonneg.mpr hs.le)

/-- Propagate the actual unforced clock increment through the complex-force
homogeneous Gaussian average at a comparable macroscopic time. -/
theorem clock_unforced_early_propagation
    : ∀ (havg : node_e_u3A_clock_u2D_averageStmt)
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      ∀ (T : ℝ) (τ : ℝ≥0) (ht : 0 < T - (τ : ℝ)),
        t₀ ≤ (τ : ℝ) → 5 * (τ : ℝ) ≤ T →
      ∀ ζ : ℂ,
        ‖ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - (τ : ℝ)) ht ζ
          (centeredComplexLp Q (P 0 τ μ) - centeredComplexLp Q μ)‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1/2 + (d : ℝ)/4)) *
          Real.sqrt ((τ : ℝ)/T) := by
  intro havg d hd D
  obtain ⟨Cg, t₀, hCg, ht₀, hg⟩ := clock_unforced_full_gaussian_smoothing havg d hd D
  let B := 6 * Cg * (4 : ℝ)^((d : ℝ)/4)
  let C := max B (|sourceReducedBound D.ellipticity| + 2)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := hB.trans_le (le_max_left _ _)
  have hBC : B ≤ C := le_max_left _ _
  have hKC : sourceReducedBound D.ellipticity + 1 ≤ C := by
    calc
      _ ≤ |sourceReducedBound D.ellipticity| + 2 := by
        linarith only [le_abs_self (sourceReducedBound D.ellipticity)]
      _ ≤ C := le_max_right _ _
  refine ⟨C, t₀, hC, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP T τ ht hτ hτT ζ
  have hτ0 : 0 ≤ (τ : ℝ) := τ.coe_nonneg
  have hT : 0 < T := by linarith
  have hhalf : (τ : ℝ) ≤ T / 2 := by linarith
  have hscale : 2 * (τ : ℝ) ≤ (T - (τ : ℝ)) / 2 := by linarith
  let f := centeredComplexLp Q (P 0 τ μ) - centeredComplexLp Q μ
  have hgauss := hg Q hQ a μ ha hμ (P 0) (hP 0) τ hτ
    ((T - (τ : ℝ))/2) (half_pos ht) hscale
  have hratio := clock_early_ratio_bound hT hτ0 hτT
  have hpow := EinsteinFull.half_rpow_le hT hτ0 hhalf d
  have hK := sourceReducedBound_pos_of_law Q
  have hexp : Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * (T - (τ : ℝ))) ≤
      Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hgauss' : ‖gaussianAverage hd Q ((T - (τ : ℝ))/2) (half_pos ht) f‖ ≤
      B * T ^ (-((d : ℝ)/4)) * Real.sqrt ((τ : ℝ)/T) := by
    calc
      _ ≤ Cg * ((T - (τ : ℝ))/2) ^ (-(d : ℝ)/4) *
          ((τ : ℝ)/((T - (τ : ℝ))/2) + Real.sqrt ((τ : ℝ)/((T - (τ : ℝ))/2))) := hgauss
      _ ≤ Cg * ((4 : ℝ)^((d : ℝ)/4) * T^(-((d : ℝ)/4))) *
          (6 * Real.sqrt ((τ : ℝ)/T)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hCg.le) hratio
          (by positivity) (by positivity)
      _ = _ := by dsimp only [B]; ring
  have hTa : (Real.sqrt T)⁻¹ * T ^ (-((d : ℝ)/4)) =
      T ^ (-(1/2+(d : ℝ)/4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hT.le, ← Real.rpow_add hT]
    congr 1
    ring
  have heq : Real.exp (‖ζ‖ ^ 2 * T) *
      Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * T) =
      Real.exp ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖ ^ 2 * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ‖ζ‖ * (Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖ ^ 2 * (T - (τ : ℝ))) *
        ‖gaussianAverage hd Q ((T - (τ : ℝ))/2) (half_pos ht) f‖) :=
      EinsteinFull.norm_smul_forced_average_le hd Q ht ζ f
    _ ≤ (Real.exp (‖ζ‖^2*T) * (Real.sqrt T)⁻¹) *
        (Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖^2*T) *
          (B * T^(-((d : ℝ)/4)) * Real.sqrt ((τ : ℝ)/T))) :=
      mul_le_mul (clock_early_force_bound hT)
        (mul_le_mul hexp hgauss' (norm_nonneg _) (Real.exp_pos _).le)
        (by positivity) (by positivity)
    _ = B * Real.exp ((sourceReducedBound D.ellipticity + 1) * ‖ζ‖^2*T) *
        T^(-(1/2+(d : ℝ)/4)) * Real.sqrt ((τ : ℝ)/T) := by
      calc
        _ = B * (Real.exp (‖ζ‖^2*T) *
            Real.exp (sourceReducedBound D.ellipticity * ‖ζ‖^2*T)) *
            ((Real.sqrt T)⁻¹ * T^(-((d : ℝ)/4))) * Real.sqrt ((τ : ℝ)/T) := by ring
        _ = _ := by rw [heq, hTa]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT.le _)
      apply mul_le_mul hBC _ (Real.exp_pos _).le hC.le
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKC (sq_nonneg ‖ζ‖)) hT.le)

end EinsteinFull.Blueprint
