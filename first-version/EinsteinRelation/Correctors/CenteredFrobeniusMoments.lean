import EinsteinRelation.Correctors.CenteredScalarIntegrableMoments
import EinsteinRelation.Correctors.FrobeniusMomentAssembly
import EinsteinRelation.Correctors.CoordinateMomentProjections
open MeasureTheory
open scoped ENNReal
open Matrix
noncomputable section
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:743-745`. Entrywise spatial means control the
Frobenius oscillation, with a constant depending only on dimension and exponent. -/
theorem lintegral_frobenius_sub_entrywise_mean_rpow_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {d : ℕ} (hd : 0 < d) (A : X → Mat d) (c : Mat d) (p : ℝ) (hp : 2 ≤ p)
    (hA : Measurable A) (hi : ∀ j k, Integrable (fun x => A x j k) μ) :
    (∫⁻ x, ENNReal.ofReal (frobeniusNorm
      (A x - Matrix.of (fun j k => ∫ y, A y j k ∂μ)) ^ p) ∂μ) ≤
      ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) *
        (∫⁻ x, ENNReal.ofReal (frobeniusNorm (A x - c) ^ p) ∂μ) := by
  have hp1 : 1 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have hp0' : 0 ≤ p := by linarith
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  set m := Matrix.of (fun j k => ∫ y, A y j k ∂μ) with hm_def
  set M := fun x : X => A x - m with hM_def
  have hM_meas : Measurable M := by
    have h_cont : Continuous (fun (M' : Mat d) => M' - m) :=
      Continuous.sub continuous_id continuous_const
    exact h_cont.measurable.comp hA
  set I := (∫⁻ x, ENNReal.ofReal (frobeniusNorm (A x - c) ^ p) ∂μ) with hI_def
  have h_entry_bound (j k : Fin d) : (∫⁻ x, ENNReal.ofReal (|M x j k| ^ p) ∂μ) ≤
      ENNReal.ofReal (2 ^ p) * I := by
    calc
      (∫⁻ x, ENNReal.ofReal (|M x j k| ^ p) ∂μ) =
          (∫⁻ x, ENNReal.ofReal (|A x j k - ∫ y, A y j k ∂μ| ^ p) ∂μ) := by
        simp [M, m]
      _ ≤ ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (|A x j k - c j k| ^ p) ∂μ) :=
        lintegral_abs_sub_mean_rpow_le μ (fun x => A x j k) (c j k) p hp1 (hi j k)
      _ = ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (|(A x - c) j k| ^ p) ∂μ) := by
        simp [Matrix.sub_apply]
      _ ≤ ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (frobeniusNorm (A x - c) ^ p) ∂μ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine lintegral_mono (fun x => ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        have h := abs_entry_le_frobeniusNorm (A x - c) j k
        have h_nonneg : 0 ≤ |(A x - c) j k| := abs_nonneg _
        have h_frob_nonneg : 0 ≤ frobeniusNorm (A x - c) := by
          unfold frobeniusNorm
          exact Real.sqrt_nonneg _
        exact Real.rpow_le_rpow h_nonneg h hp0'
      _ = ENNReal.ofReal (2 ^ p) * I := by rw [hI_def]
  have h_rpow_eq : (d : ℝ) ^ (p - 2) * (d : ℝ) ^ 2 = (d : ℝ) ^ p := by
    calc
      (d : ℝ) ^ (p - 2) * (d : ℝ) ^ 2 = (d : ℝ) ^ (p - 2) * ((d : ℝ) ^ (2 : ℝ)) := by
        congr 1
        exact (Real.rpow_natCast (d : ℝ) 2).symm
      _ = (d : ℝ) ^ ((p - 2) + (2 : ℝ)) := by
        rw [← Real.rpow_add hd0 (p - 2) (2 : ℝ)]
      _ = (d : ℝ) ^ p := by rw [sub_add_cancel]
  have h_sum_const : (∑ j : Fin d, ∑ k : Fin d, (ENNReal.ofReal (2 ^ p) * I)) =
      (d : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (2 ^ p) * I) := by
    simp [pow_two, mul_assoc]
  have h_ofReal_nonneg : 0 ≤ ENNReal.ofReal ((d : ℝ) ^ (p - 2)) := by
    positivity
  have h_factor_eq : ENNReal.ofReal ((d : ℝ) ^ (p - 2)) * (d : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal ((d : ℝ) ^ p) := by
    calc
      ENNReal.ofReal ((d : ℝ) ^ (p - 2)) * (d : ℝ≥0∞) ^ 2 =
          ENNReal.ofReal ((d : ℝ) ^ (p - 2)) * ENNReal.ofReal ((d : ℝ) ^ 2) := by
        simp
      _ = ENNReal.ofReal ((d : ℝ) ^ (p - 2) * (d : ℝ) ^ 2) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd_nonneg _)]
      _ = ENNReal.ofReal ((d : ℝ) ^ p) := by rw [h_rpow_eq]
  calc
    (∫⁻ x, ENNReal.ofReal (frobeniusNorm (M x) ^ p) ∂μ) ≤
        ENNReal.ofReal ((d : ℝ) ^ (p - 2)) *
          ∑ j : Fin d, ∑ k : Fin d,
            ∫⁻ x, ENNReal.ofReal (|M x j k| ^ p) ∂μ :=
      lintegral_frobeniusNorm_rpow_le_sum μ hd M hM_meas p hp
    _ ≤ ENNReal.ofReal ((d : ℝ) ^ (p - 2)) *
          ∑ j : Fin d, ∑ k : Fin d,
            (ENNReal.ofReal (2 ^ p) * I) := by
      refine mul_le_mul_of_nonneg_left ?_ h_ofReal_nonneg
      have h_sums : (∑ j : Fin d, ∑ k : Fin d, ∫⁻ x, ENNReal.ofReal (|M x j k| ^ p) ∂μ) ≤
                    (∑ j : Fin d, ∑ k : Fin d, (ENNReal.ofReal (2 ^ p) * I)) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact h_entry_bound j k
      exact h_sums
    _ = ENNReal.ofReal ((d : ℝ) ^ (p - 2)) *
          ((d : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (2 ^ p) * I)) := by
      rw [h_sum_const]
    _ = (ENNReal.ofReal ((d : ℝ) ^ (p - 2)) * (d : ℝ≥0∞) ^ 2) *
          ENNReal.ofReal (2 ^ p) * I := by ring
    _ = ENNReal.ofReal ((d : ℝ) ^ p) *
          ENNReal.ofReal (2 ^ p) * I := by rw [h_factor_eq]
    _ = ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) * I := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd_nonneg _)]
    _ = ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) *
        (∫⁻ x, ENNReal.ofReal (frobeniusNorm (A x - c) ^ p) ∂μ) := by rw [hI_def]
end EinsteinRelation.Correctors
