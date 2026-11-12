import EinsteinRelation.Correctors.AKMHeatKernelCutoffs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Expanding spatial cutoffs remove an integrable vector flux from
the forward/backward pairing. Source: `paper/main.tex:787–792,850`. -/
theorem akm_cutoff_flux_tendsto_zero {d : ℕ} {a b : ℝ}
    {F : ℝ × Vec d → Vec d}
    (hF : ∀ j : Fin d, Integrable (fun z => F z j)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    {η : ℝ → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    {χ : ℕ → Vec d → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (_hχ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n))
    (hχb : ∀ n x, |χ n x| ≤ 1)
    (hχD : ∀ n x, ‖gradient (χ n) x‖ ≤ B / (n+1 : ℕ)) :
    Tendsto (fun n => ∫ z in Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)),
      η z.1 * χ n z.2 * dot (F z) (gradient (χ n) z.2)) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Vec d) := volume.restrict (Set.Ioo a b ×ˢ Set.univ)
  let S : ℝ × Vec d → ℝ := fun z => ∑ j, |F z j|
  have hS : Integrable S μ := integrable_finset_sum _ (fun j _ => (hF j).abs)
  have hS0 (z) : 0 ≤ S z := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  obtain ⟨M, hM⟩ := hηc.exists_bound_of_continuous hη
  have hM0 : 0 ≤ M := (norm_nonneg (η 0)).trans (hM 0)
  have hbnd (n : ℕ) (z : ℝ × Vec d) :
      ‖η z.1 * χ n z.2 * dot (F z) (gradient (χ n) z.2)‖ ≤
        (M * (B / (n+1 : ℕ))) * S z := by
    have hd : |dot (F z) (gradient (χ n) z.2)| ≤ S z * (B / (n+1 : ℕ)) := by
      calc
        _ ≤ ∑ j, |F z j * gradient (χ n) z.2 j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |F z j| * (B / (n+1 : ℕ)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          have hc : |gradient (χ n) z.2 j| ≤ ‖gradient (χ n) z.2‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (gradient (χ n) z.2) j
          exact mul_le_mul_of_nonneg_left (hc.trans (hχD n z.2)) (abs_nonneg _)
        _ = _ := (Finset.sum_mul _ _ _).symm
    have hηχ : |η z.1 * χ n z.2| ≤ M := by
      rw [abs_mul]
      calc
        _ ≤ M * 1 := mul_le_mul (by simpa only [Real.norm_eq_abs] using hM z.1)
          (hχb n z.2) (abs_nonneg _) hM0
        _ = M := mul_one _
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ M * (S z * (B / (n+1 : ℕ))) :=
        mul_le_mul hηχ hd (abs_nonneg _) hM0
      _ = _ := by ring
  have hint (n : ℕ) : ‖∫ z, η z.1 * χ n z.2 * dot (F z) (gradient (χ n) z.2) ∂μ‖ ≤
      (M * (B / (n+1 : ℕ))) * ∫ z, S z ∂μ := by
    calc
      _ ≤ ∫ z, (M * (B / (n+1 : ℕ))) * S z ∂μ :=
        norm_integral_le_of_norm_le (hS.const_mul _) (Eventually.of_forall (hbnd n))
      _ = _ := integral_const_mul _ _
  have ht : Tendsto (fun n : ℕ => (M * (B / (n+1 : ℕ))) * ∫ z, S z ∂μ) atTop (𝓝 0) := by
    have hd : Tendsto (fun n : ℕ => B / (n+1 : ℕ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
    simpa using (hd.const_mul M).mul_const (∫ z, S z ∂μ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => norm_nonneg _) hint

end EinsteinRelation.Correctors
