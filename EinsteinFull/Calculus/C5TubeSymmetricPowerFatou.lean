import EinsteinFull.Calculus.C5TubeAllRealPowerStructure

open MeasureTheory Filter
open PDE.Parabolic.LocalMax


namespace EinsteinFull.Calculus

noncomputable section

/-- Fatou recovers the full absolute power from both signed truncations. -/
theorem c5_symmetric_truncated_power_fatou
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) :
    (∫⁻ x, ENNReal.ofReal (Real.rpow |u x| p) ∂μ) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ x, ENNReal.ofReal
      (powF p ε (n : ℝ) (u x) + powF p ε (n : ℝ) (-u x)) ∂μ) Filter.atTop := by
  have hm : ∀ n : ℕ, AEMeasurable (fun x => ENNReal.ofReal
      (powF p ε (n : ℝ) (u x) + powF p ε (n : ℝ) (-u x))) μ := by
    intro n
    have hc : Continuous (powF p ε (n : ℝ)) :=
      continuous_iff_continuousAt.mpr (fun x =>
        (powF_hasDerivAt hε (Nat.cast_nonneg n) x).continuousAt)
    exact ((hc.comp_aestronglyMeasurable hu).add
      (hc.comp_aestronglyMeasurable hu.neg)).aemeasurable.ennreal_ofReal
  refine (lintegral_mono fun x => ?_).trans (lintegral_liminf_le' hm)
  apply le_liminf_of_le (by isBoundedDefault)
  obtain ⟨N, hN⟩ := exists_nat_ge |u x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : |u x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hpow : Real.rpow |u x| p ≤ (|u x| + ε) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by linarith)
  apply ENNReal.ofReal_le_ofReal
  by_cases hx : 0 ≤ u x
  · have hpos := powF_eq_of_le (p := p) (N := (n : ℝ)) hε hx
      (Or.inr ((abs_of_nonneg hx).symm ▸ hn'))
    have hneg := (c5_all_real_truncated_power_structure hp hε n (-u x)).1
    rw [abs_of_nonneg hx] at hpow ⊢
    linarith
  · have hx' : 0 ≤ -u x := neg_nonneg.mpr (le_of_not_ge hx)
    have hpos := powF_eq_of_le (p := p) (N := (n : ℝ)) hε hx'
      (Or.inr ((abs_of_nonpos (le_of_not_ge hx)).symm ▸ hn'))
    have hneg := (c5_all_real_truncated_power_structure hp hε n (u x)).1
    rw [abs_of_nonpos (le_of_not_ge hx)] at hpow ⊢
    linarith

end
end EinsteinFull.Calculus

