import EinsteinRelation.Correctors.AKMPlanarFourEightGeometry
import EinsteinRelation.TimeChange.EuclideanTransport

/-!
# Planar heat comparisons at the repaired fixed scales

Source: `paper/main.tex:724-731`. The normalized radii are four and
`8R`, for every `R ≥ 1`. Centers may differ by as much as `2R + 4` in
physical coordinates, and the physical range is any `r ≥ 1`.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem four_eight_log_rpow_le {d : ℕ}
    (r R p : ℝ) (hr : 1 ≤ r) (hR : 1 ≤ R) (hp : 0 ≤ p)
    (z y : Vec d) (hzy : euclideanNorm (z - y) ≤ 2 * R + 4) :
    (Real.sqrt (Real.log (2 + (8 * R +
      euclideanNorm (r⁻¹ • z - r⁻¹ • y)) / 4))) ^ p ≤
        2 ^ p * (Real.sqrt (Real.log (2 + R))) ^ p := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdist : euclideanNorm (r⁻¹ • z - r⁻¹ • y) = euclideanNorm (z - y) / r := by
    rw [← smul_sub, TimeChange.euclideanNorm_smul,
      abs_of_pos (inv_pos.mpr hr0), inv_mul_eq_div]
  rw [hdist]
  have h := (four_eight_scale_geometry r R (euclideanNorm (z - y)) hr hR
    (by unfold euclideanNorm; positivity) hzy).2
  have hpw := Real.rpow_le_rpow (Real.sqrt_nonneg _) h hp
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)] at hpw

/-- AKM (4.7) at radii four and `8R`, including the physical center
separation and range rescaling required in the unit-ball L² estimate. -/
theorem akm_planar_scalar_four_eight_heat_moments (h47 : ScalarHeatDifferenceEstimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r R : ℝ), 1 ≤ r → 1 ≤ R → ∀ (z y : Vec 2),
        euclideanNorm (z - y) ≤ 2 * R + 4 →
        (∫⁻ a, ENNReal.ofReal (|scalarHeatAverage (φ.potential a) (r⁻¹ • z) 4 -
          scalarHeatAverage (φ.potential a) (r⁻¹ • y) (8 * R)| ^ p) ∂P) ≤
            ENNReal.ofReal (C * (Real.sqrt (Real.log (2 + R))) ^ p) := by
  obtain ⟨C, hC, hest⟩ := akm_planar_scalar_heat_difference_moments h47 K p hK hp
  refine ⟨C * 2 ^ p, by positivity, ?_⟩
  intro P hP e he φ r R hr hR z y hzy
  apply (hest P hP e he φ 4 (8 * R) (by norm_num) (by linarith)
    (r⁻¹ • z) (r⁻¹ • y)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (2 ^ p * (Real.sqrt (Real.log (2 + R))) ^ p) :=
      mul_le_mul_of_nonneg_left
        (four_eight_log_rpow_le r R p hr hR hp.le z y hzy) hC.le
    _ = _ := by ring

/-- AKM (6.16) at the same two centers and scales. The strict flux
separation holds even at `R = 1`; no bounded-radius comparison is needed. -/
theorem akm_planar_flux_four_eight_heat_moments (h616 : FluxHeatDifferenceEstimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ) (r R : ℝ), 1 ≤ r → 1 ≤ R → ∀ (z y : Vec 2),
        euclideanNorm (z - y) ≤ 2 * R + 4 →
        (∫⁻ a, ENNReal.ofReal (frobeniusNorm
          (fluxHeatAverage (S.potential a) (r⁻¹ • z) 4 -
            fluxHeatAverage (S.potential a) (r⁻¹ • y) (8 * R)) ^ p) ∂P) ≤
            ENNReal.ofReal (C * (Real.sqrt (Real.log (2 + R))) ^ p) := by
  obtain ⟨C, hC, hest⟩ := akm_planar_flux_heat_difference_moments h616 K p hK hp
  refine ⟨C * 2 ^ p, by positivity, ?_⟩
  intro P hP e he φ S r R hr hR z y hzy
  have hsep := (four_eight_scale_geometry r R (euclideanNorm (z - y)) hr hR
    (by unfold euclideanNorm; positivity) hzy).1
  apply (hest P hP e he φ S 4 (8 * R) (by norm_num) hsep
    (r⁻¹ • z) (r⁻¹ • y)).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C * (2 ^ p * (Real.sqrt (Real.log (2 + R))) ^ p) :=
      mul_le_mul_of_nonneg_left
        (four_eight_log_rpow_le r R p hr hR hp.le z y hzy) hC.le
    _ = _ := by ring

end EinsteinRelation.Correctors
