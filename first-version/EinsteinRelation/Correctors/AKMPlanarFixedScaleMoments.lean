import EinsteinRelation.Correctors.AKMPlanarOscillationMoments

/-!
# Radius-four planar corrector moments

Source: `paper/main.tex:724-731`. The repaired proof uses (4.6) and
(6.15) at a fixed normalized radius of four. The latter is a bound on
the squared L² norm; its moment exponent is therefore halved.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The squared flux L² estimate (6.15) implies moments of its square root.
The logarithmic exponent is `p / 2`, since the source quantity is squared. -/
theorem akm_planar_flux_L2_moments (h615 : FluxPlanarL2Estimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ) (r : ℝ), 2 ≤ r →
        (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 r,
          frobeniusNorm (S.potential a x -
            fluxHeatAverage (S.potential a) 0 r) ^ 2 ∂volume)) ^ p) ∂P) ≤
          ENNReal.ofReal (C * (Real.sqrt (Real.log r)) ^ (p / 2)) := by
  obtain ⟨C, hC, hest⟩ := h615 K 1 hK zero_lt_one one_lt_two
  refine ⟨2 * C ^ (p / 2) * (p / 2) ^ (p / 2), by positivity, ?_⟩
  intro P hP e he φ S r hr
  have hn (a : Coefficient 2 K) : 0 ≤ ⨍ x in ball 0 r,
      frobeniusNorm (S.potential a x - fluxHeatAverage (S.potential a) 0 r) ^ 2
        ∂volume := integral_nonneg fun _ => sq_nonneg _
  have h := (hest P hP e he φ S r hr).moment_pos_le
    (show 0 < p / 2 by positivity)
  simp_rw [max_eq_left (hn _), Real.rpow_div_two_eq_sqrt _ (hn _)] at h
  rw [Real.mul_rpow hC.le (Real.sqrt_nonneg _)] at h
  convert h using 1
  congr 1
  ring

/-- All scalar L² moments at radius four have a constant independent of
law, direction and choice of corrector potential. -/
theorem akm_planar_scalar_radius_four_moments (h46 : ScalarPlanarL2Estimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e),
        (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 4,
          |φ.potential a x - scalarHeatAverage (φ.potential a) 0 4| ^ 2 ∂volume)) ^ p)
          ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hest⟩ := akm_planar_scalar_L2_moments h46 K p hK hp
  refine ⟨C * (Real.sqrt (Real.log 4)) ^ p, by positivity, ?_⟩
  intro P hP e he φ
  exact hest P hP e he φ 4 (by norm_num)

/-- The squared source flux estimate supplies all L² moments at radius
four, which is the only oscillation scale needed by the repaired proof. -/
theorem akm_planar_flux_radius_four_moments (h615 : FluxPlanarL2Estimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ),
        (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 4,
          frobeniusNorm (S.potential a x -
            fluxHeatAverage (S.potential a) 0 4) ^ 2 ∂volume)) ^ p) ∂P) ≤
          ENNReal.ofReal C := by
  obtain ⟨C, hC, hest⟩ := akm_planar_flux_L2_moments h615 K p hK hp
  refine ⟨C * (Real.sqrt (Real.log 4)) ^ (p / 2), by positivity, ?_⟩
  intro P hP e he φ S
  exact hest P hP e he φ S 4 (by norm_num)

end EinsteinRelation.Correctors
