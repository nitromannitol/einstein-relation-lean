import EinsteinRelation.Correctors.AKMAEStretchedExponentialMoments

/-!
# Finite moments of the planar AKM estimates

Source: `paper/main.tex:724-731`. The spatial L² quantity is raised to
an arbitrary real moment; it is not replaced by a spatial Lᵐ norm.
All constants precede the coefficient law, corrector, scale and centers.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Theorem 4.1, (4.6), gives all moments of the spatial L² oscillation. -/
theorem akm_planar_scalar_L2_moments (h46 : ScalarPlanarL2Estimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r : ℝ), 2 ≤ r →
        (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball 0 r,
          |φ.potential a x - scalarHeatAverage (φ.potential a) 0 r| ^ 2 ∂volume)) ^ p)
          ∂P) ≤ ENNReal.ofReal (C * (Real.sqrt (Real.log r)) ^ p) := by
  obtain ⟨C, hC, hest⟩ := h46 K 1 hK zero_lt_one one_lt_two
  refine ⟨2 * C ^ p * p ^ p, by positivity, ?_⟩
  intro P hP e he φ r hr
  have h := (hest P hP e he φ r hr).moment_pos_le hp
  simp only [max_eq_left (Real.sqrt_nonneg _),
    Real.mul_rpow hC.le (Real.sqrt_nonneg _)] at h
  convert h using 1
  congr 1
  ring

/-- Theorem 4.1, (4.7), gives all moments of heat-average differences.
The square root of the logarithm stays outside the spatial integral. -/
theorem akm_planar_scalar_heat_difference_moments (h47 : ScalarHeatDifferenceEstimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r R : ℝ), 2 ≤ r → r ≤ R → ∀ (x y : Vec 2),
        (∫⁻ a, ENNReal.ofReal (|scalarHeatAverage (φ.potential a) x r -
          scalarHeatAverage (φ.potential a) y R| ^ p) ∂P) ≤
          ENNReal.ofReal (C * (Real.sqrt
            (Real.log (2 + (R + euclideanNorm (x - y)) / r))) ^ p) := by
  obtain ⟨C, hC, hest⟩ := h47 K 1 hK zero_lt_one one_lt_two
  refine ⟨2 * C ^ p * p ^ p, by positivity, ?_⟩
  intro P hP e he φ r R hr hR x y
  have h := (hest P hP e he φ r R hr hR x y).moment_pos_le hp
  simp only [max_eq_left (abs_nonneg (_ : ℝ)),
    Real.mul_rpow hC.le (Real.sqrt_nonneg _)] at h
  convert h using 1
  congr 1
  ring

/-- Proposition 4.27 retains the sharper concentric logarithm `log (R/r)`
and its original separation of the two radii. -/
theorem akm_planar_scalar_concentric_heat_moments
    (h4147 : ScalarConcentricHeatDifferenceEstimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e < 1 → ∀ (φ : Corrector P e)
        (r R : ℝ), 2 ≤ r → 2 * r ≤ R →
        (∫⁻ a, ENNReal.ofReal (|scalarHeatAverage (φ.potential a) 0 r -
          scalarHeatAverage (φ.potential a) 0 R| ^ p) ∂P) ≤
          ENNReal.ofReal (C * (Real.sqrt (Real.log (R / r))) ^ p) := by
  obtain ⟨C, hC, hest⟩ := h4147 K 1 hK zero_lt_one one_lt_two
  refine ⟨2 * C ^ p * p ^ p, by positivity, ?_⟩
  intro P hP e he φ r R hr hR
  have h := (hest P hP e he φ r R hr hR).moment_pos_le hp
  simp only [max_eq_left (abs_nonneg (_ : ℝ)),
    Real.mul_rpow hC.le (Real.sqrt_nonneg _)] at h
  convert h using 1
  congr 1
  ring

/-- Proposition 6.2, (6.16), supplies all finite moments of the
Frobenius norm of the difference of two flux heat averages. -/
theorem akm_planar_flux_heat_difference_moments (h616 : FluxHeatDifferenceEstimate)
    (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient 2 K)), LawHypotheses P →
      ∀ (e : Vec 2), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ) (r R : ℝ), 1 ≤ r → r < R / Real.sqrt 2 →
        ∀ (x y : Vec 2),
        (∫⁻ a, ENNReal.ofReal (frobeniusNorm
          (fluxHeatAverage (S.potential a) x r -
            fluxHeatAverage (S.potential a) y R) ^ p) ∂P) ≤
          ENNReal.ofReal (C * (Real.sqrt
            (Real.log (2 + (R + euclideanNorm (x - y)) / r))) ^ p) := by
  obtain ⟨C, hC, hest⟩ := h616 K 1 hK zero_lt_one one_lt_two
  refine ⟨2 * C ^ p * p ^ p, by positivity, ?_⟩
  intro P hP e he φ S r R hr hR x y
  have h := (hest P hP e he φ S r R hr hR x y).moment_pos_le hp
  simp only [frobeniusNorm, max_eq_left (Real.sqrt_nonneg _),
    Real.mul_rpow hC.le (Real.sqrt_nonneg _)] at h ⊢
  convert h using 1
  congr 1
  ring

end EinsteinRelation.Correctors

