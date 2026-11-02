import EinsteinFull.External.AKMNegativeSobolev
import EinsteinFull.Calculus.AKMNegativeSobolevDuality
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization

/-! The source compact-test second-moment estimate on the actual normalized
coefficient law. Stationarity, finite range and ellipticity premises are
proved internally. Identifying these source correctors with the frozen
horizontal correctors and extending to Schwartz tests remain separate steps. -/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.AKM
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open External.Source.AKM

/-- AKM (4.126) gives the CLT-scale compact-test second moment on the actual
rescaled reduced coefficient law, uniformly in that law and its dependence
range. Both gradient and centered flux are retained. This is still in source
spatial coordinates and does not assert a horizontal corrector identity. -/
theorem compact_test_second_moment_actual_coefficient_law
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (ψ χ : Fin d → Vec d → ℝ),
        (∀ j, IsSpatialTest (originBall d 1) (ψ j)) →
        (∀ j, integerSobolevTestNorm m (originBall d 1) (ψ j) ≤ 1) →
        (∀ j, IsSpatialTest (originBall d 1) (χ j)) →
        (∀ j, integerSobolevTestNorm m (originBall d 1) (χ j) ≤ 1) →
        (∫⁻ a, ENNReal.ofReal
          (((∑ j : Fin d, |⨍ x in originBall d 1,
              (S.corrector e).grad a (ε⁻¹ • x) j * ψ j x ∂volume|) +
            (∑ j : Fin d, |⨍ x in originBall d 1,
              ((a (ε⁻¹ • x)).mulVec (e + (S.corrector e).grad a (ε⁻¹ • x)) -
                S.homogenized.mulVec e) j * χ j x ∂volume|)) ^ 2)
            ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal (C * ε ^ (d : ℝ)) := by
  obtain ⟨C, hC, hsource⟩ := External.akm_negative_sobolev d hd
    (AKMUpperEllipticity L) (Correctors.one_lt_AKMUpperEllipticity hL)
    m hm 1 zero_lt_one one_lt_two
  refine ⟨8 * C ^ 2, mul_pos (by norm_num) (sq_pos_of_pos hC), ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := hsource (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q)
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ ψ χ hψ hnψ hχ hnχ
  obtain ⟨Z, _, hZ, hdual⟩ := hS e he ε hε hε₂
  have hbound := two_field_pairing_second_moment_le
    (fun a x => (S.corrector e).grad a (ε⁻¹ • x))
    (fun a x => (a (ε⁻¹ • x)).mulVec
      (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e)
    hZ hdual ψ χ hψ hnψ hχ hnχ
  have hpower : (ε ^ ((d : ℝ) / 2)) ^ 2 = ε ^ (d : ℝ) := by
    rw [← Real.rpow_mul_natCast hε.le]
    simp only [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simpa only [mul_pow, hpower, mul_assoc] using hbound

end EinsteinFull.AKM
