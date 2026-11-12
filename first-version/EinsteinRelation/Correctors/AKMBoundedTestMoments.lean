import EinsteinRelation.Correctors.AKMCorrectorScaling

/-! # AKM smooth-test bounds with a fixed norm bound

Source: `paper/main.tex:948–955`. Shifted mollifiers have a common finite
rescaled `H²` bound, rather than unit norm. Homogeneity converts that bound
to the normalized tests in the existing AKM input without changing the
corrector or its flux.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem coordinateDerivative_const_smul {d : ℕ} (c : ℝ)
    (ψ : Vec d → ℝ) (j : Fin d) :
    coordinateDerivative j (c • ψ) = c • coordinateDerivative j ψ := by
  funext x
  simp only [coordinateDerivative, fderiv_const_smul_of_field,
    Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Nonnegative scaling of the literal normalized `H²` test norm.
Source: `paper/main.tex:948–955`. -/
theorem h2TestNorm_const_smul {d : ℕ} (U : Set (Vec d)) (ψ : Vec d → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : h2TestNorm U (c • ψ) = c * h2TestNorm U ψ := by
  have hrms (f : Vec d → ℝ) : scalarRms volume U (c • f) = c * scalarRms volume U f :=
    scalarRms_const_mul volume U f hc
  simp only [h2TestNorm, coordinateDerivative_const_smul, hrms]
  simp only [← Finset.mul_sum]
  ring

/-- The same AKM joint gradient/flux estimate holds for any smooth test
with a common positive `H²` bound. The moment constant is chosen before
the law, corrector, bound and test. Source: `paper/main.tex:948–955`. -/
theorem correctorWeakH2_test_moments_unit_bounded (hAKM : CorrectorWeakH2)
    (K s m : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient 2 K), IsAdmissibleLaw P →
      ∀ e : Vec 2, euclideanNorm e ≤ 1 →
        ∀ (φ : Coefficient 2 K → Vec 2 → ℝ) (G : Coefficient 2 K → Vec 2 → Vec 2),
          IsFirstOrderCorrector P e φ G →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ M : ℝ, 0 < M →
            ∀ ψ : Vec 2 → ℝ, IsSpatialTest (originBall 2 1) ψ →
              h2TestNorm (originBall 2 1) ψ ≤ M → ∀ j : Fin 2,
                eLpNorm (fun A => ⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * ψ x)
                    (ENNReal.ofReal m) P +
                  eLpNorm (fun A => ⨍ x in originBall 2 1,
                    (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ψ x)
                    (ENNReal.ofReal m) P ≤ ENNReal.ofReal (C * M * ε) := by
  obtain ⟨C, hC, ht⟩ := correctorWeakH2_test_moments_unit hAKM K s m hK hs hs2 hm
  refine ⟨C, hC, ?_⟩
  intro P hP e he φ G hcorrector ε hε hεhalf M hM ψ hψ hnorm j
  have htest : IsSpatialTest (originBall 2 1) (M⁻¹ • ψ) :=
    ⟨contDiff_const.smul hψ.1, hψ.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => M⁻¹) ψ).trans hψ.2.2⟩
  have hnormalized : h2TestNorm (originBall 2 1) (M⁻¹ • ψ) ≤ 1 := by
    rw [h2TestNorm_const_smul _ _ (inv_nonneg.mpr hM.le)]
    simpa only [inv_mul_cancel₀ hM.ne'] using
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hM.le)
  have hsmall := ht P hP e he φ G hcorrector ε hε hεhalf (M⁻¹ • ψ) htest hnormalized j
  let f : Coefficient 2 K → ℝ := fun A =>
    ⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * (M⁻¹ • ψ) x
  let q : Coefficient 2 K → ℝ := fun A => ⨍ x in originBall 2 1,
    (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * (M⁻¹ • ψ) x
  have hrestore : ψ = M • (M⁻¹ • ψ) := by simp only [smul_smul, mul_inv_cancel₀ hM.ne', one_smul]
  have heq (V : Coefficient 2 K → Vec 2 → ℝ) :
      (fun A => ⨍ x in originBall 2 1, V A x * ψ x) =
        M • (fun A => ⨍ x in originBall 2 1, V A x * (M⁻¹ • ψ) x) := by
    conv_lhs => rw [hrestore]
    ext A
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (V A _), average,
      integral_const_mul]
  rw [heq (fun A x => G A (ε⁻¹ • x) j), heq (fun A x =>
    ((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j)]
  change eLpNorm (M • f) _ P + eLpNorm (M • q) _ P ≤ _
  rw [eLpNorm_const_smul, eLpNorm_const_smul, ← mul_add]
  have hnormM : ‖M‖ₑ = ENNReal.ofReal M := by
    simp [Real.enorm_eq_ofReal hM.le]
  rw [hnormM]
  calc
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C * ε) := mul_le_mul_right hsmall _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hM.le]
      congr 1
      ring

end EinsteinRelation.Correctors
