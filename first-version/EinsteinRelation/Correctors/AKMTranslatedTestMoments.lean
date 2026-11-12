import EinsteinRelation.Correctors.AKMBoundedTestMoments
import EinsteinRelation.Correctors.UniformTranslatedH2Tests
import EinsteinRelation.Correctors.PairedPDEAmplitude

/-! # AKM moments for the actual translated smooth tests

Source: `paper/main.tex:948–955`. The deterministic translated-test bound
and homogeneity of the AKM estimate give one joint gradient/flux moment
constant for all translations of a fixed compact smooth kernel. No
translated-test estimate is assumed as an extra input.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The source corrector and its centered flux satisfy a common quantitative
test bound, uniformly over all admissible half-ball translations of the
fixed kernel. Source: `paper/main.tex:948–955`; AKM (4.126), p. 173. -/
theorem correctorWeakH2_translated_test_moments (hAKM : CorrectorWeakH2)
    (K s m : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) (hm : 0 < m)
    {ζ : Vec 2 → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hsupp : tsupport ζ ⊆ originBall 2 (1/2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient 2 K), IsAdmissibleLaw P →
      ∀ e : Vec 2, euclideanNorm e ≤ 1 →
        ∀ (φ : Coefficient 2 K → Vec 2 → ℝ) (G : Coefficient 2 K → Vec 2 → Vec 2),
          IsFirstOrderCorrector P e φ G →
          ∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ a : Vec 2, euclideanNorm a ≤ 1/2 →
            ∀ j : Fin 2,
              eLpNorm (fun A => ⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * ζ (x-a))
                  (ENNReal.ofReal m) P +
                eLpNorm (fun A => ⨍ x in originBall 2 1,
                  (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ζ (x-a))
                  (ENNReal.ofReal m) P ≤ ENNReal.ofReal (C * ε) := by
  have hvolume : volume (originBall 2 1) ≠ ⊤ := by
    have hpos := paired_ball_volume_pos_finite (d := 2) (R := 1) zero_lt_one
    have hpos' : 0 < (volume (originBall 2 1)).toReal := by
      simpa only [measureReal_def, ball, originBall, sub_zero] using hpos
    exact (ENNReal.toReal_pos_iff.mp hpos').2.ne
  obtain ⟨M, hM, hnorm⟩ := exists_uniform_h2TestNorm_comp_sub_bound hζ hc _ hvolume
  obtain ⟨C, hC, htest⟩ :=
    correctorWeakH2_test_moments_unit_bounded hAKM K s m hK hs hs2 hm
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro P hP e he φ G hcorrector ε hε hεhalf a ha j
  exact htest P hP e he φ G hcorrector ε hε hεhalf M hM (fun x => ζ (x-a))
    (isSpatialTest_comp_sub_of_half_ball hζ hc hsupp ha) (hnorm a) j

end EinsteinRelation.Correctors
