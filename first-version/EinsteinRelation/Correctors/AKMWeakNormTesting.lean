import EinsteinRelation.Correctors.AKMStretchedExponentialMoments

/-! # Smooth-test consequences of AKM's weak corrector estimate

Source: `paper/main.tex:948–955`. This module extracts scalar smooth-test
pairings of both the corrector gradient and centered flux from (4.126),
including their finite-moment bounds with a common uniform constant.
The spatial coordinates and the corrector are still those of AKM; no
identification with the project's canonical corrector is presumed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- A normalized smooth scalar test is controlled by the actual extended
negative Sobolev norm, without converting an infinite norm to a real number.
Source: `paper/main.tex:948–955`, AKM (0.29) and (4.126). -/
theorem ofReal_abs_average_mul_le_negativeH2Norm {d : ℕ}
    (U : Set (Vec d)) (f ψ : Vec d → ℝ)
    (hψ : IsSpatialTest U ψ) (hnorm : h2TestNorm U ψ ≤ 1) :
    ENNReal.ofReal |⨍ x in U, f x * ψ x| ≤ negativeH2Norm U f := by
  exact le_iSup_of_le ⟨ψ, hψ, hnorm⟩ le_rfl

/-- Each tested coordinate is controlled by the component-sum vector
negative norm. Source: `paper/main.tex:948–955`. -/
theorem ofReal_abs_average_coordinate_mul_le_vectorNegativeH2Norm {d : ℕ}
    (U : Set (Vec d)) (F : Vec d → Vec d) (j : Fin d) (ψ : Vec d → ℝ)
    (hψ : IsSpatialTest U ψ) (hnorm : h2TestNorm U ψ ≤ 1) :
    ENNReal.ofReal |⨍ x in U, F x j * ψ x| ≤ vectorNegativeH2Norm U F := by
  exact (ofReal_abs_average_mul_le_negativeH2Norm U (fun x => F x j) ψ hψ hnorm).trans
    (Finset.single_le_sum (fun k _ => zero_le (negativeH2Norm U (fun x => F x k)))
      (Finset.mem_univ j))

/-- Finite-moment smooth-test bounds for both terms of AKM (4.126),
p. 173, at `d = α = 2`. The constant is chosen before the law, corrector,
scale, normalized test, and coordinate. The two fields retain their common
source random upper bound. These are seminorm inequalities; choosing
measurable spatial representatives remains part of identifying the canonical
objects. Source: `paper/main.tex:948–955`. -/
theorem correctorWeakH2_test_moments (hAKM : CorrectorWeakH2)
    (K s m : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient 2 K), IsAdmissibleLaw P →
      ∀ e : Vec 2, euclideanNorm e < 1 →
        ∀ (φ : Coefficient 2 K → Vec 2 → ℝ) (G : Coefficient 2 K → Vec 2 → Vec 2),
          IsFirstOrderCorrector P e φ G →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
            ∀ ψ : Vec 2 → ℝ, IsSpatialTest (originBall 2 1) ψ →
              h2TestNorm (originBall 2 1) ψ ≤ 1 → ∀ j : Fin 2,
                eLpNorm (fun A => ⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * ψ x)
                    (ENNReal.ofReal m) P +
                  eLpNorm (fun A => ⨍ x in originBall 2 1,
                    (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ψ x)
                    (ENNReal.ofReal m) P ≤ ENNReal.ofReal (C * ε) := by
  obtain ⟨C, hC, hweak⟩ := hAKM K s hK hs hs2
  let M : ℝ := (2 * (m / s) ^ (m / s)) ^ (1 / m)
  refine ⟨2 * M * C, by dsimp [M]; positivity, ?_⟩
  intro P hP e he φ G hcorrector ε hε hεhalf ψ hψ hψnorm j
  obtain ⟨Z, _, hZ, hnorm⟩ := hweak P hP e he φ G hcorrector ε hε hεhalf
  have hgrad : ∀ᵐ A ∂P,
      |⨍ x in originBall 2 1, G A (ε⁻¹ • x) j * ψ x| ≤ max (Z A) 0 := by
    filter_upwards [hnorm] with A hA
    apply (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp
    calc
      _ ≤ vectorNegativeH2Norm (originBall 2 1) (fun x => G A (ε⁻¹ • x)) :=
        ofReal_abs_average_coordinate_mul_le_vectorNegativeH2Norm
          (originBall 2 1) _ j ψ hψ hψnorm
      _ ≤ vectorNegativeH2Norm (originBall 2 1) (fun x => G A (ε⁻¹ • x)) +
          vectorNegativeH2Norm (originBall 2 1) (fun x =>
            (A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) :=
        le_add_of_nonneg_right (zero_le _)
      _ ≤ ENNReal.ofReal (Z A) := hA
      _ ≤ ENNReal.ofReal (max (Z A) 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hflux : ∀ᵐ A ∂P,
      |⨍ x in originBall 2 1,
        (((A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) j) * ψ x| ≤
          max (Z A) 0 := by
    filter_upwards [hnorm] with A hA
    apply (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp
    calc
      _ ≤ vectorNegativeH2Norm (originBall 2 1) (fun x =>
          (A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) :=
        ofReal_abs_average_coordinate_mul_le_vectorNegativeH2Norm
          (originBall 2 1) _ j ψ hψ hψnorm
      _ ≤ vectorNegativeH2Norm (originBall 2 1) (fun x => G A (ε⁻¹ • x)) +
          vectorNegativeH2Norm (originBall 2 1) (fun x =>
            (A (ε⁻¹ • x)).mulVec (e + G A (ε⁻¹ • x)) - firstOrderMeanFlux P e G) :=
        le_add_of_nonneg_left (zero_le _)
      _ ≤ ENNReal.ofReal (Z A) := hA
      _ ≤ ENNReal.ofReal (max (Z A) 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hθ : 0 < C * ε := mul_pos hC hε
  have hgradLp := eLpNorm_le_of_stretchedExponential_domination P hs hθ hm hgrad hZ
  have hfluxLp := eLpNorm_le_of_stretchedExponential_domination P hs hθ hm hflux hZ
  calc
    _ ≤ ENNReal.ofReal (M * (C * ε)) + ENNReal.ofReal (M * (C * ε)) :=
      add_le_add hgradLp hfluxLp
    _ = ENNReal.ofReal ((2 * M * C) * ε) := by
      rw [← ENNReal.ofReal_add (by dsimp [M]; positivity) (by dsimp [M]; positivity)]
      congr 1
      ring

end EinsteinRelation.Correctors
