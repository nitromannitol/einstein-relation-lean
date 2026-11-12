import EinsteinRelation.Correctors.AKMCoefficientColumnFlow
import EinsteinRelation.Correctors.PairedPDECutoffGradientMoments
import EinsteinRelation.Correctors.PairedPDEAmplitude

/-! # Cutoff gradient moments for the source-selected coefficient flow

Source: `paper/main.tex:798–806,844–855`; AKM, Theorem 9.1, p. 349.
The scalar decay bound and the proved weak energy inequality apply to the
same selected flow. No gradient-decay estimate is added as an input.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- Positive-time finite cylinders have positive finite Euclidean volume.
Source: `paper/main.tex:798–806,844–855`. -/
theorem positiveTimeCylinder_volume_pos_finite {d : ℕ} {a b R : ℝ}
    (hab : a < b) (hR : 0 < R) :
    volume (Set.Ioo a b ×ˢ originBall d R) ≠ 0 ∧
      volume (Set.Ioo a b ×ˢ originBall d R) ≠ ∞ := by
  have hball := paired_ball_volume_pos_finite (d := d) hR
  have heq : originBall d R = ball (0 : Vec d) R := by
    ext x
    simp only [originBall, ball, sub_zero]
  rw [heq, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
  have ht0 : ENNReal.ofReal (b-a) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hb := ENNReal.toReal_pos_iff.mp hball
  exact ⟨mul_ne_zero ht0 hb.1.ne',
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb.2).ne⟩

/-- One source-selected coefficient-column flow has all finite cutoff
energy moments, with the scalar source rate and explicit cutoff/volume
factor. The witness is chosen before the moment and cutoff.
Source: `paper/main.tex:798–806,844–855`. -/
theorem parabolicSemigroupDecay_actual_column_cutoff_gradient_moments
    (hAKM : ParabolicSemigroupDecay) (d : ℕ) (hd : 2 ≤ d)
    (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < C m) ∧
      ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P → ∀ i : Fin d,
        ∃ (u : Coefficient d K → ℝ × Vec d → ℝ)
          (G : Coefficient d K → ℝ × Vec d → Vec d),
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) ∧
          Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) ∧
          (∀ᵐ A ∂P, IsSemigroupSolution A
            (fun x => (A x).mulVec (unitVector i)) (u A) (G A)) ∧
          ∀ m : ℝ, 2 ≤ m → ∀ a b R : ℝ, 1 ≤ a → a < b → 0 < R →
            ∀ ζ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
              tsupport ζ ⊆ Set.Ioo a b ×ˢ originBall d R →
              ∀ B : ℝ, 0 ≤ B →
                (∀ z ∈ Set.Ioo a b ×ˢ originBall d R,
                  2 * ζ z * fderiv ℝ ζ z (1, 0) +
                    4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ B) →
                MemLp (fun A => Real.sqrt (∫ z in Set.Ioo a b ×ˢ originBall d R,
                  ζ z^2 * euclideanSq (G A z))) (ENNReal.ofReal m) P ∧
                eLpNorm (fun A => Real.sqrt (∫ z in Set.Ioo a b ×ˢ originBall d R,
                  ζ z^2 * euclideanSq (G A z))) (ENNReal.ofReal m) P ≤
                    ENNReal.ofReal (Real.sqrt (B * volume.real
                      (Set.Ioo a b ×ˢ originBall d R)) *
                        (C m * a^(-(1 : ℝ)/2 - (d : ℝ)/4))) := by
  obtain ⟨C, hC, hflow⟩ := parabolicSemigroupDecay_actual_column hAKM d hd K s hK hs hs2
  refine ⟨C, hC, ?_⟩
  intro P hP i
  letI : IsProbabilityMeasure P := hP.1
  obtain ⟨u, G, hum, hGm, hsol, hval⟩ := hflow P hP i
  refine ⟨u, G, hum, hGm, hsol, ?_⟩
  intro m hm a b R ha hab hR ζ hζ hζc hζsupp B hB0 hB
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hm0 : 0 < m := zero_lt_two.trans_le hm
  have heq : originBall d R = ball (0 : Vec d) R := by
    ext x
    simp only [originBall, ball, sub_zero]
  have hU : IsOpen (originBall d R) := by
    simpa only [heq] using paired_isOpen_ball (0 : Vec d) R
  have hvol := positiveTimeCylinder_volume_pos_finite hab hR (d := d)
  apply parabolicSolution_cutoff_gradient_moments (zero_lt_one.trans hK) P
    id u G hum hGm measurableSet_Ioo hU hvol.1 hvol.2
    (hsol.mono fun A hA => hA.2.1 a b R ha0 hab hR) hζ hζc
    (by simpa only [interior_Ioo] using hζsupp) hB0 hB hm
    (mul_nonneg (hC m hm0).le (Real.rpow_nonneg ha0.le _))
  intro z hz
  have hzv := hval m hm0 z.1 (ha.trans hz.1.1.le) z.2
  refine ⟨hzv.1, hzv.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos ha0 hz.1.1.le (by
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith only [hd0])) (hC m hm0).le

end EinsteinRelation.Correctors
