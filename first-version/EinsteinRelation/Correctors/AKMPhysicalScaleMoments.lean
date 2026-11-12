import EinsteinRelation.Correctors.AKMTranslatedTestMoments
import EinsteinRelation.Correctors.AKMPhysicalMollifierPairing

/-! # AKM mollifier estimates down to the physical unit radius

Source: `paper/main.tex:948–955`. The translated smooth-test estimate is
applied to the actual fixed mollifier and then transported to scale `R`.
The source corrector remains explicit; its gradient and centered flux share
one constant, chosen before the law, corrector, radius and translation.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Both terms of AKM (4.126) bound their actual mollifier convolutions
by `C/R`, uniformly on the physical ball of radius `R`.
Source: `paper/main.tex:948–955`, AKM (4.126), printed p. 173. -/
theorem correctorWeakH2_physical_scale_gradient_flux_moments (hAKM : CorrectorWeakH2)
    (K s m r : ℝ) (hr : 1 ≤ r) (hK : 1 < K) (hs : 0 < s) (hs2 : s < 2) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient 2 K), IsAdmissibleLaw P →
      ∀ e : Vec 2, euclideanNorm e ≤ 1 →
        ∀ (φ : Coefficient 2 K → Vec 2 → ℝ) (G : Coefficient 2 K → Vec 2 → Vec 2),
          IsFirstOrderCorrector P e φ G → ∀ R : ℝ, 1 ≤ R →
            ∀ y : Vec 2, euclideanNorm y ≤ R → ∀ j : Fin 2,
              eLpNorm (fun A => ((fun x => G A x j)
                  ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
                    Calculus.unitMassScaledMollifier 2 (R / r)) (r⁻¹ • y)) (ENNReal.ofReal m) P +
                eLpNorm (fun A => ((fun x =>
                    ((A x).mulVec (e + G A x) - firstOrderMeanFlux P e G) j)
                  ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
                    Calculus.unitMassScaledMollifier 2 (R / r)) (r⁻¹ • y)) (ENNReal.ofReal m) P ≤
                  ENNReal.ofReal (C * R⁻¹) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  let ζ : Vec 2 → ℝ := fun x => mollifier 2 ((-(4 * r)) • x)
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    (contDiff_mollifier 2).comp (contDiff_const.smul contDiff_id)
  have hζc : HasCompactSupport ζ :=
    (hasCompactSupport_mollifier 2).comp_homeomorph
      (Homeomorph.smul (Units.mk0 (-(4 * r)) (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hr0.ne'))))
  have hζs : tsupport ζ ⊆ originBall 2 (1/2) :=
    tsupport_physical_compressed_mollifier hr
  obtain ⟨C, hC, htest⟩ :=
    correctorWeakH2_translated_test_moments hAKM K s m hK hs hs2 hm hζ hζc hζs
  let V : ℝ := (volume (originBall 2 1)).toReal
  have hV : 0 < V := by
    simpa only [V, measureReal_def, ball, originBall, sub_zero] using
      paired_ball_volume_pos_finite (d := 2) (R := 1) zero_lt_one
  refine ⟨4 * r ^ 2 * V * C, by positivity, ?_⟩
  intro P hP e he φ G hcorrector R hR y hy j
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hε : 0 < (4 * R)⁻¹ := by positivity
  have hεhalf : (4 * R)⁻¹ < 1/2 := by
    apply (inv_lt_comm₀ (by positivity) (by norm_num)).mpr
    norm_num
    linarith
  have ha : euclideanNorm ((4 * r * R)⁻¹ • y) ≤ 1/2 := by
    rw [euclideanNorm_smul _ (by positivity : 0 ≤ (4 * r * R)⁻¹)]
    apply (inv_mul_le_iff₀ (by positivity : 0 < 4 * r * R)).mpr
    nlinarith
  have ht := htest P hP e he φ G hcorrector (4 * R)⁻¹ hε hεhalf
    ((4 * r * R)⁻¹ • y) ha j
  have harg (x : Vec 2) : ζ (x - (4 * r * R)⁻¹ • y) =
      mollifier 2 (R⁻¹ • y - (4 * r) • x) := by
    dsimp only [ζ]
    congr 1
    have hcoeff : (-(4 * r)) * (4 * r * R)⁻¹ = -R⁻¹ := by field_simp
    rw [smul_sub, smul_smul, hcoeff]
    module
  simp only [inv_inv, harg] at ht
  have heq (F : Vec 2 → ℝ) :
      (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier 2 (R / r)) (r⁻¹ • y) =
        (16 * r ^ 2 * V) * (⨍ x in originBall 2 1,
          F ((4 * R) • x) * mollifier 2 (R⁻¹ • y - (4 * r) • x)) := by
    exact convolution_source_eq_physical_unit_average F hr hR0 y hy
  let f : Coefficient 2 K → ℝ := fun A => ⨍ x in originBall 2 1,
    G A ((4 * R) • x) j * mollifier 2 (R⁻¹ • y - (4 * r) • x)
  let q : Coefficient 2 K → ℝ := fun A => ⨍ x in originBall 2 1,
    ((A ((4 * R) • x)).mulVec (e + G A ((4 * R) • x)) -
      firstOrderMeanFlux P e G) j * mollifier 2 (R⁻¹ • y - (4 * r) • x)
  have hf : (fun A => ((fun x => G A x j)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Calculus.unitMassScaledMollifier 2 (R / r)) (r⁻¹ • y)) =
      (16 * r ^ 2 * V) • f := funext fun A => heq (fun x => G A x j)
  have hq : (fun A => ((fun x => ((A x).mulVec (e + G A x) - firstOrderMeanFlux P e G) j)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Calculus.unitMassScaledMollifier 2 (R / r)) (r⁻¹ • y)) =
      (16 * r ^ 2 * V) • q := funext fun A => heq _
  rw [hf, hq, eLpNorm_const_smul, eLpNorm_const_smul, ← mul_add,
    Real.enorm_eq_ofReal (by positivity : 0 ≤ 16 * r ^ 2 * V)]
  calc
    _ ≤ ENNReal.ofReal (16 * r ^ 2 * V) * ENNReal.ofReal (C * (4 * R)⁻¹) :=
      mul_le_mul_right ht _
    _ = ENNReal.ofReal ((4 * r ^ 2 * V * C) * R⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

end EinsteinRelation.Correctors
