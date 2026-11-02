import EinsteinRelation.Correctors.ParabolicLargeScaleFlow
import EinsteinRelation.Correctors.PairedPDEBallNormalization

/-! # The random-radius volume cost in semigroup gradient decay

Source: `paper/main.tex:788–796`. Comparison from the AKM random scale
to the unit ball gives the precise factor `X^(d/2)` in the good event.
The remaining Caccioppoli and probability estimates are separate.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- The two source interfaces use the same Euclidean origin ball.
Source: `paper/main.tex:788–796,862–866`. -/
theorem originBall_eq_gt_ball (d : ℕ) (r : ℝ) :
    originBall d r = ball (0 : Vec d) r := by
  ext x
  simp only [originBall, ball, sub_zero]

/-- The exact unit-ball volume comparison costs `r^(d/2)`.
Source: `paper/main.tex:788–796`. -/
theorem vectorRms_unitBall_le {d : ℕ} {r : ℝ} (hr : 1 ≤ r)
    (G : Vec d → Vec d)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict (originBall d r))) :
    vectorRms volume (originBall d 1) G ≤
      r ^ ((d : ℝ)/2) * vectorRms volume (originBall d r) G := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hV := paired_ball_volume_pos_finite (d := d) (by norm_num : (0 : ℝ) < 1)
  have hVr := paired_ball_volume_pos_finite (d := d) hr0
  rw [← originBall_eq_gt_ball] at hV hVr
  have hsub : originBall d 1 ⊆ originBall d r := fun _ hx => lt_of_lt_of_le hx hr
  have h := vectorRms_mono_set_volume_ratio volume hsub
    (ENNReal.toReal_pos_iff.mp hV).1.ne' (ENNReal.toReal_pos_iff.mp hV).2.ne
    (ENNReal.toReal_pos_iff.mp hVr).2.ne G hG
  have hv : (volume (originBall d r)).toReal =
      r ^ d * (volume (originBall d 1)).toReal := by
    simpa only [originBall_eq_gt_ball, Measure.real] using paired_ball_volume_real (d := d) hr0
  have hratio : (volume (originBall d r)).toReal / (volume (originBall d 1)).toReal = r^d := by
    rw [hv]
    exact mul_div_cancel_right₀ _ (show (volume (originBall d 1)).toReal ≠ 0 from hV.ne')
  rw [hratio, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le] at h
  simpa only [div_eq_mul_inv, one_div, one_mul] using h

/-- On the good event `4 X ≤ R`, the actual semigroup unit-ball gradient
is bounded by `C X^(d/2)` times its large-cylinder gradient energy. This
keeps the source's almost-every-time interpretation intact.
Source: `paper/main.tex:788–796`. -/
theorem parabolicLargeScale_semigroup_unit_gradient (hAKM : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∃ X : Coefficient d K → ℝ, Measurable X ∧
        (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound P s C X ∧
        ∀ᵐ A ∂P, ∀ (g : Vec d → Vec d) (u : ℝ × Vec d → ℝ)
          (G : ℝ × Vec d → Vec d), IsSemigroupSolution A g u G →
          ∀ R : ℝ, 4 * X A ≤ R → ∀ t : ℝ, R^2 < t →
            ∀ᵐ τ ∂volume.restrict (Set.Ioo (-((2 * X A)^2)/4) 0),
              vectorRms volume (originBall d 1) (fun x => G (τ+t,x)) ≤
                C * (X A) ^ ((d : ℝ)/2) *
                  vectorRms volume (cylinder d R) (fun z => G (z.1+t,z.2)) := by
  obtain ⟨C, hC, hreg⟩ := hAKM d hd K s hK hs hsd
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨X, hXm, hX, htail, hbound⟩ := hreg P hP
  refine ⟨X, hXm, hX, htail, ?_⟩
  filter_upwards [hbound] with A hA
  intro g u G hsol R hR t ht
  have hX0 : 0 < X A := zero_lt_one.trans_le (hX A)
  have hXR : X A ≤ R := by linarith
  have hR0 : 0 < R := hX0.trans_le hXR
  have hshift := semigroupSolution_backward_cylinder hsol hR0 ht
  have hslice := parabolicSolution_gradient_slice_memLp hshift
  have htsub : Set.Ioo (-((2*X A)^2)/4) 0 ⊆ Set.Ioc (-(R^2)) 0 := by
    intro τ hτ
    have hp : (2*X A)^2 ≤ R^2 := by nlinarith
    exact ⟨by nlinarith [hτ.1], hτ.2.le⟩
  have hslices := hslice.filter_mono (ae_mono (Measure.restrict_mono_set volume htsub))
  have hb := hA R hXR _ _ hshift (2*X A) (by linarith) (by linarith)
  simp only [mul_div_cancel_left₀ (X A) (by norm_num : (2 : ℝ) ≠ 0)] at hb
  filter_upwards [hslices, hb] with τ hG hτ
  have hsub : originBall d (X A) ⊆ originBall d R := fun _ hx => lt_of_lt_of_le hx hXR
  have hsmall := hG.mono_measure (Measure.restrict_mono_set volume hsub)
  calc
    _ ≤ (X A)^((d : ℝ)/2) * vectorRms volume (originBall d (X A))
        (fun x => G (τ+t,x)) := vectorRms_unitBall_le (hX A) _ hsmall
    _ ≤ (X A)^((d : ℝ)/2) *
        (C * vectorRms volume (cylinder d R) (fun z => G (z.1+t,z.2))) :=
      mul_le_mul_of_nonneg_left hτ (Real.rpow_nonneg hX0.le _)
    _ = _ := by ring

end EinsteinRelation.Correctors
