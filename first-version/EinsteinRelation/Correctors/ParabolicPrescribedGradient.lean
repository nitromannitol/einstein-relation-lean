import EinsteinRelation.Correctors.PrescribedTimeGradientRecovery
import EinsteinRelation.Correctors.EuclideanRmsNorm
import EinsteinRelation.Correctors.TimeIntervalTranslation
import EinsteinRelation.Correctors.ParabolicUnitScaleGradient
import EinsteinRelation.Correctors.SemigroupLocalL2Continuity

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport

/-- AKM Remark 8.8 gives a genuine gradient at a prescribed final time.
The representative is recovered from the continuous scalar flow.
Source: `paper/main.tex:798–806`. -/
theorem parabolicLargeScale_semigroup_prescribed_gradient
    (hAKM : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (K s : ℝ) (hK : 1 < K) (hs : 0 < s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Measure (Coefficient d K), IsAdmissibleLaw P →
      ∃ X : Coefficient d K → ℝ, Measurable X ∧
        (∀ A, 1 ≤ X A) ∧ StretchedExponentialBound P s C X ∧
        ∀ᵐ A ∂P, ∀ (g : Vec d → Vec d) (u : ℝ × Vec d → ℝ)
          (G : ℝ × Vec d → Vec d), IsSemigroupSolution A g u G →
          ∀ R : ℝ, X A ≤ R → ∀ t : ℝ, R^2 < t →
            ∀ r : ℝ, X A ≤ r → r ≤ R / 2 →
              ∃ H : Vec d → Vec d,
                HasWeakGradient (originBall d (r/2)) (fun x => u (t,x)) H ∧
                MemLp (fun x => euclideanNorm (H x)) 2
                  (volume.restrict (originBall d (r/2))) ∧
                vectorRms volume (originBall d (r/2)) H ≤
                  Real.sqrt d * C * vectorRms volume (cylinder d R)
                    (fun z => G (z.1+t,z.2)) := by
  obtain ⟨C,hC,hreg⟩ := parabolicLargeScale_semigroup_gradient hAKM d hd K s hK hs hsd
  refine ⟨C,hC,?_⟩
  intro P hP
  obtain ⟨X,hXm,hX,htail,hbound⟩ := hreg P hP
  refine ⟨X,hXm,hX,htail,?_⟩
  filter_upwards [hbound] with A hA
  intro g u G hsol R hR t ht r hr hrR
  have hr0 : 0 < r := zero_lt_one.trans_le ((hX A).trans hr)
  have hR0 : 0 < R := hr0.trans_le (by linarith)
  have ha : 0 < t-r^2/4 := by nlinarith [sq_nonneg R, sq_nonneg r]
  have hab : t-r^2/4 < t := by nlinarith [sq_pos_of_pos hr0]
  let U := originBall d (r/2)
  have hUcompact : IsCompact (closure U) := by
    let F : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
    have hc : IsCompact (F '' Metric.closedBall 0 (r/2)) :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (r/2)).image
        (PiLp.continuous_ofLp 2 _)
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hc.isClosed
    intro x hx
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) - 0‖ ≤ r/2
    rw [sub_zero, ← TimeChange.euclideanNorm_eq_norm_toLp]
    exact le_of_lt hx
  have hUfin : volume U ≠ ⊤ :=
    ne_top_of_le_ne_top (hUcompact.measure_ne_top (μ := volume)) (measure_mono subset_closure)
  letI : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hUfin.lt_top⟩
  have hlocal := hsol.2.1 (t-r^2/4) t (r/2) ha hab (half_pos hr0)
  have hb := (ae_restrict_Ioo_add_right_iff
    (a := -(r^2)/4) (b := 0) (c := t)
    (p := fun q => vectorRms volume U (fun x => G (q,x)) ≤
      C * vectorRms volume (cylinder d R) (fun z => G (z.1+t,z.2)))).mp
        (hA g u G hsol R hR t ht r hr hrR)
  have he : -(r^2)/4+t = t-r^2/4 := by ring
  simp only [he, zero_add] at hb
  have hus : ∀ q ∈ Set.Icc (t-r^2/4) t,
      MemLp (fun x => u (q,x)) 2 (volume.restrict U) := fun q hq =>
    semigroupSolution_scalar_memLp_on_precompact hsol hUcompact (ha.trans_le hq.1)
  obtain ⟨H,hH,hHL,hHb⟩ :=
    continuous_flow_exists_weakGradient_of_ae_rms_bound hsol.1 ha hab
      (mul_nonneg hC.le (Real.sqrt_nonneg _)) hus hlocal.2.2.2.1
      (parabolicSolution_gradient_slice_memLp hlocal) hb t ⟨hab.le,le_rfl⟩
  refine ⟨H,hH,hHL,?_⟩
  rw [eLpNorm_euclideanNorm_toReal_eq_volume_mul_rms volume U H hHL] at hHb
  have hV : 0 < Real.sqrt ((volume U).toReal) := by
    apply Real.sqrt_pos.2
    simpa only [U,originBall_eq_gt_ball,Measure.real] using
      paired_ball_volume_pos_finite (d := d) (half_pos hr0)
  change vectorRms volume U H ≤ _
  apply (mul_le_mul_iff_right₀ hV).mp
  convert hHb using 1
  simp only [vectorRms, add_comm]
  ring

end EinsteinRelation.Correctors
