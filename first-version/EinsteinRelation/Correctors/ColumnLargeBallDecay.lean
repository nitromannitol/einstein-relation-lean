import EinsteinRelation.Correctors.BallEnergyAveraging
import EinsteinRelation.Correctors.SpecifiedColumnCopyEstimates

/-! # Uniform larger-ball decay of the actual parabolic gradient

Source: `paper/main.tex:790–808,842–849`. The actual semigroup energy
class supplies spatial L2 slices. Averaging translated unit-ball estimates
then gives a bound uniform over all larger radii, at almost every time.
-/

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The prescribed actual column has a radius-uniform larger-ball decay
bound. The constant precedes the law, column, flow and averaging radius.
No extra spatial energy or stationary identification premise is used.
Source: `paper/main.tex:790–808,842–849`. -/
theorem actual_column_large_ball_gradient_decay
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ m : ℝ) (hL : 1 ≤ L) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      (∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
        HasWeakGradient univ (fun x => u A (t,x)) (fun x => G A (t,x))) →
      ∀ R : ℝ, 1 ≤ R → ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)),
        MemLp (fun A => vectorRms volume (originBall d R) (fun x => G A (t,x)))
          (ENNReal.ofReal m) (actualCoefficientLaw Q) ∧
        eLpNorm (fun A => vectorRms volume (originBall d R) (fun x => G A (t,x)))
          (ENNReal.ofReal m) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C*t^(-1-(d : ℝ)/4)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_column_gradient_decay_and_tail
    hdecay hreg d hd L r₀ hL
  refine ⟨Real.sqrt (2^d : ℝ)*C m,mul_pos (Real.sqrt_pos.mpr (by positivity)) (hC m hm),?_⟩
  intro Q i u G hu hG hflow hweak R hR
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hJG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => J (G z.1 z.2)) := J.continuous.measurable.comp hG
  have hvol (r : ℝ) : originBall d r = ball (0 : Vec d) r := by
    ext x
    simp only [originBall,ball,mem_setOf_eq,sub_zero]
  have hs : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)),
      MemLp (fun x => J (G A (t,x))) 2 (volume.restrict (ball (0 : Vec d) (3*R))) := by
    filter_upwards [hflow] with A hA
    filter_upwards [semigroupSolution_gradient_tail_slice_memLp hA.1
      (hG.comp (measurable_const.prodMk measurable_id)) zero_lt_one (by linarith : 0 < 3*R)]
      with t ht
    simpa only [hvol] using J.toContinuousLinearMap.comp_memLp' ht
  have hn : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) × ℝ =>
      eLpNorm (fun x => J (G z.1 (z.2,x))) 2
        (volume.restrict (ball (0 : Vec d) (3*R)))) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    exact ((hJG.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))).enorm.pow_const _).lintegral_prod_right' |>.pow_const _
  have hsections : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)), ∀ᵐ A ∂actualCoefficientLaw Q,
      MemLp (fun x => J (G A (t,x))) 2 (volume.restrict (ball (0 : Vec d) (3*R))) := by
    have ha : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)),
        eLpNorm (fun x => J (G A (t,x))) 2
          (volume.restrict (ball (0 : Vec d) (3*R))) < ⊤ :=
      hs.mono fun _ hA => hA.mono fun _ ht => ht.2
    have hset : MeasurableSet {z : Coefficient d (AKMUpperEllipticity L) × ℝ |
        eLpNorm (fun x => J (G z.1 (z.2,x))) 2
          (volume.restrict (ball (0 : Vec d) (3*R))) < ⊤} :=
      measurableSet_lt hn measurable_const
    have hh := (Measure.ae_ae_comm hset).mp ha
    filter_upwards [hh] with t ht
    filter_upwards [ht] with A hA
    exact ⟨(hJG.comp (measurable_const.prodMk
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable,hA⟩
  have hsq (v : Vec d) : ‖J v‖^2 = euclideanSq v := by
    change ‖WithLp.toLp 2 v‖^2 = _
    rw [← TimeChange.euclideanNorm_eq_norm_toLp]
    exact Real.sq_sqrt (euclideanSq_nonneg_fisher _)
  filter_upwards [hsections,ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht ht1
  have hb := (hbound Q i u G hu hG hflow hweak).1
  have hlarge := ball_rms_moment_le_of_unit_moments (actualCoefficientLaw Q)
    hR hm (mul_nonneg (hC m hm).le (Real.rpow_nonneg (by exact zero_le_one.trans ht1.le : 0 ≤ t) _))
    (fun z => J (G z.1 (t,z.2)))
    (hJG.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    (by
      filter_upwards [ht] with A hA
      have hv : ∀ᵐ v ∂((volume (ball (0 : Vec d) (2*R)))⁻¹ •
          volume.restrict (ball (0 : Vec d) (2*R))), v ∈ ball (0 : Vec d) (2*R) :=
        (ae_restrict_mem (μ := volume) (paired_isOpen_ball _ _).measurableSet).filter_mono
          Measure.smul_absolutelyContinuous.ae_le
      exact hv.mono fun v hv => translated_unit_memLp_of_ball hR hA hv)
    (fun v => by
      simpa only [hsq,vectorRms,setAverage_eq',hvol] using
        (hb v m t hm ht1.le).2)
  simpa only [hsq,vectorRms,setAverage_eq',hvol,mul_assoc] using hlarge.2

end EinsteinRelation.Correctors
