import EinsteinRelation.Calculus.WeakGradientExhaustion
import EinsteinRelation.Calculus.WeakGradientSubtraction
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Correctors.SpatialBallVolume

/-! # Subtracting affine corrector equations

Source: `paper/main.tex:693-698,727-729`. The common affine slope cancels
and the difference is a genuine weak homogeneous solution on every ball.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem integrable_flux_test {d : ℕ} {F : Vec d → Vec d}
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) Set.univ volume)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest Set.univ φ) :
    Integrable (fun x => dot (F x) (gradient φ x)) volume := by
  unfold dot
  apply integrable_finset_sum
  intro i _
  have hi : LocallyIntegrable (fun x => F x i) volume := by
    simpa only [locallyIntegrableOn_univ] using hF i
  have hd : Continuous (coordinateDerivative i φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  exact hi.integrable_smul_right_of_hasCompactSupport hd hdc

/-- Homogeneous weak divergence equations are closed under subtraction. -/
theorem hasWeakDivergence_sub_zero_univ {d : ℕ} {F G : Vec d → Vec d}
    (hF : HasWeakDivergence Set.univ F (fun _ => 0))
    (hG : HasWeakDivergence Set.univ G (fun _ => 0)) :
    HasWeakDivergence Set.univ (fun x => F x - G x) (fun _ => 0) := by
  refine ⟨fun i => (hF.1 i).sub (hG.1 i), locallyIntegrableOn_zero, ?_⟩
  intro φ hφ
  have hfi := integrable_flux_test hF.1 hφ
  have hgi := integrable_flux_test hG.1 hφ
  have heq : (fun x => dot (F x - G x) (gradient φ x)) =
      (fun x => dot (F x) (gradient φ x) - dot (G x) (gradient φ x)) := by
    funext x
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hFzero : (∫ x, dot (F x) (gradient φ x)) = 0 := by
    simpa only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] using hF.2.2 φ hφ
  have hGzero : (∫ x, dot (G x) (gradient φ x)) = 0 := by
    simpa only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] using hG.2.2 φ hφ
  simp only [Measure.restrict_univ, heq, integral_sub hfi hgi,
    hFzero, hGzero, zero_mul, integral_zero, neg_zero, sub_self]

/-- Subtract two affine correctors without altering their weak representatives. -/
theorem affine_corrector_difference_weakSolution {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (e : Vec d) (u v : Vec d → ℝ) (g h : Vec d → Vec d)
    (hwu : HasWeakGradient Set.univ u g) (hwv : HasWeakGradient Set.univ v h)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hv : ∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (ball 0 R)))
    (hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)))
    (hh : ∀ R : ℝ, 0 < R → MemLp h 2 (volume.restrict (ball 0 R)))
    (hdu : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (hdv : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + h x)) (fun _ => 0)) :
    HasWeakGradient Set.univ (fun x => u x - v x) (fun x => g x - h x) ∧
      ∀ R : ℝ, 0 < R → External.GilbargTrudinger.WeakSolution (ball 0 R) a.field
        (fun x => u x - v x) (fun x => g x - h x) := by
  have hw (R : ℝ) (hR : 0 < R) :
      HasWeakGradient (ball 0 R) (fun x => u x - v x) (fun x => g x - h x) := by
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
      simpa using (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2⟩
    exact hasWeakGradient_sub_of_memLp _ u v g h (hu R hR) (hv R hR) (hg R hR) (hh R hR)
      (fun i => (hwu i).restrict_subset (Set.subset_univ _) MeasurableSet.univ)
      (fun i => (hwv i).restrict_subset (Set.subset_univ _) MeasurableSet.univ)
  have hflux : (fun x => (a x).mulVec (e + g x) - (a x).mulVec (e + h x)) =
      (fun x => (a x).mulVec (g x - h x)) := by
    funext x
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sub]
    abel
  have hdif := hasWeakDivergence_sub_zero_univ hdu hdv
  rw [hflux] at hdif
  refine ⟨hasWeakGradient_univ_of_balls _ _ (fun n => hw _ (by positivity)), ?_⟩
  intro R hR
  exact ⟨(hu R hR).sub (hv R hR), (hg R hR).sub (hh R hR), hw R hR,
    hdif.restrict_subset (Set.subset_univ _) MeasurableSet.univ⟩

end EinsteinRelation.Correctors
