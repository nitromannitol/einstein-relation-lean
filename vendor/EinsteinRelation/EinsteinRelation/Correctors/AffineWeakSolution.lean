import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import EinsteinRelation.Calculus.WeakDerivativeRestriction
import EinsteinRelation.Correctors.BallPoincareTransfer
import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinRelation.Correctors.SpatialBallVolume

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Adding the affine coordinate to a Sobolev corrector yields the literal
homogeneous weak solution; source `paper/main.tex:693-698,727-729`. -/
theorem affine_weakSolution_of_weakPotential {d : ℕ}
    (R : ℝ) (hR : 0 < R) (i : Fin d) (a : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : MemLp g 2 (volume.restrict (ball 0 R)))
    (hweak : HasWeakGradient (ball 0 R) u g)
    (hflux : HasWeakDivergence (ball 0 R)
      (fun x => (a x).mulVec (unitVector i + g x)) (fun _ => 0)) :
    WeakSolution (ball 0 R) a (fun x => x i + u x)
      (fun x => unitVector i + g x) := by
  have hv := ball_volume_pos_finite d R hR
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hv).2.ne
  have hm : MemLp (fun x : Vec d => x i) 2 (volume.restrict (ball 0 R)) := by
    apply (memLp_const R).of_le (continuous_apply i).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (by
      unfold ball euclideanNorm euclideanSq dot
      exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)] with x hx
    change |x i| ≤ |R|
    rw [abs_of_pos hR]
    exact (Regeneration.coordinate_abs_le_euclideanNorm x i).trans
      (by
        change euclideanNorm (x - 0) < R at hx
        simpa only [sub_zero] using hx.le)
  refine ⟨hm.add hu, (memLp_const (unitVector i)).add hg, ?_, hflux⟩
  intro j
  have hclass : HasWeakPartialDerivative (ball (0 : Vec d) R) j
      (fun x : Vec d => x i) (fun _ => unitVector i j) := by
    have hc := hasWeakPartialDerivative_of_contDiff j (fun x : Vec d => x i)
      (contDiff_apply ℝ ℝ i)
    have heq : coordinateDerivative j (fun x : Vec d => x i) =
        fun _ : Vec d => unitVector i j := by
      funext x
      rw [coordinateDerivative, (hasFDerivAt_apply i x).fderiv]
      change unitVector j i = unitVector i j
      simp [unitVector, Pi.single_apply, eq_comm]
    rw [heq] at hc
    exact HasWeakPartialDerivative.restrict (Set.subset_univ _)
      (by
        unfold ball euclideanNorm euclideanSq dot
        exact (isOpen_lt (by fun_prop) continuous_const).measurableSet)
      MeasurableSet.univ hc
  refine ⟨hclass.1.add (hweak j).1, hclass.2.1.add (hweak j).2.1, ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative j φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨B, hB⟩ := (hφ.2.1.fderiv_apply ℝ (unitVector j)).exists_bound_of_continuous hd
  obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
  have h1 := (hm.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable (ae_of_all _ hB)
  have h2 := (hu.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable (ae_of_all _ hB)
  have h3 := (integrable_const (μ := volume.restrict (ball (0 : Vec d) R)) (unitVector i j)).mul_bdd hφ.1.continuous.aestronglyMeasurable
    (ae_of_all _ hC)
  have h4 := ((memLp_pi_iff.mp hg j).integrable (by norm_num)).mul_bdd
    hφ.1.continuous.aestronglyMeasurable (ae_of_all _ hC)
  change (∫ x in ball (0 : Vec d) R, (x i + u x) * coordinateDerivative j φ x) =
    -(∫ x in ball (0 : Vec d) R, (unitVector i j + g x j) * φ x)
  simp_rw [add_mul]
  rw [integral_add h1 h2, integral_add h3 h4, hclass.2.2 φ hφ, (hweak j).2.2 φ hφ]
  ring

end EinsteinRelation.Correctors
