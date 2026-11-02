import EinsteinRelation.Correctors.AffineWeakSolution

/-! Arbitrary-center affine weak coordinates, `paper/main.tex:727-731`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The Lebesgue volume of any Euclidean ball with positive radius is positive,
regardless of center. -/
private theorem volume_euclideanBall_pos {d : ℕ} (z : Vec d) (R : ℝ) (hR : 0 < R) :
    0 < volume.real (ball z R) := by
  have hU : IsOpen (ball z R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hne : (ball z R).Nonempty := by
    refine ⟨z, ?_⟩
    have hzero : euclideanNorm (0 : Vec d) = (0 : ℝ) := by
      simp [euclideanNorm, euclideanSq, dot]
    simpa [ball, sub_self, hzero] using hR
  have hfin : volume (ball z R) ≠ ⊤ := by
    have h_sub : ball z R ⊆ Metric.closedBall z R := by
      intro y hy
      have hy' : euclideanNorm (y - z) < R := by
        simpa [ball] using hy
      rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
      intro j
      rw [Real.dist_eq]
      have hj := Regeneration.coordinate_abs_le_euclideanNorm (y - z) j
      have : |y j - z j| = |(y - z) j| := by simp
      rw [this]
      exact hj.trans hy'.le
    have h_closedBall_fin : volume (Metric.closedBall z R) ≠ ⊤ := by
      rw [Real.volume_pi_closedBall _ hR.le]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h_closedBall_fin (measure_mono h_sub)
  exact ENNReal.toReal_pos (hU.measure_pos volume hne).ne' hfin

/-- Add the centered affine coordinate to a weak corrector at any center
and in any scalar gauge. The coefficient and flux equation are unchanged. -/
theorem affine_weakSolution_on_ball_of_weakPotential {d : ℕ}
    (z : Vec d) (R : ℝ) (hR : 0 < R) (i : Fin d) (a : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ)
    (hu : MemLp (fun x => u x - c) 2 (volume.restrict (ball z R)))
    (hg : MemLp g 2 (volume.restrict (ball z R)))
    (hweak : HasWeakGradient (ball z R) (fun x => u x - c) g)
    (hflux : HasWeakDivergence (ball z R)
      (fun x => (a x).mulVec (unitVector i + g x)) (fun _ => 0)) :
    WeakSolution (ball z R) a (fun x => x i - z i + u x - c)
      (fun x => unitVector i + g x) := by
  have hv := volume_euclideanBall_pos z R hR
  letI : IsFiniteMeasure (volume.restrict (ball z R)) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hv).2.ne
  have hm : MemLp (fun x : Vec d => x i - z i) 2 (volume.restrict (ball z R)) := by
    apply (memLp_const R).of_le
      ((continuous_apply i).sub continuous_const).aestronglyMeasurable
    have h_open : MeasurableSet (ball z R) := by
      unfold ball euclideanNorm euclideanSq dot
      exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
    filter_upwards [ae_restrict_mem h_open] with x hx
    have hRnorm : ‖R‖ = R := abs_of_pos hR
    rw [hRnorm]
    calc
      ‖x i - z i‖ = ‖(x - z) i‖ := by simp
      _ ≤ euclideanNorm (x - z) := Regeneration.coordinate_abs_le_euclideanNorm (x - z) i
      _ ≤ R := hx.le
  have hsum : MemLp (fun x => x i - z i + u x - c) 2 (volume.restrict (ball z R)) := by
    have hgoal : (fun x => x i - z i + u x - c) =
        ((fun x : Vec d => x i - z i) + (fun x => u x - c)) := by
      ext x; dsimp; abel
    rw [hgoal]
    exact hm.add hu
  refine ⟨hsum, (memLp_const (unitVector i)).add hg, ?_, hflux⟩
  intro j
  have hclass : HasWeakPartialDerivative (ball z R) j
      (fun x : Vec d => x i - z i) (fun _ => unitVector i j) := by
    have hc := hasWeakPartialDerivative_of_contDiff j
      (fun x : Vec d => x i - z i) ((contDiff_apply ℝ ℝ i).sub contDiff_const)
    have heq : coordinateDerivative j (fun x : Vec d => x i - z i) =
        fun _ : Vec d => unitVector i j := by
      funext x
      rw [coordinateDerivative]
      have hderiv : fderiv ℝ (fun x : Vec d => x i - z i) x =
          fderiv ℝ (fun x : Vec d => x i) x := by
        simpa using fderiv_sub_const (z i) (f := fun x : Vec d => x i) (x := x)
      rw [hderiv, (hasFDerivAt_apply i x).fderiv]
      change unitVector j i = unitVector i j
      simp [unitVector, Pi.single_apply, eq_comm]
    rw [heq] at hc
    exact hc.restrict (Set.subset_univ _) (by
      unfold ball euclideanNorm euclideanSq dot
      exact (isOpen_lt (by fun_prop) continuous_const).measurableSet) MeasurableSet.univ
  have hgoal_add : (fun x => x i - z i + u x - c) =
      ((fun x : Vec d => x i - z i) + (fun x => u x - c)) := by
    ext x; dsimp; abel
  have hgoal_g : (fun x => (unitVector i + g x) j) =
      ((fun _ => unitVector i j) + (fun x => g x j)) := by
    ext x; rfl
  have hball_meas : MeasurableSet (ball z R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [hgoal_add]
    exact hclass.1.add (hweak j).1
  ·
    rw [hgoal_g]
    exact hclass.2.1.add (hweak j).2.1
  · intro φ hφ
    have hd : Continuous (coordinateDerivative j φ) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨B, hB⟩ := (hφ.2.1.fderiv_apply ℝ (unitVector j)).exists_bound_of_continuous hd
    obtain ⟨C, hC⟩ := hφ.2.1.exists_bound_of_continuous hφ.1.continuous
    have h1 := (hm.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable (ae_of_all _ hB)
    have h2 := (hu.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable (ae_of_all _ hB)
    have h3 := (integrable_const (μ := volume.restrict (ball z R)) (unitVector i j)).mul_bdd
      hφ.1.continuous.aestronglyMeasurable (ae_of_all _ hC)
    have h4 := ((memLp_pi_iff.mp hg j).integrable (by norm_num)).mul_bdd
      hφ.1.continuous.aestronglyMeasurable (ae_of_all _ hC)
    simp
    calc
      (∫ x in ball z R, (x i - z i + u x - c) * coordinateDerivative j φ x) =
          (∫ x in ball z R, ((x i - z i) * coordinateDerivative j φ x +
            (u x - c) * coordinateDerivative j φ x)) := by
        refine setIntegral_congr_fun hball_meas ?_
        intro x hx; ring
      _ = (∫ x in ball z R, (x i - z i) * coordinateDerivative j φ x) +
          (∫ x in ball z R, (u x - c) * coordinateDerivative j φ x) :=
        integral_add h1 h2
      _ = (-(∫ x in ball z R, unitVector i j * φ x)) +
          (-(∫ x in ball z R, g x j * φ x)) := by
        rw [hclass.2.2 φ hφ, (hweak j).2.2 φ hφ]
      _ = -(∫ x in ball z R, (unitVector i j * φ x + g x j * φ x)) := by
        calc
          (-(∫ x in ball z R, unitVector i j * φ x)) + (-(∫ x in ball z R, g x j * φ x))
              = -((∫ x in ball z R, unitVector i j * φ x) + (∫ x in ball z R, g x j * φ x)) := by ring
          _ = -(∫ x in ball z R, (unitVector i j * φ x + g x j * φ x)) := by rw [← integral_add h3 h4]
      _ = -(∫ x in ball z R, (unitVector i j + g x j) * φ x) := by
        refine congrArg (fun t => -t) (setIntegral_congr_fun hball_meas ?_)
        intro x hx; ring

end EinsteinRelation.Correctors
