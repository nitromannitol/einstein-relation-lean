import EinsteinFull.Homogenization.HighContrastLocalSobolev
import EllipticRegularity.Energy.CoefficientEnergyCaccioppoli
import PDEFoundation.Sobolev.Cutoff.Ball
import PDEFoundation.Geometry.ConvexDomain

/-!
# The Caccioppoli inequality on Euclidean balls

For a whole-space weak solution of a divergence-form equation with a measurable coefficient
field that is pointwise `(1, K)`-elliptic, the energy on a ball is controlled by the square
deviation on the doubled ball. This transfers the reabsorbed Caccioppoli estimate of the
elliptic regularity library of Armstrong, Kuusi and Loher to the weak-solution vocabulary of
their high-contrast homogenization theory.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

/-- **Caccioppoli inequality** for a whole-space weak solution on concentric Euclidean balls of
radii `r` and `2r`. -/
theorem caccioppoli_euclideanBall {f : CoeffField d} {K : ℝ} (hK : 1 ≤ K)
    (hfm : Measurable (fun x i j => f x i j)) (hf : ∀ x, IsEllipticMatrix 1 K (f x))
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hw : HasWeakGradientOn Set.univ u Du)
    {r : ℝ} (hr : 0 < r)
    (hu2 : MemLp u 2 (volume.restrict (euclideanBall d (4 * r))))
    (hDu2 : ∀ i, MemLp (fun x => Du x i) 2 (volume.restrict (euclideanBall d (4 * r))))
    (hsol : IsWeakSolutionOn f Set.univ Du) (k : ℝ) :
    ∫ x in euclideanBall d r, vecNormSq (Du x) ≤
      4 * K * (32 / r) ^ 2 * ∫ x in euclideanBall d (2 * r), (u x - k) ^ 2 := by
  let U : Set (Vec d) := euclideanBall d (4 * r)
  have hUopen : IsOpen U := HighContrast.isOpen_euclideanBall d (4 * r)
  have hU : PDE.IsOpenBoundedConvexDomain U :=
    PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (by positivity)
  have hwU : HasWeakGradientOn U u Du := hw.restrict hUopen (Set.subset_univ _)
  let uP : PDE.H1Function U :=
    { toFun := u
      grad := Du
      memL2 := hu2
      gradMemL2 := hDu2
      hasWeakGradient := fun i φ h1 h2 h3 => hwU i φ h1 h2 h3 }
  have hmeasf (i j : Fin d) : Measurable (fun x => f x i j) :=
    (measurable_pi_iff.mp (measurable_pi_iff.mp hfm i)) j
  have hEll : PDE.IsEllipticFieldOn 1 K U f := by
    refine ⟨?_, fun x _ => hf x⟩
    classical
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact Measurable.ite hUopen.measurableSet (hmeasf i j) measurable_const
  have hsolP : PDE.IsWeakDivergenceFormHarmonicOn f U uP := by
    intro φ
    obtain ⟨hint, hzero⟩ := hsol φ.toFun ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
    have hpt (x : Vec d) : PDE.vecDot (PDE.matVecMul (f x) (uP.grad x)) (φ.grad x) =
        vecDot (smoothGrad φ.toFun x) (matVecMul (f x) (Du x)) := by
      change vecDot (matVecMul (f x) (Du x)) (smoothGrad φ.toFun x) = _
      exact vecDot_comm _ _
    have hsupp : ∀ x ∉ U, vecDot (smoothGrad φ.toFun x) (matVecMul (f x) (Du x)) = 0 := by
      intro x hx
      have hxφ : x ∉ tsupport φ.toFun := fun h => hx (φ.tsupport_subset h)
      have hfd : fderiv ℝ φ.toFun x = 0 := by
        by_contra hne
        exact hxφ (support_fderiv_subset ℝ hne)
      have hg : smoothGrad φ.toFun x = 0 := by
        funext i
        simp [smoothGrad, hfd]
      rw [hg]
      simp [vecDot]
    have hfun : (fun x => PDE.vecDot (PDE.matVecMul (f x) (uP.grad x)) (φ.grad x)) =
        fun x => vecDot (smoothGrad φ.toFun x) (matVecMul (f x) (Du x)) := funext hpt
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hfun]
      exact hint.mono_set (Set.subset_univ _)
    · simp
    · simp [PDE.vecDot]
    · rw [hfun, setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      simp only [Measure.restrict_univ] at hzero
      rw [hzero]
      simp [PDE.vecDot]
  have hinner : MeasurableSet (euclideanBall d r) :=
    (HighContrast.isOpen_euclideanBall d r).measurableSet
  have houter : MeasurableSet (euclideanBall d (2 * r)) :=
    (HighContrast.isOpen_euclideanBall d (2 * r)).measurableSet
  have hsub : euclideanBall d (2 * r) ⊆ U := by
    intro x hx
    have hx' : vecNormSq (x - 0) < (2 * r) ^ 2 := hx
    show vecNormSq (x - 0) < (4 * r) ^ 2
    nlinarith
  let η := PDE.quantitativeBallCutoff (0 : Vec d) hr.le (by linarith : r < 2 * r)
  have hmain := PDE.caccioppoli_coefficient_energy_on_inner (k := k) hU hinner houter hEll
    one_pos (by linarith) hsolP η hsub
  have hrr : 2 * r - r = r := by ring
  simp only [div_one, hrr] at hmain
  have hinnerU : euclideanBall d r ⊆ U := by
    intro x hx
    have hx' : vecNormSq (x - 0) < r ^ 2 := hx
    show vecNormSq (x - 0) < (4 * r) ^ 2
    nlinarith
  have hsqi (i : Fin d) : IntegrableOn (fun x => Du x i * Du x i) (euclideanBall d r) volume := by
    have h : IntegrableOn (fun x => Du x i ^ 2) U volume := (hDu2 i).integrable_sq
    exact (h.mono_set hinnerU).congr_fun (fun x _ => by ring) hinner
  have hDuint : IntegrableOn (fun x => vecNormSq (Du x)) (euclideanBall d r) volume := by
    have h := integrable_finsetSum (μ := volume.restrict (euclideanBall d r)) Finset.univ
      fun i _ => hsqi i
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [vecNormSq, vecDot]
  have hmeasDu (i : Fin d) : AEStronglyMeasurable (fun x => Du x i)
      (volume.restrict (euclideanBall d r)) :=
    ((hDu2 i).aestronglyMeasurable).mono_measure (Measure.restrict_mono hinnerU le_rfl)
  have hEint : IntegrableOn (fun x => vecDot (Du x) (matVecMul (f x) (Du x)))
      (euclideanBall d r) volume := by
    have hmeas : AEStronglyMeasurable (fun x => vecDot (Du x) (matVecMul (f x) (Du x)))
        (volume.restrict (euclideanBall d r)) := by
      simp only [vecDot, matVecMul]
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hmeasDu i).mul ?_
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        ((hmeasf i j).aestronglyMeasurable).mul (hmeasDu j)
    refine (hDuint.const_mul K).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (Du x) (matVecMul (f x) (Du x))
    have hfb := vecNormSq_matVecMul_le_of_isEllipticMatrix (hf x) (Du x)
    have hnn := vecNormSq_nonneg (Du x)
    have h2 : vecDot (Du x) (matVecMul (f x) (Du x)) ^ 2 ≤ (K * vecNormSq (Du x)) ^ 2 := by
      calc _ ≤ vecNormSq (Du x) * vecNormSq (matVecMul (f x) (Du x)) := hcs
        _ ≤ vecNormSq (Du x) * (K ^ 2 * vecNormSq (Du x)) :=
          mul_le_mul_of_nonneg_left hfb hnn
        _ = (K * vecNormSq (Du x)) ^ 2 := by ring
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.elim fun h1 h3 => abs_le.mpr ⟨h1, h3⟩
  calc ∫ x in euclideanBall d r, vecNormSq (Du x)
      ≤ ∫ x in euclideanBall d r, vecDot (Du x) (matVecMul (f x) (Du x)) := by
        refine setIntegral_mono_on hDuint hEint hinner fun x _ => ?_
        have h := (hf x).2.2.1 (Du x)
        linarith
    _ ≤ 4 * K * (32 / r) ^ 2 * ∫ x in euclideanBall d (2 * r), (u x - k) ^ 2 := hmain

end EinsteinFull.Homogenization
