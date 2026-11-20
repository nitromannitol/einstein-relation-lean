import EinsteinFull.Homogenization.HighContrastCarrier
import EinsteinFull.Homogenization.HighContrastLocalSobolev
import EinsteinFull.Homogenization.WeakGradientDilation
import EinsteinFull.Homogenization.WeakGradientBridge
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Source correctors as correctors of the dilated coefficient

A source corrector of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Definitions 3.14–3.15, rescaled by the dilation `x ↦ 2x` that defines
the high-contrast coefficient of the source coefficient, is a whole-space `H¹_loc` function whose
corrected affine function solves the equation of the dilated coefficient in the weak sense of
Armstrong, Kuusi and Loher, *Homogenization at a polynomial scale in high contrast*.
-/

open MeasureTheory
open scoped Pointwise

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM

variable {d : ℕ}

/-- The dilated potential `x ↦ u(2x)/2`. -/
noncomputable def dilatedPotential (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  (2 : ℝ)⁻¹ * u ((2 : ℝ) • x)

/-- The dilated gradient `x ↦ g(2x)`. -/
noncomputable def dilatedGradient (g : Vec d → Vec d) (x : Vec d) : Vec d :=
  g ((2 : ℝ) • x)

theorem hasWeakGradientOn_of_hasWeakGradient {U : Set (Vec d)} {u : Vec d → ℝ}
    {g : Vec d → Vec d} (h : HasWeakGradient U u g) :
    _root_.Homogenization.HasWeakGradientOn U u g := by
  intro i φ hφ hc hs
  simpa only [coordinateDerivative, unitVector, _root_.Homogenization.basisVec] using
    (h i).2.2 φ ⟨hφ, hc, hs⟩

theorem hasWeakGradientOn_dilated {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ u g) :
    _root_.Homogenization.HasWeakGradientOn Set.univ (dilatedPotential u)
      (dilatedGradient g) :=
  EinsteinFull.Homogenization.HasWeakGradientOn.univ_dilate two_pos
    (hasWeakGradientOn_of_hasWeakGradient h)

theorem smul_openCubeSet_originCube_subset_ball (n : ℕ) :
    (2 : ℝ) • _root_.Homogenization.openCubeSet
        (_root_.Homogenization.originCube d (n : ℤ)) ⊆
      ball 0 ((Real.sqrt d + 1) * (3 : ℝ) ^ n) := by
  rintro _ ⟨x, hx, rfl⟩
  have hcoord (i : Fin d) : |x i| ≤ (3 : ℝ) ^ n / 2 :=
    ((mem_openCubeSet_originCube_iff.mp hx) i).le
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hsq : euclideanSq ((2 : ℝ) • x) ≤ (d : ℝ) * ((3 : ℝ) ^ n) ^ 2 := by
    rw [euclideanSq_smul]
    change (2 : ℝ) ^ 2 * ∑ i, x i * x i ≤ _
    have hsum : ∑ i, x i * x i ≤ ∑ _i : Fin d, ((3 : ℝ) ^ n / 2) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := hcoord i
      have h2 : x i * x i = |x i| ^ 2 := by rw [sq_abs, sq]
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith
  have hnorm : euclideanNorm ((2 : ℝ) • x) ≤ Real.sqrt d * (3 : ℝ) ^ n := by
    unfold euclideanNorm
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt d * (3 : ℝ) ^ n), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg d)]
    exact Real.sqrt_le_sqrt hsq
  change euclideanNorm ((2 : ℝ) • x - 0) < _
  rw [sub_zero]
  nlinarith

theorem memL2On_dilatedPotential {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) (n : ℕ) :
    _root_.Homogenization.MemL2On
      (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d (n : ℤ)))
      (dilatedPotential u) := by
  have hR : (0 : ℝ) < (Real.sqrt d + 1) * (3 : ℝ) ^ n := by positivity
  have h := ((hu _ hR).mono_measure (Measure.restrict_mono
    (smul_openCubeSet_originCube_subset_ball n) le_rfl))
  have hmeas : MeasurableSet
      (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d (n : ℤ))) :=
    (_root_.Homogenization.isOpenBoundedConvexDomain_openCubeSet _).isOpen.measurableSet
  exact (MemLp.comp_smul_restrict two_ne_zero hmeas h).const_mul _

theorem gradMemL2On_dilatedGradient {g : Vec d → Vec d}
    (hg : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R))) (n : ℕ) :
    _root_.Homogenization.GradMemL2On
      (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d (n : ℤ)))
      (dilatedGradient g) := by
  intro i
  have hR : (0 : ℝ) < (Real.sqrt d + 1) * (3 : ℝ) ^ n := by positivity
  have h := ((hg _ hR).mono_measure (Measure.restrict_mono
    (smul_openCubeSet_originCube_subset_ball n) le_rfl))
  have hmeas : MeasurableSet
      (_root_.Homogenization.openCubeSet (_root_.Homogenization.originCube d (n : ℤ))) :=
    (_root_.Homogenization.isOpenBoundedConvexDomain_openCubeSet _).isOpen.measurableSet
  exact MemLp.comp_smul_restrict two_ne_zero hmeas (memLp_pi_iff.mp h i)

theorem smoothGrad_comp_inv_two_smul {χ : Vec d → ℝ} (hχ : Differentiable ℝ χ) (y : Vec d) :
    _root_.Homogenization.HighContrast.smoothGrad χ ((2 : ℝ)⁻¹ • y) =
      (2 : ℝ) • gradient (fun z => χ ((2 : ℝ)⁻¹ • z)) y := by
  funext i
  simp only [_root_.Homogenization.HighContrast.smoothGrad, gradient, coordinateDerivative,
    Pi.smul_apply, smul_eq_mul]
  rw [fderiv_comp_smul_apply hχ, unitVector, ← _root_.Homogenization.basisVec]
  field_simp

/-- The corrected affine function of a dilated source corrector solves the equation of the
dilated coefficient, in the weak sense used by the high-contrast theory. -/
theorem isWeakSolutionOn_dilated {K : ℝ} (hK : 1 ≤ K) (a : Coefficient d K) (e : Vec d)
    {g : Vec d → Vec d}
    (hharm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0)) :
    _root_.Homogenization.HighContrast.IsWeakSolutionOn
      (fun x => (toHighContrast hK a).1 x) Set.univ (fun x => e + dilatedGradient g x) := by
  intro χ hχ
  let χ' : Vec d → ℝ := fun y => χ ((2 : ℝ)⁻¹ • y)
  have hχ'smooth : ContDiff ℝ (⊤ : ℕ∞) χ' := hχ.contDiff.comp (contDiff_const_smul _)
  have hχ'cs : HasCompactSupport χ' := hχ.hasCompactSupport.comp_smul (inv_ne_zero two_ne_zero)
  have hdiff : Differentiable ℝ χ := hχ.contDiff.differentiable (by simp)
  let F : Vec d → Vec d := fun y => (a y).mulVec (e + g y)
  let J : Vec d → ℝ := fun y =>
    _root_.Homogenization.vecDot (_root_.Homogenization.HighContrast.smoothGrad χ ((2 : ℝ)⁻¹ • y))
      (F y)
  have hJ : J = fun y => (2 : ℝ) * dot (F y) (gradient χ' y) := by
    funext y
    simp only [J, smoothGrad_comp_inv_two_smul hdiff y, _root_.Homogenization.vecDot, dot,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hgradcont : Continuous (gradient χ') := by
    refine continuous_pi fun i => ?_
    exact (hχ'smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradcs (i : Fin d) : HasCompactSupport (fun y => gradient χ' y i) := by
    have : HasCompactSupport (fderiv ℝ χ') := hχ'cs.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector i)) (by simp)
  have hJint : Integrable J := by
    rw [hJ]
    refine Integrable.const_mul ?_ _
    simp only [dot]
    refine integrable_finsetSum _ fun i _ => ?_
    have hloc : LocallyIntegrable (fun y => F y i) volume :=
      locallyIntegrableOn_univ.mp (hharm.1 i)
    simpa [smul_eq_mul, mul_comm] using
      hloc.integrable_smul_left_of_hasCompactSupport
        ((continuous_apply i).comp hgradcont) (hgradcs i)
  have hcongr : (fun x => _root_.Homogenization.vecDot
      (_root_.Homogenization.HighContrast.smoothGrad χ x)
      (_root_.Homogenization.matVecMul ((toHighContrast hK a).1 x)
        (e + dilatedGradient g x))) =ᵐ[volume] fun x => J ((2 : ℝ) • x) := by
    filter_upwards [toHighContrast_ae_eq hK a] with x hx
    have hx2 : (2 : ℝ)⁻¹ • (2 : ℝ) • x = x := inv_smul_smul₀ (two_ne_zero' ℝ) x
    simp only [J, F, hx, dilatedGradient, hx2]
    congr 1
  have hint : Integrable (fun x => J ((2 : ℝ) • x)) := hJint.comp_smul two_ne_zero
  refine ⟨?_, ?_⟩
  · exact integrableOn_univ.mpr (hint.congr hcongr.symm)
  · rw [setIntegral_univ, integral_congr_ae hcongr, Measure.integral_comp_smul, hJ,
      integral_const_mul]
    have hzero := hharm.2.2 χ' ⟨hχ'smooth, hχ'cs, Set.subset_univ _⟩
    rw [setIntegral_univ, setIntegral_univ] at hzero
    simp only [zero_mul, integral_zero, neg_zero] at hzero
    rw [hzero]
    simp

end EinsteinFull.Homogenization
