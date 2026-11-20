import EinsteinFull.Homogenization.CorrectorEnergyIteration
import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
import PDEFoundation.PDE.CoefficientL2
import EinsteinFull.Homogenization.SmoothGradBounds

/-!
# Testing whole-space solutions with cutoffs of Sobolev functions

A whole-space solution of a divergence-form equation with a pointwise elliptic coefficient may
be tested against `η² (u - k)` for every function `u` that is locally in `H¹` and every smooth
cutoff `η`. For `u` the corrector this is the identity
`∫ η² ∇φ · a ∇v = -2 ∫ η (φ - k) ∇η · a ∇v`, obtained from the `H¹₀` testing of the elliptic
regularity library of Armstrong, Kuusi and Loher.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem volume_euclideanBall_lt_top (R : ℝ) : volume (euclideanBall d R) < ⊤ := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * |R|) (by norm_num : (1 : ℝ) < 3)
  have hsub : euclideanBall d R ⊆ euclideanBall d |R| := by
    intro x hx
    have hx' : vecNormSq (x - 0) < R ^ 2 := hx
    show vecNormSq (x - 0) < |R| ^ 2
    rwa [sq_abs]
  have hsub2 : euclideanBall d |R| ⊆ cubeSet (originCube d (N : ℤ)) :=
    euclideanBall_subset_cubeSet_originCube (abs_nonneg R) (by linarith)
  exact (measure_mono (hsub.trans hsub2)).trans_lt (volume_cubeSet_lt_top _)

namespace EllipticWholeSpaceSolution

variable {K : ℝ} (s : EllipticWholeSpaceSolution d K)

theorem memLp_euclideanBall_vecDot (e : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    MemLp (fun x => vecDot e x) 2 (volume.restrict (euclideanBall d R)) := by
  have : IsFiniteMeasure (volume.restrict (euclideanBall d R)) :=
    isFiniteMeasure_restrict.mpr (volume_euclideanBall_lt_top R).ne
  refine MemLp.of_bound (contDiff_vecDot_left e).continuous.aestronglyMeasurable
    (Real.sqrt (vecNormSq e) * R) ?_
  refine ae_restrict_of_forall_mem (HighContrast.isOpen_euclideanBall d R).measurableSet
    fun x hx => ?_
  rw [Real.norm_eq_abs]
  have hx' : vecNormSq (x - 0) < R ^ 2 := hx
  rw [sub_zero] at hx'
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq e x
  have hxR : Real.sqrt (vecNormSq x) ≤ R := by
    rw [Real.sqrt_le_left hR]
    exact hx'.le
  calc |vecDot e x| = Real.sqrt (vecDot e x ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecNormSq e * vecNormSq x) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (vecNormSq e) * Real.sqrt (vecNormSq x) :=
        Real.sqrt_mul (vecNormSq_nonneg e) _
    _ ≤ Real.sqrt (vecNormSq e) * R := mul_le_mul_of_nonneg_left hxR (Real.sqrt_nonneg _)

/-- **Testing with a cutoff of the corrector.** For a smooth cutoff `η` supported in a ball,
`∫ η² ∇φ · a ∇v = -2 ∫ η (φ - k) ∇η · a ∇v`. -/
theorem integral_cutoff_sq_correctorGrad [NeZero d] (e : Vec d) {R : ℝ} (hR : 0 < R)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcs : HasCompactSupport η)
    (hηR : tsupport η ⊆ euclideanBall d R) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    {M : ℝ} (hM : ∀ x, ‖fderiv ℝ η x‖ ≤ M) (k : ℝ) :
    ∫ x, η x ^ 2 * vecDot (s.correctorGrad e x) (matVecMul (s.coeff x) (s.Dv x)) =
      -(2 * ∫ x, η x * (s.corrector e x - k) *
        vecDot (smoothGrad η x) (matVecMul (s.coeff x) (s.Dv x))) := by
  set U : Set (Vec d) := euclideanBall d R with hUdef
  have hUopen : IsOpen U := HighContrast.isOpen_euclideanBall d R
  have hU : PDE.IsOpenBoundedConvexDomain U :=
    PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR
  have hUfin : volume U < ⊤ := volume_euclideanBall_lt_top R
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUfin.ne
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hwv : HasWeakGradientOn U s.v s.Dv := s.weak.restrict hUopen (Set.subset_univ _)
  have hwΦ : HasWeakGradientOn U (s.corrector e) (s.correctorGrad e) :=
    (s.hasWeakGradientOn_corrector e).restrict hUopen (Set.subset_univ _)
  let uv : PDE.H1Function U :=
    { toFun := s.v
      grad := s.Dv
      memL2 := (s.locL2 R hR).1
      gradMemL2 := (s.locL2 R hR).2
      hasWeakGradient := fun i φ h1 h2 h3 => hwv i φ h1 h2 h3 }
  have hΦL2 : MemLp (s.corrector e) 2 (volume.restrict U) :=
    (s.locL2 R hR).1.sub (memLp_euclideanBall_vecDot e hR.le)
  let uΦ : PDE.H1Function U :=
    { toFun := s.corrector e
      grad := s.correctorGrad e
      memL2 := hΦL2
      gradMemL2 := fun i => ((s.locL2 R hR).2 i).sub (memLp_const (e i))
      hasWeakGradient := fun i φ h1 h2 h3 => hwΦ i φ h1 h2 h3 }
  have hmeasf (i j : Fin d) : Measurable (fun x => s.coeff x i j) :=
    (measurable_pi_iff.mp (measurable_pi_iff.mp s.measurable_coeff i)) j
  have hEll : PDE.IsEllipticFieldOn 1 K U s.coeff := by
    refine ⟨?_, fun x _ => s.elliptic x⟩
    classical
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact Measurable.ite hUopen.measurableSet (hmeasf i j) measurable_const
  have hsolP : PDE.IsWeakDivergenceFormHarmonicOn s.coeff U uv := by
    intro φ
    obtain ⟨hint, hzero⟩ := s.solution φ.toFun ⟨φ.contDiff, φ.hasCompactSupport,
      Set.subset_univ _⟩
    have hpt (x : Vec d) : PDE.vecDot (PDE.matVecMul (s.coeff x) (uv.grad x)) (φ.grad x) =
        vecDot (smoothGrad φ.toFun x) (matVecMul (s.coeff x) (s.Dv x)) := by
      change vecDot (matVecMul (s.coeff x) (s.Dv x)) (smoothGrad φ.toFun x) = _
      exact vecDot_comm _ _
    have hsupp : ∀ x ∉ U, vecDot (smoothGrad φ.toFun x) (matVecMul (s.coeff x) (s.Dv x)) = 0 := by
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
    have hfun : (fun x => PDE.vecDot (PDE.matVecMul (s.coeff x) (uv.grad x)) (φ.grad x)) =
        fun x => vecDot (smoothGrad φ.toFun x) (matVecMul (s.coeff x) (s.Dv x)) := funext hpt
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hfun]
      exact hint.mono_set (Set.subset_univ _)
    · simp
    · simp [PDE.vecDot]
    · rw [hfun, setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      simp only [Measure.restrict_univ] at hzero
      rw [hzero]
      simp [PDE.vecDot]
  have hgradbd (x : Vec d) : PDE.vecEuclideanNorm (PDE.classicalGradient η x) ≤
      Real.sqrt d * M := by
    have h1 := vecNormSq_smoothGrad_le η x
    have h2 : ‖fderiv ℝ η x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM x) 2
    change Real.sqrt (vecNormSq (smoothGrad η x)) ≤ _
    rw [show Real.sqrt d * M = Real.sqrt (d * M ^ 2) by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hM0]]
    exact Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)))
  let ηP : PDE.QuantitativeSmoothCutoff (∅ : Set (Vec d)) U (Real.sqrt d * M) :=
    { toFun := η
      smooth := hη
      hasCompactSupport := hcs
      tsupport_subset := hηR
      nonneg := hη0
      le_one := hη1
      eq_one_on_inner := fun x hx => absurd hx (Set.notMem_empty x)
      gradient_bound := hgradbd }
  let φ := PDE.H1Function.mulCutoffSqSubConstToH10 hU uΦ k ηP subset_rfl
  have htest := ((hsolP.toH10SolutionOn hEll) φ).2
  have hφgrad := PDE.H1Function.mulCutoffSqSubConstToH10_grad hU uΦ k ηP
    (subset_rfl : U ⊆ U)
  set X : Vec d → Vec d := fun x => matVecMul (s.coeff x) (s.Dv x) with hXdef
  set A : Vec d → ℝ := fun x => η x ^ 2 * vecDot (s.correctorGrad e x) (X x) with hAdef
  set B : Vec d → ℝ := fun x => η x * (s.corrector e x - k) * vecDot (smoothGrad η x) (X x)
    with hBdef
  have hpt (x : Vec d) : PDE.vecDot (PDE.matVecMul (s.coeff x) (uv.grad x))
      (φ.toH1Function.grad x) = A x + 2 * B x := by
    rw [hφgrad]
    change vecDot (matVecMul (s.coeff x) (s.Dv x)) (η x ^ 2 • s.correctorGrad e x +
      (2 * η x * (s.corrector e x - k)) • smoothGrad η x) = _
    simp only [hAdef, hBdef, hXdef, vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero : ∫ x in U, (A x + 2 * B x) = 0 := by
    have h := htest
    simp only [hpt] at h
    rw [h]
    simp [PDE.vecDot]
  have hX : PDE.MemVectorL2On U X :=
    PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll uv.gradMemL2
  have hηc : Continuous η := hη.continuous
  have hdηc (i : Fin d) : Continuous (fun x => smoothGrad η x i) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hAint : IntegrableOn A U volume := by
    have h1 : IntegrableOn (fun x => vecDot (s.correctorGrad e x) (X x)) U volume := by
      have := PDE.integrableOn_vecDot_of_memVectorL2On uΦ.gradMemL2 hX
      exact this
    refine (h1.bdd_mul (c := 1) (hηc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hη0 x
    have := hη1 x
    nlinarith
  have hY : MemLp (fun x => η x * vecDot (smoothGrad η x) (X x)) 2 (volume.restrict U) := by
    have hsum : (fun x => η x * vecDot (smoothGrad η x) (X x)) =
        fun x => ∑ j, (η x * smoothGrad η x j) * X x j := by
      funext x
      simp only [vecDot, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
    refine memLp_finsetSum (f := fun j x => (η x * smoothGrad η x j) * X x j) Finset.univ
      fun j _ => ?_
    have hb : MemLp (fun x => η x * smoothGrad η x j) ⊤ (volume.restrict U) := by
      refine memLp_top_of_bound ((hηc.mul (hdηc j)).aestronglyMeasurable) M
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |η x| ≤ 1 := abs_le.mpr ⟨by linarith [hη0 x], hη1 x⟩
      have h2 : |smoothGrad η x j| ≤ M := (abs_fderiv_apply_basisVec_le η x j).trans (hM x)
      calc |η x| * |smoothGrad η x j| ≤ 1 * M :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    exact hb.fun_mul (hX j)
  have hBint : IntegrableOn B U volume := by
    have hΦk : MemLp (fun x => s.corrector e x - k) 2 (volume.restrict U) :=
      hΦL2.sub (memLp_const k)
    have h := hΦk.integrable_mul hY
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hBdef, Pi.mul_apply]
    ring
  have hsplit : ∫ x in U, A x = -(2 * ∫ x in U, B x) := by
    rw [integral_add hAint (hBint.const_mul 2), integral_const_mul] at hzero
    linarith
  have hAU : ∫ x in U, A x = ∫ x, A x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hηR h)
    simp [hAdef, hx']
  have hBU : ∫ x in U, B x = ∫ x, B x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hηR h)
    simp [hBdef, hx']
  rw [hAU, hBU] at hsplit
  exact hsplit

end EllipticWholeSpaceSolution

end EinsteinFull.Homogenization
