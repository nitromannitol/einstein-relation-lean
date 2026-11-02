import SubdiffusiveProcess.Gluing.Truncation
import EinsteinFull.Calculus.C16TubeNativeInitialEnergy
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat

open scoped NNReal ENNReal

namespace EinsteinFull.Calculus

open EinsteinRelation MeasureTheory Filter External.Source.GMP Blueprint.TubeProbability

/-- The scalar multiplier for the initial heat-semigroup difference. -/
theorem c16_heat_multiplier_sq_le (a : ℝ) (ha : 0 ≤ a) :
    (1 - Real.exp (-a)) ^ 2 ≤ a := by
  have hp : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hu : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hl : 1 - a ≤ Real.exp (-a) := by
    have h := Real.add_one_le_exp (-a)
    linarith
  nlinarith

/-- The finite spectral difference is bounded by the corresponding finite
Dirichlet energy. -/
theorem c16_finite_spectral_trace_bound (ell c : ℕ → ℝ)
    (hell : ∀ n, 0 ≤ ell n) (t : ℝ) (ht : 0 ≤ t) (I : Finset ℕ) :
    (∑ n ∈ I, (1 - Real.exp (-(ell n) * t)) ^ 2 * (c n) ^ 2) ≤
      t * ∑ n ∈ I, ell n * (c n) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have h := c16_heat_multiplier_sq_le (ell n * t) (mul_nonneg (hell n) ht)
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (c n))
  simpa only [neg_mul] using (show (1 - Real.exp (-(ell n * t))) ^ 2 * (c n) ^ 2 ≤
    t * (ell n * (c n) ^ 2) by nlinarith)

/-- The finite-mode trace bound uses the actual source spectral coefficients. -/
theorem c16_dirichlet_finite_spectral_trace_bound {d : ℕ}
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R : ℝ} (s : External.Source.GMP.DirichletSpectralResolution ρ α R)
    (φ : EinsteinRelation.Vec d → ℝ) (t : ℝ) (ht : 0 ≤ t) (I : Finset ℕ) :
    let a := fun n => ∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
      ρ x * s.eigenfunction n x * φ x
    (∑ n ∈ I, (1 - Real.exp (-(s.eigenvalue n) * t)) ^ 2 * (a n) ^ 2) ≤
      t * ∑ n ∈ I, s.eigenvalue n * (a n) ^ 2 := by
  exact c16_finite_spectral_trace_bound s.eigenvalue _
    (fun n => (s.eigenvalue_pos n).le) t ht I

/-- The squared initial-trace coefficients are summable for any datum in
an orthonormal spectral family. -/
theorem c16_spectral_trace_coefficients_summable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {v : ℕ → H} (hv : Orthonormal ℝ v) (ell : ℕ → ℝ)
    (hell : ∀ n, 0 ≤ ell n) (f : H) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun n => (1 - Real.exp (-(ell n) * t)) ^ 2 *
      (inner ℝ (v n) f) ^ 2) := by
  have hs : Summable (fun n => (inner ℝ (v n) f) ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hv.inner_products_summable f
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ hs
  intro n
  have hp : 0 ≤ Real.exp (-(ell n) * t) := (Real.exp_pos _).le
  have hu : Real.exp (-(ell n) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hell n)) ht)
  have hm : (1 - Real.exp (-(ell n) * t)) ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg (inner ℝ (v n) f))]

/-- The actual weighted Fourier coefficients of a spatial test give a
summable initial-trace series. -/
theorem c16_dirichlet_trace_coefficients_summable {d : ℕ}
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (s : External.Source.GMP.DirichletSpectralResolution ρ α R)
    (φ : EinsteinRelation.Vec d → ℝ)
    (hφ : EinsteinRelation.IsSpatialTest (External.Source.GMP.sourceBall 0 R) φ)
    (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun n => (1 - Real.exp (-(s.eigenvalue n) * t)) ^ 2 *
      (∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        ρ x * s.eigenfunction n x * φ x) ^ 2) := by
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hc (n : ℕ) : inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n)) (hp.toLp φ) =
      ∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        ρ x * s.eigenfunction n x * φ x :=
    Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native hκ hell R _ _ _ _
      (s.square_integrable n).coeFn_toLp hp.coeFn_toLp
  simpa only [hc] using c16_spectral_trace_coefficients_summable s.orthonormal
    s.eigenvalue (fun n => (s.eigenvalue_pos n).le) (hp.toLp φ) t ht

/-- Parseval identifies the squared spectral heat trace with its mode series. -/
@[nolint unusedArguments]
theorem c16_spectral_heat_trace_parseval {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (b : HilbertBasis ℕ ℝ H)
    (ell : ℕ → ℝ) (hell : ∀ n, 0 ≤ ell n) (f : H) (t : ℝ≥0) :
    ‖Blueprint.TubeProbability.SpectralHeat.heatOperator b ell hell t f - f‖ ^ 2 =
      ∑' n, (1 - Real.exp (-(ell n) * (t : ℝ))) ^ 2 * (b.repr f n) ^ 2 := by
  calc
    _ = ‖b.repr (Blueprint.TubeProbability.SpectralHeat.heatOperator b ell hell t f - f)‖ ^ 2 := by
      rw [b.repr.norm_map]
    _ = ∑' n, ‖b.repr (Blueprint.TubeProbability.SpectralHeat.heatOperator b ell hell t f - f) n‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
          (b.repr (Blueprint.TubeProbability.SpectralHeat.heatOperator b ell hell t f - f))
    _ = _ := by
      apply tsum_congr
      intro n
      rw [map_sub]
      change ‖b.repr (Blueprint.TubeProbability.SpectralHeat.heatOperator b ell hell t f) n - b.repr f n‖ ^ 2 = _
      rw [Blueprint.TubeProbability.SpectralHeat.heatOperator_repr, Real.norm_eq_abs, sq_abs]
      ring

/-- Parseval for the supplied Dirichlet spectrum and a native spatial test. -/
theorem c16_dirichlet_heat_trace_parseval {d : ℕ}
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {R κ : ℝ} (hR : 0 < R) (hκ : 0 < κ)
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (s : External.Source.GMP.DirichletSpectralResolution ρ α R)
    (φ : EinsteinRelation.Vec d → ℝ)
    (hφ : EinsteinRelation.IsSpatialTest (External.Source.GMP.sourceBall 0 R) φ)
    (t : ℝ≥0) :
    let b := HilbertBasis.mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    ‖Blueprint.TubeProbability.SpectralHeat.heatOperator b s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) - hp.toLp φ‖ ^ 2 =
    ∑' n, (1 - Real.exp (-(s.eigenvalue n) * (t : ℝ))) ^ 2 *
      (∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        ρ x * s.eigenfunction n x * φ x) ^ 2 := by
  dsimp only
  let b := HilbertBasis.mk s.orthonormal
    (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hb (n : ℕ) : b n = (s.square_integrable n).toLp (s.eigenfunction n) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
  have hc (n : ℕ) : b.repr (hp.toLp φ) n =
      ∫ x in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        ρ x * s.eigenfunction n x * φ x := by
    rw [b.repr_apply_apply, hb]
    exact Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native hκ hell R _ _ _ _
      (s.square_integrable n).coeFn_toLp hp.coeFn_toLp
  simpa only [hc] using c16_spectral_heat_trace_parseval b s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) (hp.toLp φ) t

/-- For the supplied kernel, spectral heat flow acts by the literal native
kernel convolution in the weighted space. -/
theorem c16_supplied_kernel_heat_action {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (K : ℝ → EinsteinRelation.Vec d → EinsteinRelation.Vec d → ℝ)
    (G : ℝ → EinsteinRelation.Vec d → EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hK : External.Source.GMP.IsSpectralDirichletFundamentalSolution ρ α R K G)
    (φ : EinsteinRelation.Vec d → ℝ)
    (hφ : EinsteinRelation.IsSpatialTest (External.Source.GMP.sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∃ s : External.Source.GMP.DirichletSpectralResolution ρ α R,
      let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      (fun x => Blueprint.TubeProbability.SpectralHeat.heatOperator
        (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) x) =ᵐ[External.Source.GMP.dirichletVolume ρ R]
      fun x => ∫ y in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        K t x y * φ y := by
  obtain ⟨s, hs⟩ := hK.2
  refine ⟨s, ?_⟩
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hB : MeasurableSet (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R) :=
    (Blueprint.TubeProbability.dirichletBall (d := d) R).isOpen.measurableSet
  have hxball : ∀ᵐ x ∂External.Source.GMP.dirichletVolume ρ R,
      x ∈ External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R :=
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le (MeasureTheory.ae_restrict_mem hB)
  filter_upwards [Blueprint.SbxS3UniformCrossHeat.spectral_heat_operator_ae_kernel_action
    hd hκ hell hR s t ht (hp.toLp φ), hxball] with x hx hxb
  rw [hx]
  have hi : (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * (hp.toLp φ) y
      ∂External.Source.GMP.dirichletVolume ρ R) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y
        ∂External.Source.GMP.dirichletVolume ρ R := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [hi]
  change (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
    s.eigenfunction n x * s.eigenfunction n y) * φ y ∂(MeasureTheory.volume.restrict
      (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)).withDensity
      (fun y => ENNReal.ofReal (ρ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (MeasureTheory.ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hB] with y hy
  simp only [ENNReal.toReal_ofReal (hκ.le.trans (hell.2.2 y).1), smul_eq_mul,
    (hs (t : ℝ) ht x hxb y hy).2]
  ring

/-- Each supplied eigenmode is an H¹ function with its supplied weak gradient. -/
theorem c16_supplied_eigenfunction_H1 {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (s : External.Source.GMP.DirichletSpectralResolution ρ α R) (n : ℕ) :
    ∃ w : Homogenization.H1Function (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R),
      w.toFun = s.eigenfunction n ∧ w.grad = s.gradient n := by
  refine ⟨{ toFun := s.eigenfunction n
            grad := s.gradient n
            memL2 := Blueprint.SbxS3UniformCrossHeat.spectral_eigenfunction_memLp_sourceBall hκ hell s n
            gradMemL2 := Blueprint.SbxS3UniformCrossHeat.spectral_gradient_coordinate_memLp s n
            hasWeakGradient := Blueprint.TubeProbability.hasWeakGradientOn_of_source
              (Blueprint.SbxS3UniformCrossHeat.spectral_eigenfunction_weakGradient s n) }, rfl, rfl⟩

/-- Supplied eigenmodes have zero Sobolev boundary trace. -/
theorem c16_supplied_eigenfunction_memH10 {d : ℕ} {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (s : External.Source.GMP.DirichletSpectralResolution ρ α R) (n : ℕ) :
    Homogenization.MemH10 (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)
      ((closure (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)).indicator
        (s.eigenfunction n)) := by
  classical
  let U := External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R
  obtain ⟨w, hw, hg⟩ := c16_supplied_eigenfunction_H1 hκ hell s n
  have hdomain : Homogenization.IsOpenBoundedConvexDomain U := by
    have h := PDE.isOpenBoundedConvexDomain_euclideanBall (0 : EinsteinRelation.Vec d) hR
    rw [Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall _ hR] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hae : (closure U).indicator (s.eigenfunction n) =ᵐ[MeasureTheory.volume.restrict U]
      w.toFun := by
    filter_upwards [MeasureTheory.ae_restrict_mem hdomain.1.measurableSet] with x hx
    rw [Set.indicator_of_mem (subset_closure hx), hw]
  let v : Homogenization.H1Function U := {
    toFun := (closure U).indicator (s.eigenfunction n)
    grad := w.grad
    memL2 := w.memL2.ae_eq hae.symm
    gradMemL2 := w.gradMemL2
    hasWeakGradient := by
      intro i φ hφ hφc hφs
      have h1 : ∫ x in U, (closure U).indicator (s.eigenfunction n) x *
          (fderiv ℝ φ x) (Homogenization.basisVec i) =
          ∫ x in U, w.toFun x * (fderiv ℝ φ x) (Homogenization.basisVec i) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hae] with x hx
        rw [hx]
      rw [h1]
      exact w.hasWeakPartialDerivOn i φ hφ hφc hφs }
  apply SubdiffusiveProcess.Gluing.memH10_of_continuousOn_zero_frontier hdomain v
  · apply (s.continuous n).congr
    intro x hx
    change (closure U).indicator (s.eigenfunction n) x = s.eigenfunction n x
    exact Set.indicator_of_mem hx _
  · intro x hx
    rw [show v.toFun = (closure U).indicator (s.eigenfunction n) from rfl,
      Set.indicator_of_mem hx.1, s.boundary_zero n x hx]
  · intro x hx
    exact Set.indicator_of_notMem hx _

/-- The zero-trace representative has the supplied gradient almost everywhere. -/
theorem c16_supplied_eigenfunction_H10 {d : ℕ} {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (s : External.Source.GMP.DirichletSpectralResolution ρ α R) (n : ℕ) :
    ∃ v : Homogenization.H10Function (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R),
      v.toH1Function.toFun = (closure (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)).indicator (s.eigenfunction n) ∧
      v.toH1Function.grad =ᵐ[MeasureTheory.volume.restrict
        (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)] s.gradient n := by
  classical
  let U := External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R
  obtain ⟨w, hw, hg⟩ := c16_supplied_eigenfunction_H1 hκ hell s n
  have hdomain : Homogenization.IsOpenBoundedConvexDomain U := by
    have h := PDE.isOpenBoundedConvexDomain_euclideanBall (0 : EinsteinRelation.Vec d) hR
    rw [Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall _ hR] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
  have hae : (closure U).indicator (s.eigenfunction n) =ᵐ[MeasureTheory.volume.restrict U]
      w.toFun := by
    filter_upwards [MeasureTheory.ae_restrict_mem hdomain.1.measurableSet] with x hx
    rw [Set.indicator_of_mem (subset_closure hx), hw]
  let z : Homogenization.H1Function U := {
    toFun := (closure U).indicator (s.eigenfunction n)
    grad := w.grad
    memL2 := w.memL2.ae_eq hae.symm
    gradMemL2 := w.gradMemL2
    hasWeakGradient := by
      intro i φ hφ hφc hφs
      have h1 : ∫ x in U, (closure U).indicator (s.eigenfunction n) x *
          (fderiv ℝ φ x) (Homogenization.basisVec i) =
          ∫ x in U, w.toFun x * (fderiv ℝ φ x) (Homogenization.basisVec i) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hae] with x hx
        rw [hx]
      rw [h1]
      exact w.hasWeakPartialDerivOn i φ hφ hφc hφs }
  obtain ⟨v, hv⟩ := c16_supplied_eigenfunction_memH10 hκ hR hell s n
  refine ⟨v, hv, ?_⟩
  have heq : v.toH1Function.toFun = z.toFun := hv
  have hgrad := Blueprint.TubeProbability.DimensionLift.h1Function_grad_ae_eq_of_toFun_eq
    hdomain.1 v.toH1Function z heq
  simpa only [z, hg] using hgrad

/-- Each supplied mode satisfies its eigenvalue equation against every
completed Dirichlet test. -/
theorem c16_supplied_eigenfunction_dirichletEquation {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (n : ℕ) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) u : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] s.eigenfunction n ∧
      ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x)) =
        s.eigenvalue n * inner ℝ
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) u)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w) := by
  classical
  obtain ⟨v, hv, hg⟩ := c16_supplied_eigenfunction_H10 hκ hR hell s n
  have hweak : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      s.eigenvalue n * ∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * φ x := by
    intro φ
    have ht : IsSpatialTest (sourceBall (0 : Vec d) R) (φ : Vec d → ℝ) :=
      ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
    have he := s.eigenfunction_equation n φ ht
    have hleft : (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
        ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (s.gradient n x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i)) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    have hright : (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * φ x) =
        ∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
      rw [hv, Set.indicator_of_mem (subset_closure hx)]
    rw [hleft, hright]
    exact he
  obtain ⟨u, hu, hueq⟩ := exists_dirichletHilbert_weakEquation_of_native_smooth
    hd hκ hell R hR v (s.eigenvalue n) hweak
  refine ⟨u, ?_, hueq⟩
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [hu, hac.ae_le (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)] with x hx hxU
  rw [hx, hv, Set.indicator_of_mem (subset_closure hxU)]

/-- Orthogonal modes in a nonnegative symmetric energy obey a finite
Bessel inequality. -/
theorem c16_energy_orthogonal_finite_bound {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x) (u : ℕ → H) (ell c : ℕ → ℝ) (v : H)
    (hpair : ∀ n, B (u n) v = ell n * c n)
    (horth : ∀ n m, B (u n) (u m) = if n = m then ell n else 0)
    (I : Finset ℕ) : (∑ n ∈ I, ell n * c n ^ 2) ≤ B v v := by
  classical
  let z : H := ∑ n ∈ I, c n • u n
  have hzv : B z v = ∑ n ∈ I, ell n * c n ^ 2 := by
    simp only [z, map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hpair]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hzz : B z z = ∑ n ∈ I, ell n * c n ^ 2 := by
    simp only [z, map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, horth]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', mul_assoc]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [hn, if_true]
    ring
  have hp := hpos (v - z)
  simp only [map_sub, ContinuousLinearMap.sub_apply] at hp
  rw [hsym v z, hzv, hzz] at hp
  linarith

/-- The supplied modes satisfy the finite Dirichlet-energy Bessel bound. -/
theorem c16_supplied_modes_finite_energy {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (v : DirichletHilbertSpace (d := d) R hR) (I : Finset ℕ) :
    (∑ n ∈ I, s.eigenvalue n * (inner ℝ
      ((s.square_integrable n).toLp (s.eigenfunction n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) v)) ^ 2) ≤
    ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => v.val (some i) x)) (fun i => v.val (some i) x) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  choose u hu heq using fun n => c16_supplied_eigenfunction_dirichletEquation hd hκ hR hell s n
  have hJu (n : ℕ) : J (u n) = (s.square_integrable n).toLp (s.eigenfunction n) := by
    apply Lp.ext
    exact (hu n).trans ((s.square_integrable n).coeFn_toLp).symm
  obtain ⟨c, hc, B, hB, hform⟩ := exists_dirichletHilbert_energyForm hd hκ hell R hR
  have hsym (a b : DirichletHilbertSpace (d := d) R hR) : B a b = B b a := by
    rw [hform, hform]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    have hs : (α x).IsSymm := (hell.2.2 x).2.2.1
    have hx := hs.dotProduct_mulVec_comm
      (x := fun i => b.val (some i) x) (y := fun i => a.val (some i) x)
    rw [dotProduct_comm, dotProduct_comm (fun i => a.val (some i) x)] at hx
    exact hx
  have hpos (a : DirichletHilbertSpace (d := d) R hR) : 0 ≤ B a a :=
    (mul_nonneg hc.le (sq_nonneg _)).trans (hB a)
  have hp (n : ℕ) : B (u n) v = s.eigenvalue n * inner ℝ (J (u n)) (J v) := by
    rw [hform]
    exact heq n v
  have ho (n m : ℕ) : B (u n) (u m) = if n = m then s.eigenvalue n else 0 := by
    rw [hform, heq n (u m), hJu n, hJu m]
    rw [(orthonormal_iff_ite.mp s.orthonormal) n m]
    split_ifs <;> simp
  have hb := c16_energy_orthogonal_finite_bound B hsym hpos u s.eigenvalue
    (fun n => inner ℝ (J (u n)) (J v)) v hp ho I
  simpa only [hJu, hform, J] using hb

/-- The supplied spectral coefficients of a smooth test are bounded by its
actual source Dirichlet energy. -/
theorem c16_spatial_test_finite_dirichlet_energy {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (φ : Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall (0 : Vec d) R) φ) (I : Finset ℕ) :
    (∑ n ∈ I, s.eigenvalue n *
      (∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x) ^ 2) ≤
    ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
        (fun i => fderiv ℝ φ x (unitVector i)) := by
  let ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
  let v := dirichletSmoothElement R hR ψ
  have hp (n : ℕ) : inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) v) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x := by
    rw [dirichletHilbertInclusion_inner_smooth hκ hell R hR]
    apply integral_congr_ae
    have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
      apply withDensity_absolutelyContinuous' hell.1.ennreal_ofReal.aemeasurable
      exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (hell.2.2 x).1)).ne'
    filter_upwards [hac.ae_le (s.square_integrable n).coeFn_toLp] with x hx
    rw [hx]
    rfl
  have hg : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), ∀ i : Fin d,
      v.val (some i) x = fderiv ℝ φ x (unitVector i) := by
    apply ae_all_iff.mpr
    intro i
    have ht := (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono_set volume (sourceBall_subset_cube R hR))).ae_le
        (SubdiffusiveProcess.testPartialL2_coeFn (dirichletTestInCube R hR ψ) i)
    exact ht
  have he : (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => v.val (some i) x)) (fun i => v.val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
        (fun i => fderiv ℝ φ x (unitVector i)) := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [funext hx]
  simpa only [hp, he] using c16_supplied_modes_finite_energy hd hκ hR hell s v I

/-- Quantitative initial trace for the supplied kernel in the dimensions
used by the cutoff argument. -/
theorem c16_native_cutoff_quantitative_L2_trace_of_two_le {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ) (t : ℝ) (ht : 0 < t) :
    (∫ x in sourceBall 0 R, ρ x * ((∫ y in sourceBall 0 R, K t x y * φ y)-φ x)^2) ≤
    t * ∫ x in sourceBall 0 R, dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
      (fun i => fderiv ℝ φ x (unitVector i)) := by
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have hτ : (τ : ℝ) = t := rfl
  obtain ⟨s, haction⟩ := c16_supplied_kernel_heat_action hd hκ hR hell K G hK φ hφ τ ht
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let b := Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s
  let f := Blueprint.TubeProbability.SpectralHeat.heatOperator b s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) τ (hp.toLp φ)
  let a := fun n => ∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x
  have hbound : (∑' n, (1 - Real.exp (-s.eigenvalue n * t)) ^ 2 * (a n) ^ 2) ≤
      t * ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
          (fun i => fderiv ℝ φ x (unitVector i)) := by
    apply Real.tsum_le_of_sum_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    intro I
    calc
      _ ≤ t * ∑ n ∈ I, s.eigenvalue n * (a n) ^ 2 :=
        c16_dirichlet_finite_spectral_trace_bound s φ t ht.le I
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (c16_spatial_test_finite_dirichlet_energy hd hκ hR hell s φ hφ I) ht.le
  have hparse : ‖f - hp.toLp φ‖ ^ 2 =
      ∑' n, (1 - Real.exp (-s.eigenvalue n * t)) ^ 2 * (a n) ^ 2 := by
    simpa only [f, b, a, hτ, Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis] using
      c16_dirichlet_heat_trace_parseval hR hκ hell s φ hφ τ
  have hae : ((f - hp.toLp φ : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
      fun x => (∫ y in sourceBall 0 R, K t x y * φ y) - φ x := by
    filter_upwards [Lp.coeFn_sub f (hp.toLp φ), haction, hp.coeFn_toLp] with x hx hy hz
    rw [hx]
    change f x - (hp.toLp φ) x = _
    rw [hy, hz, hτ]
  have hnorm := Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native
    hκ hell R (f - hp.toLp φ) (f - hp.toLp φ) _ _ hae hae
  rw [real_inner_self_eq_norm_sq] at hnorm
  have hnative : (∫ x in sourceBall 0 R, ρ x * ((∫ y in sourceBall 0 R, K t x y * φ y)-φ x)^2) = ‖f - hp.toLp φ‖ ^ 2 := by
    rw [hnorm]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  rw [hnative, hparse]
  exact hbound


/-- A diagonal value of the supplied spectral kernel controls its heat row. -/
theorem c16_supplied_heat_row_coefficients_summable {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    Summable (fun i => (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) ^ 2) := by
  have hsum := hs (2 * t) (by linarith) x hx x hx
  convert hsum using 1
  funext i
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  have he : -s.eigenvalue i * t + -s.eigenvalue i * t =
      -s.eigenvalue i * (2 * t) := by ring
  rw [he]
  ring

/-- The supplied diagonal kernel gives square-summable row coefficients. -/
theorem c16_supplied_heat_row_coefficients_memℓp {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    Memℓp (fun i => Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) 2 := by
  apply memℓp_gen
  convert c16_supplied_heat_row_coefficients_summable s hs t ht x hx using 1
  funext i
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast, Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x)

/-- The supplied diagonal kernel makes each spectral heat row converge in L². -/
theorem c16_supplied_heat_row_Lp_summable {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    Summable (fun i => (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) := by
  have hsum := (s.orthonormal.orthogonalFamily.summable_iff_norm_sq_summable
    (fun i => Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x)).2 ?_
  · simpa only [LinearIsometry.toSpanSingleton_apply] using hsum
  · simpa only [Real.norm_eq_abs, sq_abs] using
      c16_supplied_heat_row_coefficients_summable s hs t ht x hx

/-- The supplied pointwise kernel series represents its L² heat row. -/
theorem c16_supplied_heat_row_Lp_ae_eq {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    (fun y => (∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) y) =ᵐ[dirichletVolume ρ R]
      (fun y => ∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i x * s.eigenfunction i y) := by
  classical
  let f : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hf : Summable f := c16_supplied_heat_row_Lp_summable s hs t ht x hx
  have hlim := hf.tendsto_sum_tsum_nat
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hsum : ∀ᵐ y ∂dirichletVolume ρ R, ∀ n,
      (∑ i ∈ Finset.range n, f i : Lp ℝ 2 (dirichletVolume ρ R)) y =
        ∑ i ∈ Finset.range n, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) f,
      ae_all_iff.mpr (fun i => Lp.coeFn_smul
        (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x)
        ((s.square_integrable i).toLp (s.eigenfunction i))),
      ae_all_iff.mpr (fun i => (s.square_integrable i).coeFn_toLp)] with y hy hsmul hmode
    rw [hy]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsmul i]
    simp only [Pi.smul_apply, smul_eq_mul, hmode i]
  have hball : ∀ᵐ y ∂dirichletVolume ρ R, y ∈ sourceBall 0 R := by
    have hm : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hm)
  filter_upwards [hpoint, hsum, hball] with y hy hys hyball
  have hcross := hs t ht x hx y hyball
  have hp := hcross.tendsto_sum_tsum_nat.comp hns.tendsto_atTop
  apply tendsto_nhds_unique hy
  change Tendsto (fun n => ∑ i ∈ Finset.range (ns n),
    Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y)
    atTop (nhds (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y)) at hp
  simpa only [hys] using hp



theorem c16_supplied_heat_row_basis_coordinate {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) (j : ℕ) :
    (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).repr (∑' i,
      (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) j =
      Real.exp (-s.eigenvalue j * t) * s.eigenfunction j x := by
  classical
  let c : lp (fun _ : ℕ => ℝ) 2 := ⟨_,
    c16_supplied_heat_row_coefficients_memℓp s hspec t ht x hx⟩
  have hb (i : ℕ) : Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s i =
      (s.square_integrable i).toLp (s.eigenfunction i) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) i
  have hs := (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).hasSum_repr_symm c
  have heq : (∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) =
      (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).repr.symm c := by
    simpa only [hb] using hs.tsum_eq
  rw [heq, LinearIsometryEquiv.apply_symm_apply]


theorem c16_supplied_heat_row_action_coordinates {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    (∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) =
    ∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) *
      (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).repr f i := by
  classical
  let row : Lp ℝ 2 (dirichletVolume ρ R) := ∑' i,
    (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hae := c16_supplied_heat_row_Lp_ae_eq s hspec t ht x hx
  calc
    _ = inner ℝ row f := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      change row y = _ at hy
      simp only [RCLike.inner_apply, conj_trivial, hy, mul_comm]
    _ = ∑' i, inner ℝ row (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s i) *
        inner ℝ (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s i) f :=
      ((Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).tsum_inner_mul_inner row f).symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [show inner ℝ row (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s i) =
        inner ℝ (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s i) row from real_inner_comm _ _,
        ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply]
      rw [c16_supplied_heat_row_basis_coordinate s hspec t ht x hx]


theorem c16_supplied_spectral_heat_operator_ae_kernel_action {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    (fun x => SpectralHeat.heatOperator (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t f x) =ᵐ[dirichletVolume ρ R]
    (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) := by
  classical
  let b := Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s
  let F : Lp ℝ 2 (dirichletVolume ρ R) :=
    SpectralHeat.heatOperator b s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f
  let u : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    (Real.exp (-s.eigenvalue i * (t : ℝ)) * b.repr f i) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hb (i : ℕ) : b i = (s.square_integrable i).toLp (s.eigenfunction i) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) i
  have hseries : HasSum u F := by
    have hsum := b.hasSum_repr F
    simpa only [SpectralHeat.heatOperator_repr, hb, u, F] using hsum
  have hlim := hseries.summable.tendsto_sum_tsum_nat
  have heq : ∑' i, u i = F := hseries.tsum_eq
  rw [heq] at hlim
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hsum : ∀ᵐ x ∂dirichletVolume ρ R, ∀ n,
      (∑ i ∈ Finset.range n, u i : Lp ℝ 2 (dirichletVolume ρ R)) x =
        ∑ i ∈ Finset.range n, (Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x) * b.repr f i := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) u,
      ae_all_iff.mpr (fun i => Lp.coeFn_smul
        (Real.exp (-s.eigenvalue i * (t : ℝ)) * b.repr f i)
        ((s.square_integrable i).toLp (s.eigenfunction i))),
      ae_all_iff.mpr (fun i => (s.square_integrable i).coeFn_toLp)] with x hx hsmul hmode
    rw [hx]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsmul i]
    simp only [Pi.smul_apply, smul_eq_mul, hmode i]
    ring
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall 0 R := by
    have hm : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hm)
  filter_upwards [hpoint, hsum, hball] with x hx hxs hxball
  let row : Lp ℝ 2 (dirichletVolume ρ R) := ∑' i,
    (Real.exp (-s.eigenvalue i * (t : ℝ)) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hs : Summable (fun i => (Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i x) * b.repr f i) := by
    have hh := b.summable_inner_mul_inner row f
    convert hh using 1
    funext i
    rw [show inner ℝ row (b i) = inner ℝ (b i) row from real_inner_comm _ _,
      ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply]
    rw [c16_supplied_heat_row_basis_coordinate s hspec (t : ℝ) ht x hxball]
  have hp := hs.tendsto_sum_tsum_nat.comp hns.tendsto_atTop
  have ha := c16_supplied_heat_row_action_coordinates s hspec (t : ℝ) ht x hxball f
  rw [ha]
  apply tendsto_nhds_unique hx
  change Tendsto (fun n => ∑ i ∈ Finset.range (ns n),
    (Real.exp (-s.eigenvalue i * (t : ℝ)) * s.eigenfunction i x) *
      (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).repr f i) atTop
    (nhds (∑' i, (Real.exp (-s.eigenvalue i * (t : ℝ)) * s.eigenfunction i x) *
      (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s).repr f i)) at hp
  simpa only [hxs] using hp


/-- The supplied kernel acts on native tests in every dimension. -/
theorem c16_supplied_kernel_heat_action_all_dimensions {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (K : ℝ → EinsteinRelation.Vec d → EinsteinRelation.Vec d → ℝ)
    (G : ℝ → EinsteinRelation.Vec d → EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hK : External.Source.GMP.IsSpectralDirichletFundamentalSolution ρ α R K G)
    (φ : EinsteinRelation.Vec d → ℝ)
    (hφ : EinsteinRelation.IsSpatialTest (External.Source.GMP.sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∃ s : External.Source.GMP.DirichletSpectralResolution ρ α R,
      let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
      (fun x => Blueprint.TubeProbability.SpectralHeat.heatOperator
        (Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t (hp.toLp φ) x) =ᵐ[External.Source.GMP.dirichletVolume ρ R]
      fun x => ∫ y in External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        K t x y * φ y := by
  obtain ⟨s, hs⟩ := hK.2
  have hsumm : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) :=
    fun t ht x hx y hy => (hs t ht x hx y hy).1
  refine ⟨s, ?_⟩
  dsimp only
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hB : MeasurableSet (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R) :=
    (Blueprint.TubeProbability.dirichletBall (d := d) R).isOpen.measurableSet
  have hxball : ∀ᵐ x ∂External.Source.GMP.dirichletVolume ρ R,
      x ∈ External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R :=
    (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le (MeasureTheory.ae_restrict_mem hB)
  filter_upwards [c16_supplied_spectral_heat_operator_ae_kernel_action
    s hsumm t ht (hp.toLp φ), hxball] with x hx hxb
  rw [hx]
  have hi : (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y) * (hp.toLp φ) y
      ∂External.Source.GMP.dirichletVolume ρ R) =
      ∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y
        ∂External.Source.GMP.dirichletVolume ρ R := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hp.coeFn_toLp] with y hy
    rw [hy]
  rw [hi]
  change (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
    s.eigenfunction n x * s.eigenfunction n y) * φ y ∂(MeasureTheory.volume.restrict
      (External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)).withDensity
      (fun y => ENNReal.ofReal (ρ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (MeasureTheory.ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hB] with y hy
  simp only [ENNReal.toReal_ofReal (hκ.le.trans (hell.2.2 y).1), smul_eq_mul,
    (hs (t : ℝ) ht x hxb y hy).2]
  ring


/-- The native Dirichlet energy extends to a continuous bilinear form in every dimension. -/
theorem c16_exists_dirichletHilbert_energyForm_all_dimensions {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ B : DirichletHilbertSpace (d := d) R hR →L[ℝ]
        DirichletHilbertSpace (d := d) R hR →L[ℝ] ℝ,
      ∀ u v, B u v = ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) := by
  let Q := SubdiffusiveProcess.centeredCube (0 : SubdiffusiveProcess.SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SubdiffusiveProcess.SpatialCoordinates d))
  let a := dirichletValueGradientMatrix (fun _ : Vec d => 0) α
  have ha (i j : Option (Fin d)) : AEStronglyMeasurable (fun x => a x i j) μ := by
    cases i with
    | none => cases j <;> exact aestronglyMeasurable_const
    | some i => cases j with
      | none => exact aestronglyMeasurable_const
      | some j => exact dirichletValueGradientMatrix_aestronglyMeasurable h μ (some i) (some j)
  have hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ κ⁻¹ := by
    apply ae_of_all
    intro x i j
    cases i with
    | none => cases j <;> simpa only [a, dirichletValueGradientMatrix, abs_zero] using inv_nonneg.mpr hκ.le
    | some i => cases j with
      | none => simpa only [a, dirichletValueGradientMatrix, abs_zero] using inv_nonneg.mpr hκ.le
      | some j => exact dirichletValueGradientMatrix_bound hκ h x (some i) (some j)
  obtain ⟨D, hD⟩ := exists_coordinateL2Form μ a ha (inv_nonneg.mpr hκ.le) hb
  let S := (dirichletHilbertSubmodule (d := d) R hR).subtypeL
  let B := D.bilinearComp S S
  refine ⟨B, ?_⟩
  intro u v
  change D u.val v.val = _
  rw [hD]
  have he := integral_congr_ae (μ := μ) (ae_of_all μ fun x =>
      dirichletValueGradientMatrix_sum (fun _ : Vec d => 0) α x
        (fun j => u.val j x) (fun j => v.val j x))
  have hball := dirichletHilbert_integral_eq_ball (fun _ : Vec d => 0) α R hR u v
  simpa only [zero_mul, zero_add] using he.trans hball



theorem c16_dirichletHilbert_weakEquation_of_smooth_all_dimensions {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) (eig : ℝ)
    (hweak : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => (dirichletSmoothElement R hR φ).val (some i) x)) =
      eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u)
        (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) (dirichletSmoothElement R hR φ))) :
    ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => w.val (some i) x)) =
      eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u)
        (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) w) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨B, hform⟩ := c16_exists_dirichletHilbert_energyForm_all_dimensions hκ h R hR
  have hclosed : IsClosed {w : DirichletHilbertSpace (d := d) R hR |
      B u w = eig * inner ℝ (J u) (J w)} :=
    isClosed_eq (B u).continuous ((continuous_const.inner J.continuous).const_mul eig)
  have hsub : Set.range (dirichletSmoothElement (d := d) R hR) ⊆
      {w : DirichletHilbertSpace (d := d) R hR | B u w = eig * inner ℝ (J u) (J w)} := by
    rintro w ⟨φ, rfl⟩
    change B u (dirichletSmoothElement R hR φ) =
      eig * inner ℝ (J u) (J (dirichletSmoothElement R hR φ))
    rw [hform]
    exact hweak φ
  intro w
  rw [← hform]
  exact closure_minimal hsub hclosed (denseRange_dirichletSmoothElement R hR w)


theorem c16_exists_dirichletHilbert_weakEquation_of_native_smooth_all_dimensions {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      eig * ∫ x in sourceBall (0 : Vec d) R, ρ x * v.toH1Function.toFun x * φ x) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x)) =
        eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) u)
          (dirichletHilbertInclusion ρ R hR κ⁻¹
            (fun x _ => (h.2.2 x).2.1) w) := by
  obtain ⟨u, hv, hg⟩ := exists_dirichletHilbert_of_nativeH10_weighted ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) v
  refine ⟨u, hv, c16_dirichletHilbert_weakEquation_of_smooth_all_dimensions hκ h R hR u eig ?_⟩
  intro φ
  rw [dirichletHilbert_energyIntegral_smooth]
  have hgrad : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      (fun i => u.val (some i) x) = v.toH1Function.grad x := by
    filter_upwards [ae_all_iff.mpr hg] with x hx
    exact funext hx
  have he : (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i)) := by
    apply integral_congr_ae
    filter_upwards [hgrad] with x hx
    rw [hx]
  rw [he, hweak φ]
  congr 1
  symm
  rw [L2.inner_def]
  calc
    _ = ∫ x, v.toH1Function.toFun x * φ x ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [hv, dirichletHilbertInclusion_smooth_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) φ] with x hx hy
      simp only [RCLike.inner_apply, conj_trivial, hx, hy]
      exact mul_comm _ _
    _ = _ := by
      change (∫ x, v.toH1Function.toFun x * φ x ∂(volume.restrict
        (sourceBall (0 : Vec d) R)).withDensity (fun x => ENNReal.ofReal (ρ x))) = _
      rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
        ring


theorem c16_supplied_eigenfunction_dirichletEquation_all_dimensions {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (n : ℕ) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) u : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] s.eigenfunction n ∧
      ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x)) =
        s.eigenvalue n * inner ℝ
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) u)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w) := by
  classical
  obtain ⟨v, hv, hg⟩ := c16_supplied_eigenfunction_H10 hκ hR hell s n
  have hweak : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      s.eigenvalue n * ∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * φ x := by
    intro φ
    have ht : IsSpatialTest (sourceBall (0 : Vec d) R) (φ : Vec d → ℝ) :=
      ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
    have he := s.eigenfunction_equation n φ ht
    have hleft : (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
        ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (s.gradient n x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i)) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    have hright : (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * φ x) =
        ∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
      rw [hv, Set.indicator_of_mem (subset_closure hx)]
    rw [hleft, hright]
    exact he
  obtain ⟨u, hu, hueq⟩ := c16_exists_dirichletHilbert_weakEquation_of_native_smooth_all_dimensions
    hκ hell R hR v (s.eigenvalue n) hweak
  refine ⟨u, ?_, hueq⟩
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [hu, hac.ae_le (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)] with x hx hxU
  rw [hx, hv, Set.indicator_of_mem (subset_closure hxU)]



theorem c16_supplied_modes_finite_energy_all_dimensions {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (v : DirichletHilbertSpace (d := d) R hR) (I : Finset ℕ) :
    (∑ n ∈ I, s.eigenvalue n * (inner ℝ
      ((s.square_integrable n).toLp (s.eigenfunction n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) v)) ^ 2) ≤
    ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => v.val (some i) x)) (fun i => v.val (some i) x) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  choose u hu heq using fun n => c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  have hJu (n : ℕ) : J (u n) = (s.square_integrable n).toLp (s.eigenfunction n) := by
    apply Lp.ext
    exact (hu n).trans ((s.square_integrable n).coeFn_toLp).symm
  obtain ⟨B, hform⟩ := c16_exists_dirichletHilbert_energyForm_all_dimensions hκ hell R hR
  have hsym (a b : DirichletHilbertSpace (d := d) R hR) : B a b = B b a := by
    rw [hform, hform]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    have hs : (α x).IsSymm := (hell.2.2 x).2.2.1
    have hx := hs.dotProduct_mulVec_comm
      (x := fun i => b.val (some i) x) (y := fun i => a.val (some i) x)
    rw [dotProduct_comm, dotProduct_comm (fun i => a.val (some i) x)] at hx
    exact hx
  have hpos (a : DirichletHilbertSpace (d := d) R hR) : 0 ≤ B a a := by
    rw [hform]
    apply integral_nonneg
    intro x
    have he := ((hell.2.2 x).2.2.2 (fun i => a.val (some i) x)).1
    change κ * (∑ i : Fin d, a.val (some i) x * a.val (some i) x) ≤
      dotProduct (fun i => a.val (some i) x) ((α x).mulVec (fun i => a.val (some i) x)) at he
    rw [dotProduct_comm] at he
    exact (mul_nonneg hκ.le (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))).trans he
  have hp (n : ℕ) : B (u n) v = s.eigenvalue n * inner ℝ (J (u n)) (J v) := by
    rw [hform]
    exact heq n v
  have ho (n m : ℕ) : B (u n) (u m) = if n = m then s.eigenvalue n else 0 := by
    rw [hform, heq n (u m), hJu n, hJu m]
    rw [(orthonormal_iff_ite.mp s.orthonormal) n m]
    split_ifs <;> simp
  have hb := c16_energy_orthogonal_finite_bound B hsym hpos u s.eigenvalue
    (fun n => inner ℝ (J (u n)) (J v)) v hp ho I
  simpa only [hJu, hform, J] using hb


theorem c16_spatial_test_finite_dirichlet_energy_all_dimensions {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (φ : Vec d → ℝ)
    (hφ : IsSpatialTest (sourceBall (0 : Vec d) R) φ) (I : Finset ℕ) :
    (∑ n ∈ I, s.eigenvalue n *
      (∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x) ^ 2) ≤
    ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
        (fun i => fderiv ℝ φ x (unitVector i)) := by
  let ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
  let v := dirichletSmoothElement R hR ψ
  have hp (n : ℕ) : inner ℝ ((s.square_integrable n).toLp (s.eigenfunction n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) v) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x := by
    rw [dirichletHilbertInclusion_inner_smooth hκ hell R hR]
    apply integral_congr_ae
    have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
      apply withDensity_absolutelyContinuous' hell.1.ennreal_ofReal.aemeasurable
      exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (hell.2.2 x).1)).ne'
    filter_upwards [hac.ae_le (s.square_integrable n).coeFn_toLp] with x hx
    rw [hx]
    rfl
  have hg : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), ∀ i : Fin d,
      v.val (some i) x = fderiv ℝ φ x (unitVector i) := by
    apply ae_all_iff.mpr
    intro i
    have ht := (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono_set volume (sourceBall_subset_cube R hR))).ae_le
        (SubdiffusiveProcess.testPartialL2_coeFn (dirichletTestInCube R hR ψ) i)
    exact ht
  have he : (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => v.val (some i) x)) (fun i => v.val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
        (fun i => fderiv ℝ φ x (unitVector i)) := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [funext hx]
  simpa only [hp, he] using c16_supplied_modes_finite_energy_all_dimensions hκ hR hell s v I


theorem c16_native_cutoff_quantitative_L2_trace {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ) (t : ℝ) (ht : 0 < t) :
    (∫ x in sourceBall 0 R, ρ x * ((∫ y in sourceBall 0 R, K t x y * φ y)-φ x)^2) ≤
    t * ∫ x in sourceBall 0 R, dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
      (fun i => fderiv ℝ φ x (unitVector i)) := by
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have hτ : (τ : ℝ) = t := rfl
  obtain ⟨s, haction⟩ := c16_supplied_kernel_heat_action_all_dimensions hκ hR hell K G hK φ hφ τ ht
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let b := Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s
  let f := Blueprint.TubeProbability.SpectralHeat.heatOperator b s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) τ (hp.toLp φ)
  let a := fun n => ∫ x in sourceBall (0 : Vec d) R, ρ x * s.eigenfunction n x * φ x
  have hbound : (∑' n, (1 - Real.exp (-s.eigenvalue n * t)) ^ 2 * (a n) ^ 2) ≤
      t * ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => fderiv ℝ φ x (unitVector i)))
          (fun i => fderiv ℝ φ x (unitVector i)) := by
    apply Real.tsum_le_of_sum_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    intro I
    calc
      _ ≤ t * ∑ n ∈ I, s.eigenvalue n * (a n) ^ 2 :=
        c16_dirichlet_finite_spectral_trace_bound s φ t ht.le I
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (c16_spatial_test_finite_dirichlet_energy_all_dimensions hκ hR hell s φ hφ I) ht.le
  have hparse : ‖f - hp.toLp φ‖ ^ 2 =
      ∑' n, (1 - Real.exp (-s.eigenvalue n * t)) ^ 2 * (a n) ^ 2 := by
    simpa only [f, b, a, hτ, Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis] using
      c16_dirichlet_heat_trace_parseval hR hκ hell s φ hφ τ
  have hae : ((f - hp.toLp φ : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
      fun x => (∫ y in sourceBall 0 R, K t x y * φ y) - φ x := by
    filter_upwards [Lp.coeFn_sub f (hp.toLp φ), haction, hp.coeFn_toLp] with x hx hy hz
    rw [hx]
    change f x - (hp.toLp φ) x = _
    rw [hy, hz, hτ]
  have hnorm := Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native
    hκ hell R (f - hp.toLp φ) (f - hp.toLp φ) _ _ hae hae
  rw [real_inner_self_eq_norm_sq] at hnorm
  have hnative : (∫ x in sourceBall 0 R, ρ x * ((∫ y in sourceBall 0 R, K t x y * φ y)-φ x)^2) = ‖f - hp.toLp φ‖ ^ 2 := by
    rw [hnorm]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  rw [hnative, hparse]
  exact hbound



end EinsteinFull.Calculus
