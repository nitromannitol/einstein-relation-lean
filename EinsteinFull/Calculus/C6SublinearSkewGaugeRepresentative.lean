import EinsteinFull.Calculus.C6SublinearSkewRepresentative
import EinsteinFull.Calculus.C3SublinearSmoothBootstrap

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.AKM EinsteinRelation.Correctors
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

namespace C6SkewGauge

/-- Smooth vector forcing has a finite Euclidean Hölder bound on every ball. -/
theorem exists_holder_field_ball {d : ℕ} {F : Vec d → Vec d}
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : Vec d) R) F (1 / 2) K := by
  obtain ⟨K, hK, hFK⟩ :=
    PDE.exists_euclideanFieldHolderSeminormLE_half_of_contDiff
      (fun j => (hF j).comp (contDiff_id.const_smul R))
  have hmem {x : Vec d} (hx : x ∈ PDE.euclideanBall (0 : Vec d) R) :
      R⁻¹ • x ∈ PDE.euclideanBall (0 : Vec d) 1 := by
    apply (PDE.DGNM.affineScale_mem_euclideanBall_iff 0 hR 1 (R⁻¹ • x)).mp
    simpa only [mul_one, smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_zero] using hx
  refine ⟨K * (R⁻¹) ^ (1 / 2 : ℝ),
    mul_nonneg hK (Real.rpow_nonneg (inv_nonneg.mpr hR.le) _), ?_⟩
  intro x hx y hy
  have h := hFK (R⁻¹ • x) (hmem hx) (R⁻¹ • y) (hmem hy)
  change PDE.vecEuclideanNorm (F (R • (R⁻¹ • x)) - F (R • (R⁻¹ • y))) ≤
    K * PDE.vecEuclideanNorm (R⁻¹ • x - R⁻¹ • y) ^ (1 / 2 : ℝ) at h
  simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at h
  rw [← smul_sub, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
    Real.mul_rpow (inv_nonneg.mpr hR.le) (PDE.vecEuclideanNorm_nonneg _)] at h
  simpa only [mul_assoc] using h

theorem identity_elliptic (d : ℕ) : PDE.IsEllipticMatrix 1 1 (1 : Mat d) := by
  refine ⟨by norm_num, le_rfl, ?_, ?_⟩
  · intro ξ
    change 1 * PDE.vecNormSq ξ ≤ PDE.vecDot ξ ((1 : Mat d).mulVec ξ)
    rw [Matrix.one_mulVec, one_mul]
    exact le_rfl
  · intro ξ
    simp only [inv_one]
    change 1 * PDE.vecNormSq ξ ≤ PDE.vecDot ξ ((1 : Mat d).mulVec ξ)
    rw [Matrix.one_mulVec, one_mul]
    exact le_rfl

/-- Local Schauder regularity for the literal weak Poisson potential. -/
theorem exists_holder_poisson_gradient_ball {d : ℕ} (hd : 0 < d)
    {u : Vec d → ℝ} {g F : Vec d → Vec d}
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ (fun x => g x + F x) (fun _ => 0))
    {R : ℝ} (hR : 0 < R)
    (hu : MemLp u 2 (volume.restrict (ball 0 R)))
    (hg : MemLp g 2 (volume.restrict (ball 0 R))) :
    ∃ (G : Vec d → Vec d) (K : ℝ), 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE
        (PDE.euclideanBall (0 : Vec d) (R * (1 / 2))) G (1 / 2) K ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (R * (1 / 2)))] g := by
  classical
  have hball : PDE.euclideanBall (0 : Vec d) R = ball 0 R := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR
  rw [← hball] at hu hg
  have hell : PDE.IsEllipticFieldOn 1 1 (PDE.euclideanBall (0 : Vec d) R)
      (fun _ => (1 : Mat d)) := by
    refine ⟨?_, fun _ _ => identity_elliptic d⟩
    apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro k
    exact Measurable.ite (PDE.isOpen_euclideanBall _ _).measurableSet
      measurable_const measurable_const
  have hFl : PDE.MemVectorL2On (PDE.euclideanBall (0 : Vec d) R) F := by
    intro j
    exact (PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR)
      ((hF j).of_le (by simp))).memL2
  have he' : HasWeakDivergence Set.univ
      (fun x => (1 : Mat d).mulVec (g x) + F x) (fun _ => 0) := by
    simpa only [Matrix.one_mulVec] using he
  have hsol := C3SublinearSmooth.sourceH1_forced_isL2Solution hell hu hg hFl hw he'
  exact C3SublinearSmooth.exists_holder_forced_gradient_ball hd hR
    (fun _ => (1 : Mat d)) F (fun _ _ => contDiff_const)
    (exists_holder_field_ball hF hR) (fun _ _ => identity_elliptic d)
    (C3SublinearC1.sourceH1 hu hg hw) hsol.toIsWeakDivergenceFormSolutionOn

/-- The inhomogeneous Poisson equation gives a C1 representative in the
literal AE potential class, without choosing a new additive normalization. -/
theorem exists_c1_poisson_representative {d : ℕ} (hd : 0 < d)
    {u : Vec d → ℝ} {g F : Vec d → Vec d}
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ (fun x => g x + F x) (fun _ => 0))
    (hl : ∀ R : ℝ, 0 < R →
      MemLp u 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R))) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (1 : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))] u ∧
      gradient v =ᵐ[(volume : Measure (Vec d))] g := by
  have hlocal (n : ℕ) : ∃ G : Vec d → Vec d,
      ContinuousOn G (PDE.euclideanBall (0 : Vec d) (n + 1 : ℝ)) ∧
      G =ᵐ[PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (n + 1 : ℝ))] g := by
    have hR : (0 : ℝ) < 2 * (n + 1 : ℝ) := by positivity
    obtain ⟨G, K, hK, hGH, hG⟩ := exists_holder_poisson_gradient_ball hd hF hw he hR
      (hl _ hR).1 (hl _ hR).2
    have hr : 2 * (n + 1 : ℝ) * (1 / 2) = n + 1 := by ring
    rw [hr] at hGH hG
    exact ⟨G, hGH.continuousOn (by norm_num) hK, hG⟩
  obtain ⟨G, hGc, hG⟩ := C3SublinearC1.exists_continuous_representative_of_open_cover g
    (fun n => PDE.euclideanBall (0 : Vec d) (n + 1 : ℝ))
    (fun _ => PDE.isOpen_euclideanBall _ _) (by
      intro x
      obtain ⟨n, hn⟩ := exists_nat_gt (PDE.vecEuclideanNorm x)
      refine ⟨n, ?_⟩
      apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mpr
      simpa only [sub_zero] using hn.trans (by norm_num : (n : ℝ) < n + 1)) hlocal
  obtain ⟨v, hv, hvu, hvg⟩ :=
    C3SublinearC1.exists_c1_representative_of_source_continuous_gradient hd hw hGc hG
  refine ⟨v, hv, hvu, ?_⟩
  filter_upwards [hvg] with x hx
  exact funext hx

/-- Local Hölder regularity belongs to the gradient of the same C1 value
representative, by equality of continuous representatives on each open ball. -/
theorem holder_gradient_of_c1_poisson {d : ℕ} (hd : 0 < d)
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (he : HasWeakDivergence Set.univ (fun x => gradient u x + F x) (fun _ => 0)) :
    ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
        (gradient u) (1 / 2) K := by
  intro R hR
  have h2R : 0 < 2 * R := mul_pos (by norm_num) hR
  let U := PDE.euclideanBall (0 : Vec d) (2 * R)
  let w := PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (PDE.isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) h2R) hu
  have hw := C3SublinearSmooth.hasWeakGradient_of_contDiff hu
  have hball : U = ball (0 : Vec d) (2 * R) := by
    ext x
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt h2R
  have hval : MemLp u 2 (volume.restrict (ball 0 (2 * R))) := by
    rw [← hball]
    exact w.memL2
  have hgrad : MemLp (gradient u) 2 (volume.restrict (ball 0 (2 * R))) := by
    rw [← hball]
    exact memLp_pi_iff.mpr fun j => w.gradMemL2 j
  obtain ⟨G, K, hK, hGH, hG⟩ := exists_holder_poisson_gradient_ball hd hF hw he
    h2R hval hgrad
  have hr : (2 * R) * (1 / 2 : ℝ) = R := by ring
  rw [hr] at hGH hG
  have hgc : Continuous (gradient u) := by
    apply continuous_pi
    intro j
    exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have heq : EqOn G (gradient u) (PDE.euclideanBall (0 : Vec d) R) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hG
      (PDE.isOpen_euclideanBall _ _) (hGH.continuousOn (by norm_num) hK)
      hgc.continuousOn
  refine ⟨K, hK, fun x hx y hy => ?_⟩
  rw [← heq hx, ← heq hy]
  exact hGH x hx y hy

theorem identity_operatorLipschitz (d : ℕ) :
    IsOperatorLipschitz 0 (fun _ : Vec d => (1 : Mat d)) := by
  intro x y ξ
  change euclideanNorm (((1 : Mat d) - 1).mulVec ξ) ≤
    0 * euclideanNorm (x - y) * euclideanNorm ξ
  rw [sub_self, Matrix.zero_mulVec, zero_mul, zero_mul]
  change Real.sqrt (∑ _ : Fin d, (0 : ℝ) * 0) ≤ 0
  simp only [mul_zero, Finset.sum_const_zero, Real.sqrt_zero, le_refl]

/-- The existing forced Schauder bootstrap applies to the identity operator
with the actual smooth source retained in the equation. -/
theorem c2_and_holder_hessian_of_c1_poisson {d : ℕ} (hd : 0 < d)
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (he : HasWeakDivergence Set.univ (fun x => gradient u x + F x) (fun _ => 0)) :
    ContDiff ℝ (2 : ℕ∞) u ∧
      ∀ (z : Vec d) (R : ℝ), 0 < R → ∃ K : ℝ, 0 ≤ K ∧
        PDE.EuclideanFieldHolderSeminormLE (PDE.euclideanBall (0 : Vec d) R)
          (gradient (fun x => fderiv ℝ u x z)) (1 / 2) K := by
  have he' : HasWeakDivergence Set.univ
      (fun x => (1 : Mat d).mulVec (0 + gradient u x) + F x) (fun _ => 0) := by
    simpa only [zero_add, Matrix.one_mulVec] using he
  exact C3SublinearSmooth.contDiff_two_and_holder_gradient_fderiv_of_forced_equation hd
    (a := fun _ => (1 : Mat d)) (Λ := 1) (L := 0) (u := u) (S := F)
    (fun _ _ => contDiff_const) (identity_operatorLipschitz d)
    (fun _ => identity_elliptic d) hu (fun j => (hF j).of_le (by simp))
    (holder_gradient_of_c1_poisson hd hu hF he)
    (fun z _ hR => exists_holder_field_ball
      (fun j => (contDiff_infty_iff_fderiv.mp (hF j)).2.clm_apply contDiff_const) hR)
    0 he'

/-- Differentiation of the forced Poisson equation has no coefficient
commutator, because the literal coefficient is the identity. -/
theorem poisson_equation_fderiv {d : ℕ}
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : ContDiff ℝ (2 : ℕ∞) u)
    (hF : ∀ j, ContDiff ℝ (1 : ℕ∞) (fun x => F x j))
    (he : HasWeakDivergence Set.univ (fun x => gradient u x + F x) (fun _ => 0))
    (z : Vec d) :
    HasWeakDivergence Set.univ
      (fun x => gradient (fun y => fderiv ℝ u y z) x +
        (fun j => fderiv ℝ (fun y => F y j) x z)) (fun _ => 0) := by
  have he' : HasWeakDivergence Set.univ
      (fun x => (1 : Mat d).mulVec (0 + gradient u x) + F x) (fun _ => 0) := by
    simpa only [zero_add, Matrix.one_mulVec] using he
  have h := C3SublinearSmooth.weakDivergence_forced_gradient_fderiv
    (a := fun _ => (1 : Mat d)) (u := u) (S := F)
    (fun _ _ => contDiff_const) hu hF 0 he' z
  simpa only [Matrix.one_mulVec, fderiv_const_apply, zero_apply,
    show (fun _ _ : Fin d => (0 : ℝ)) = (0 : Mat d) from rfl,
    Matrix.zero_mulVec, zero_add] using h

/-- A C1 weak solution of the Poisson equation with smooth divergence forcing
is smooth. Each induction step differentiates the actual equation. -/
theorem smooth_of_c1_poisson {d : ℕ} (hd : 0 < d)
    {u : Vec d → ℝ} {F : Vec d → Vec d}
    (hu : ContDiff ℝ (1 : ℕ∞) u)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (he : HasWeakDivergence Set.univ (fun x => gradient u x + F x) (fun _ => 0)) :
    ContDiff ℝ (⊤ : ℕ∞) u := by
  have hfinite (n : ℕ) : ∀ (v : Vec d → ℝ) (S : Vec d → Vec d),
      ContDiff ℝ (1 : ℕ∞) v →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => S x j)) →
      HasWeakDivergence Set.univ (fun x => gradient v x + S x) (fun _ => 0) →
      ContDiff ℝ (n : ℕ∞) v := by
    induction n with
    | zero => exact fun v S hv _ _ => hv.of_le (by norm_num)
    | succ n ih =>
      intro v S hv hS hvE
      obtain ⟨hv₂, _⟩ := c2_and_holder_hessian_of_c1_poisson hd hv hS hvE
      change ContDiff ℝ ((n : WithTop ℕ∞) + 1) v
      apply contDiff_succ_iff_fderiv_apply.mpr
      refine ⟨hv.differentiable (by norm_num), by simp, fun z => ?_⟩
      exact ih (fun x => fderiv ℝ v x z)
        (fun x j => fderiv ℝ (fun y => S y j) x z)
        ((hv₂.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
        (fun j => (contDiff_infty_iff_fderiv.mp (hS j)).2.clm_apply contDiff_const)
        (poisson_equation_fderiv hv₂ (fun j => (hS j).of_le (by simp)) hvE z)
  exact contDiff_infty.mpr fun n => hfinite n u F hu hF he

/-- Smooth inhomogeneous regularity preserves both the literal potential
class and its specified weak gradient. -/
theorem exists_smooth_poisson_representative {d : ℕ} (hd : 0 < d)
    {u : Vec d → ℝ} {g F : Vec d → Vec d}
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (hw : HasWeakGradient Set.univ u g)
    (he : HasWeakDivergence Set.univ (fun x => g x + F x) (fun _ => 0))
    (hl : ∀ R : ℝ, 0 < R →
      MemLp u 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R))) :
    ∃ v : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      v =ᵐ[(volume : Measure (Vec d))] u ∧
      gradient v =ᵐ[(volume : Measure (Vec d))] g := by
  obtain ⟨v, hv, hvu, hvg⟩ := exists_c1_poisson_representative hd hF hw he hl
  have hvE : HasWeakDivergence Set.univ (fun x => gradient v x + F x)
      (fun _ => 0) := by
    apply Correctors.hasWeakDivergence_congr_ae isOpen_univ he _
      Filter.EventuallyEq.rfl
    rw [Measure.restrict_univ]
    filter_upwards [hvg] with x hx
    rw [hx]
  exact ⟨v, smooth_of_c1_poisson hd hv hF hvE, hvu, hvg⟩

end C6SkewGauge

/-- Smoothness of the scalar corrector gives a smooth representative of its
actual centered flux, under the same physical environment law. -/
theorem c6_centeredFlux_smooth_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ q : Vec d → Vec d,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => q x j)) ∧
      q =ᵐ[(volume : Measure (Vec d))]
        centeredFlux φ (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) := by
  have hs : ∀ᵐ ω ∂physicalReferenceLaw Q, IsSmoothFieldPair ω.1 := by
    have h := hQ.mono fun _ hω => hω.1
    rw [← physicalReferenceLaw_forget Q] at h
    exact ae_of_ae_map measurable_subtype_coe.aemeasurable h
  filter_upwards [sublinear_source_corrector_smooth_representative d hd D Q hQ i φ, hs]
    with ω hv hsω
  obtain ⟨u, hu, _, hug⟩ := hv
  let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
  have ha := C3SublinearC1.project_smooth (r₀ := D.dependenceRange)
    Q.ellipticity_parameter ω hsω
  refine ⟨fun x => (a x).mulVec ((correctorUnitVector i).ofLp + gradient u x) - meanFlux φ,
    ?_, ?_⟩
  · intro j
    change ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      (∑ k, a x j k * ((correctorUnitVector i).ofLp k + gradient u x k)) - meanFlux φ j)
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.sum
    intro k _
    exact (ha j k).mul (contDiff_const.add
      ((contDiff_infty_iff_fderiv.mp hu).2.clm_apply contDiff_const))
  · filter_upwards [hug] with x hx
    have hgrad : gradient u x = φ.grad a x := funext hx
    simp only [centeredFlux, hgrad]
    rfl

/-- Smooth representatives of the skew-gauged source entries, retaining
their actual source gradients. This is inhomogeneous regularity for the
curl-Poisson equation, with the same scalar corrector throughout. -/
theorem c6_skewSource_entries_smooth_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ j k : Fin d, ∃ w : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) w ∧
      w =ᵐ[(volume : Measure (Vec d))]
        (fun x => c6SkewSourcePotential S (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x j k) ∧
      gradient w =ᵐ[(volume : Measure (Vec d))]
        S.grad (project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω) j k := by
  have hm := (measurable_project (d := d) (r₀ := D.dependenceRange)
    Q.ellipticity_parameter).aemeasurable (μ := physicalReferenceLaw Q)
  have hw := ae_of_ae_map hm (c6SkewSourcePotential_weak_gradient S)
  have hl := ae_of_ae_map hm (c6SkewSourceFluxCorrector S).locally_square_integrable
  have he := ae_of_ae_map hm (c6_sourcePotential_poisson_flux (by omega) S)
  have ht := ae_of_ae_map hm (sublinear_source_flux_column_trace d hd D Q hQ i φ S)
  filter_upwards [c6_centeredFlux_smooth_representative d hd D Q hQ i φ, hw, hl, he, ht]
    with ω hq hwω hlω heω htω
  obtain ⟨q, hq, hqeq⟩ := hq
  let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
  intro j k
  let F : Vec d → Vec d := fun x => -(q x j • unitVector k - q x k • unitVector j)
  have hF : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x l) := by
    intro l
    exact (((hq j).mul contDiff_const).sub ((hq k).mul contDiff_const)).neg
  have hE : HasWeakDivergence Set.univ (fun x => S.grad a j k x + F x)
      (fun _ => 0) := by
    apply Correctors.hasWeakDivergence_congr_ae isOpen_univ (heω j k) _
      Filter.EventuallyEq.rfl
    rw [Measure.restrict_univ]
    filter_upwards [htω, hqeq] with x hx hqx
    change S.grad a j k x -
      (c6SourceRowDivergence S a x j • unitVector k -
        c6SourceRowDivergence S a x k • unitVector j) = S.grad a j k x + F x
    rw [hx, ← hqx]
    rfl
  exact C6SkewGauge.exists_smooth_poisson_representative (by omega) hF (hwω j k) hE
    (fun R hR => hlω R hR j k)

/-- The sign-corrected skew representative of the same source potential,
modulo its permitted constant matrix gauge. -/
theorem sublinear_source_skew_smooth_representative_mod_const
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ (v : Vec d → Mat d) (A : Mat d),
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j k)) ∧
      (∀ x, (v x).transpose = -(v x)) ∧
      v =ᵐ[(volume : Measure (Vec d))]
        (fun x => -S.potential (project (r₀ := D.dependenceRange)
          Q.ellipticity_parameter ω) x + A) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        (∑ k : Fin d, fderiv ℝ (fun y => v y k j) x (unitVector k)) =
          centeredFlux φ (project (r₀ := D.dependenceRange)
            Q.ellipticity_parameter ω) x j := by
  classical
  have hm := (measurable_project (d := d) (r₀ := D.dependenceRange)
    Q.ellipticity_parameter).aemeasurable (μ := physicalReferenceLaw Q)
  have hg := ae_of_ae_map hm (c6SkewSourcePotential_matrix_gauge (by omega) S)
  have ht := ae_of_ae_map hm
    (c6_actualSourceColumnGradientTrace_eq_neg_centeredFlux d hd D Q hQ i φ S)
  filter_upwards [c6_skewSource_entries_smooth_representative d hd D Q hQ i φ S, hg, ht]
    with ω hw hgω htω
  let a := project (r₀ := D.dependenceRange) Q.ellipticity_parameter ω
  choose w hwc hwp hwg using hw
  let W : Vec d → Mat d := fun x j k => w j k x
  have hW : W =ᵐ[(volume : Measure (Vec d))] c6SkewSourcePotential S a := by
    filter_upwards [ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hwp j k] with x hx
    exact funext fun j => funext fun k => hx j k
  have hWskew : ∀ x, (W x).transpose = -(W x) := by
    have heq : (fun x => (W x).transpose) = (fun x => -(W x)) := by
      apply MeasureTheory.Measure.eq_of_ae_eq
        (hW.mono fun x hx => by rw [hx]; exact c6SkewSourcePotential_transpose S a x)
      · exact continuous_pi fun j => continuous_pi fun k => (hwc k j).continuous
      · exact continuous_pi fun j => continuous_pi fun k => (hwc j k).continuous.neg
    exact congrFun heq
  obtain ⟨C, hC⟩ := hgω
  refine ⟨fun x => -W x, -C, fun j k => (hwc j k).neg, ?_, ?_, ?_⟩
  · intro x
    rw [Matrix.transpose_neg, hWskew x]
  · filter_upwards [hW, hC] with x hx hCx
    rw [hx, hCx, neg_add]
  · have hall := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => hwg j k
    filter_upwards [hall, htω] with x hx htx
    intro j
    calc
      (∑ k : Fin d, fderiv ℝ (fun y => (-W y) k j) x (unitVector k)) =
          ∑ k : Fin d, -(S.grad a k j x k) := by
        apply Finset.sum_congr rfl
        intro k _
        change fderiv ℝ (fun y => -(w k j y)) x (unitVector k) = _
        rw [fderiv_fun_neg]
        exact congrArg Neg.neg (congrFun (hx k j) k)
      _ = -(∑ k : Fin d, S.grad a k j x k) := by rw [Finset.sum_neg_distrib]
      _ = centeredFlux φ a x j := by rw [htx j, neg_neg]

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.sublinear_source_skew_smooth_representative_mod_const
