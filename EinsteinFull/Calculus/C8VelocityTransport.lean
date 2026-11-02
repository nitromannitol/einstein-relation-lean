import EinsteinRelation.Diffusion.Velocity
import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Algebra
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Velocity transport under actual path and kernel pushforwards

Path scaling keeps the environment index fixed. A separate measurable
reindexing transports the joint law and its kernel together, including spatial
reflection of both coefficient fields. Physical martingale problems are
transported under the actual path maps; no invariance of the original
environment law is assumed.
-/

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull
open EinsteinRelation

/-- Spatial scalar multiplication and positive-time dilation of continuous paths. -/
def velocityPathTransform {d : ℕ} (a : ℝ) (b : ℝ≥0) (γ : Path d) : Path d :=
  ⟨fun t => a • γ (b * t), by
    exact continuous_const.fun_smul
      (γ.continuous.comp (continuous_const.fun_mul continuous_id))⟩

theorem continuous_velocityPathTransform {d : ℕ} (a : ℝ) (b : ℝ≥0) :
    Continuous (velocityPathTransform (d := d) a b) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Path d × ℝ≥0 => a • p.1 (b * p.2))
  exact continuous_const.fun_smul (continuous_eval.comp
    (continuous_fst.prodMk (continuous_const.fun_mul continuous_snd)))

theorem measurable_velocityPathTransform {d : ℕ} (a : ℝ) (b : ℝ≥0) :
    Measurable (velocityPathTransform (d := d) a b) :=
  (continuous_velocityPathTransform a b).measurable

/-- The time dilation multiplies velocity by its rate, in addition to the
spatial scalar. No isotropy or property of the environment law is used. -/
theorem hasPathVelocity_velocityPathTransform {d : ℕ} {γ : Path d} {v : Vec d}
    (hv : HasPathVelocity γ v) (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    HasPathVelocity (velocityPathTransform a b γ) ((a * (b : ℝ)) • v) := by
  have ht : Tendsto (fun t : ℝ≥0 => b * t) atTop atTop :=
    tendsto_id.const_mul_atTop' hb
  have h := (hv.comp ht).const_smul (a * (b : ℝ))
  apply h.congr
  intro t
  ext i
  simp only [Function.comp_apply, velocityPathTransform, ContinuousMap.coe_mk,
    Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, mul_inv_rev]
  have hb' : (b : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hb)
  field_simp

private theorem velocityPathTransform_inverse {d : ℕ} {a : ℝ} (ha : a ≠ 0)
    {b : ℝ≥0} (hb : b ≠ 0) (γ : Path d) :
    velocityPathTransform a⁻¹ b⁻¹ (velocityPathTransform a b γ) = γ := by
  ext t i
  simp only [velocityPathTransform, ContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul]
  simp only [← mul_assoc, mul_inv_cancel₀ hb, inv_mul_cancel₀ ha, one_mul]

/-- Nondegenerate path scaling is a homeomorphism, so its pushforward carries
arbitrary almost-sure predicates without an extra event-measurability premise. -/
noncomputable def velocityPathHomeomorph {d : ℕ} {a : ℝ} (ha : a ≠ 0)
    {b : ℝ≥0} (hb : 0 < b) : Path d ≃ₜ Path d where
  toFun := velocityPathTransform a b
  invFun := velocityPathTransform a⁻¹ b⁻¹
  left_inv := velocityPathTransform_inverse ha (ne_of_gt hb)
  right_inv := by
    intro γ
    simpa only [inv_inv] using
      velocityPathTransform_inverse (inv_ne_zero ha) (inv_ne_zero (ne_of_gt hb)) γ
  continuous_toFun := continuous_velocityPathTransform a b
  continuous_invFun := continuous_velocityPathTransform a⁻¹ b⁻¹

/-- The actual pushforward kernel; its environment index is unchanged. -/
noncomputable def velocityKernelTransform {d : ℕ}
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (a : ℝ) (b : ℝ≥0) :
    ProbabilityTheory.Kernel (FieldPair d) (Path d) :=
  P.map (velocityPathTransform a b)

/-- Explicit pointwise law identity, justified by measurability of path scaling. -/
theorem velocityKernelTransform_apply {d : ℕ}
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (a : ℝ) (b : ℝ≥0)
    (ω : FieldPair d) :
    velocityKernelTransform P a b ω = (P ω).map (velocityPathTransform a b) :=
  ProbabilityTheory.Kernel.map_apply P (measurable_velocityPathTransform a b) ω

/-- Almost-sure velocity transport for the measurably mapped actual kernel.
No new velocity existence input is introduced: the given velocity is transported. -/
theorem hasQuenchedVelocity_velocityKernelTransform {d : ℕ}
    {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {v : Vec d}
    (hv : HasQuenchedVelocity Q P v) (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    HasQuenchedVelocity Q (velocityKernelTransform P a b) ((a * (b : ℝ)) • v) := by
  filter_upwards [hv] with ω hω
  rw [velocityKernelTransform_apply]
  by_cases ha : a = 0
  · subst a
    have hz : ∀ᵐ γ ∂(P ω).map (velocityPathTransform (d := d) 0 b), γ = 0 := by
      apply (ae_map_iff (measurable_velocityPathTransform 0 b).aemeasurable
        (measurableSet_singleton (0 : Path d))).2
      exact Filter.Eventually.of_forall fun γ => by
        ext t i
        simp only [velocityPathTransform, ContinuousMap.coe_mk, zero_smul,
          ContinuousMap.zero_apply, Pi.zero_apply]
    filter_upwards [hz] with γ hγ
    rw [hγ]
    simpa only [HasPathVelocity, ContinuousMap.zero_apply, smul_zero, zero_mul, zero_smul]
      using (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : Vec d)) atTop (𝓝 0))
  · apply (velocityPathHomeomorph ha hb).measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hω] with γ hγ
    exact hasPathVelocity_velocityPathTransform hγ a hb

/-- Spatial reflection of actual paths reverses the velocity. It asserts no
reflection invariance of the environment's joint coefficient law. -/
theorem hasQuenchedVelocity_reflection {d : ℕ} {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {v : Vec d}
    (hv : HasQuenchedVelocity Q P v) :
    HasQuenchedVelocity Q (velocityKernelTransform P (-1) 1) (-v) := by
  simpa only [NNReal.coe_one, mul_one, neg_one_smul] using
    hasQuenchedVelocity_velocityKernelTransform hv (-1) (by norm_num : (0 : ℝ≥0) < 1)

/-- Positive parabolic path scaling `rho * gamma(rho⁻² * t)` has velocity
`rho⁻¹ * v`, with the original environment law kept as the kernel index. -/
theorem hasQuenchedVelocity_parabolic {d : ℕ} {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {v : Vec d}
    (hv : HasQuenchedVelocity Q P v) {rho : ℝ≥0} (hrho : 0 < rho) :
    HasQuenchedVelocity Q (velocityKernelTransform P (rho : ℝ) (rho⁻¹ ^ 2))
      ((rho : ℝ)⁻¹ • v) := by
  have h := hasQuenchedVelocity_velocityKernelTransform hv (rho : ℝ)
    (pow_pos (inv_pos.mpr hrho) 2)
  have hr : (rho : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hrho)
  convert h using 1
  simp only [NNReal.coe_pow, NNReal.coe_inv]
  rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- The existing diffusive-scaling path is exactly this actual path transform. -/
theorem rescalePath_eq_velocityPathTransform {d : ℕ} (rho : ℝ≥0) (γ : Path d) :
    rescalePath (rho : ℝ) γ = velocityPathTransform (rho : ℝ) (rho⁻¹ ^ 2) γ := by
  have ht : ((rho : ℝ)⁻¹ ^ 2).toNNReal = rho⁻¹ ^ 2 := by
    simp only [← NNReal.coe_inv, ← NNReal.coe_pow, Real.toNNReal_coe]
  ext t i
  change ((rho : ℝ) • γ (((rho : ℝ)⁻¹ ^ 2).toNNReal * t)) i = _
  rw [ht]
  rfl

/-- The manuscript's existing parabolic path scaling transports its actual limit. -/
theorem hasPathVelocity_rescalePath {d : ℕ} {γ : Path d} {v : Vec d}
    (hv : HasPathVelocity γ v) {rho : ℝ≥0} (hrho : 0 < rho) :
    HasPathVelocity (rescalePath (rho : ℝ) γ) ((rho : ℝ)⁻¹ • v) := by
  rw [rescalePath_eq_velocityPathTransform]
  have h := hasPathVelocity_velocityPathTransform hv (rho : ℝ)
    (pow_pos (inv_pos.mpr hrho) 2)
  have hr : (rho : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hrho)
  convert h using 1
  simp only [NNReal.coe_pow, NNReal.coe_inv]
  rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- Reindex the mapped path kernel by the inverse of an actual environment
measurable equivalence. The coefficient law must be pushed forward as well. -/
noncomputable def reindexVelocityKernel {d : ℕ}
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (e : FieldPair d ≃ᵐ FieldPair d) (a : ℝ) (b : ℝ≥0) :
    ProbabilityTheory.Kernel (FieldPair d) (Path d) :=
  (velocityKernelTransform P a b).comap e.symm e.symm.measurable

/-- Exact law identity after simultaneous environment and path transport. -/
theorem reindexVelocityKernel_apply {d : ℕ}
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (e : FieldPair d ≃ᵐ FieldPair d) (a : ℝ) (b : ℝ≥0) (ω : FieldPair d) :
    reindexVelocityKernel P e a b (e ω) =
      (P ω).map (velocityPathTransform a b) := by
  simp only [reindexVelocityKernel, ProbabilityTheory.Kernel.comap_apply,
    e.symm_apply_apply, velocityKernelTransform_apply]

/-- Transport the actual environment law together with its actual path kernel.
This uses no symmetry of the source law, including no isotropy. -/
theorem hasQuenchedVelocity_reindexVelocityKernel {d : ℕ}
    {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {v : Vec d}
    (hv : HasQuenchedVelocity Q P v) (e : FieldPair d ≃ᵐ FieldPair d)
    (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    HasQuenchedVelocity (Q.map e) (reindexVelocityKernel P e a b)
      ((a * (b : ℝ)) • v) := by
  apply e.measurableEmbedding.ae_map_iff.mpr
  have h := hasQuenchedVelocity_velocityKernelTransform hv a hb
  filter_upwards [h] with ω hω
  simpa only [reindexVelocityKernel, ProbabilityTheory.Kernel.comap_apply,
    e.symm_apply_apply] using hω

/-- Full spatial inversion pulls back both the matrix and the potential.
Conjugation of a matrix by minus the identity leaves all its entries intact;
no diagonalization or isotropy hypothesis is involved. -/
def reflectEnvironment {d : ℕ} (ω : FieldPair d) : FieldPair d :=
  (ω.1.comp ⟨fun x => -x, continuous_neg⟩,
    ω.2.comp ⟨fun x => -x, continuous_neg⟩)

@[simp] theorem reflectEnvironment_matrix {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    (reflectEnvironment ω).1 x = ω.1 (-x) := rfl

@[simp] theorem reflectEnvironment_potential {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    (reflectEnvironment ω).2 x = ω.2 (-x) := rfl

theorem continuous_reflectEnvironment {d : ℕ} :
    Continuous (reflectEnvironment (d := d)) := by
  exact ((ContinuousMap.continuous_precomp
    (⟨fun x : Vec d => -x, continuous_neg⟩ : C(Vec d, Vec d))).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_precomp
      (⟨fun x : Vec d => -x, continuous_neg⟩ : C(Vec d, Vec d))).comp continuous_snd)

@[simp] theorem reflectEnvironment_involutive {d : ℕ} (ω : FieldPair d) :
    reflectEnvironment (reflectEnvironment ω) = ω := by
  apply Prod.ext <;> ext x <;>
    simp only [reflectEnvironment_matrix, reflectEnvironment_potential, neg_neg]

/-- Reflection is an actual equivalence of the joint coefficient carrier. -/
def reflectEnvironmentHomeomorph (d : ℕ) : FieldPair d ≃ₜ FieldPair d where
  toFun := reflectEnvironment
  invFun := reflectEnvironment
  left_inv := reflectEnvironment_involutive
  right_inv := reflectEnvironment_involutive
  continuous_toFun := continuous_reflectEnvironment
  continuous_invFun := continuous_reflectEnvironment

/-- The reflected joint law and reflected path kernel have opposite velocity.
This does not identify the reflected joint law with the original law. -/
theorem hasQuenchedVelocity_reflectedJointLaw {d : ℕ}
    {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {v : Vec d}
    (hv : HasQuenchedVelocity Q P v) :
    HasQuenchedVelocity (Q.map (reflectEnvironmentHomeomorph d))
      (reindexVelocityKernel P (reflectEnvironmentHomeomorph d).toMeasurableEquiv (-1) 1)
      (-v) := by
  simpa only [NNReal.coe_one, mul_one, neg_one_smul,
    Homeomorph.toMeasurableEquiv_coe] using
    hasQuenchedVelocity_reindexVelocityKernel hv
      (reflectEnvironmentHomeomorph d).toMeasurableEquiv (-1) (by norm_num : (0 : ℝ≥0) < 1)

/-- Reflection conjugates translation by `x` to translation by `-x`. -/
theorem reflectEnvironment_translate {d : ℕ} (x : Vec d) (ω : FieldPair d) :
    reflectEnvironment (translate x ω) = translate (-x) (reflectEnvironment ω) := by
  apply Prod.ext <;> ext y <;>
    simp only [reflectEnvironment_matrix, reflectEnvironment_potential,
      translate_matrix, translate_scalar]
  · abel_nf
  · congr 1
    abel

/-- Reflection preserves stationarity of the pushed-forward joint law; it
need not preserve the law itself. -/
theorem isStationary_reflectedJointLaw {d : ℕ} {Q : Measure (FieldPair d)}
    (hQ : IsStationary Q) : IsStationary (Q.map reflectEnvironment) := by
  intro x
  have hm := (continuous_reflectEnvironment (d := d)).measurable
  rw [Measure.map_map (EinsteinRelation.Probability.measurable_translate x) hm]
  have heq : translate x ∘ reflectEnvironment =
      reflectEnvironment ∘ translate (-x) := by
    funext ω
    simpa only [Function.comp_apply, neg_neg] using
      (reflectEnvironment_translate (-x) ω).symm
  rw [heq, ← Measure.map_map hm
    (EinsteinRelation.Probability.measurable_translate (-x)), hQ (-x)]

private theorem euclideanNorm_neg_reflection {d : ℕ} (x : Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  simp only [euclideanNorm, euclideanSq, dot, Pi.neg_apply, neg_mul_neg]

/-- Full spatial inversion retains the same ellipticity, potential and
Euclidean operator-Lipschitz bounds, including anisotropic matrices. -/
theorem isRegular_reflectEnvironment {d : ℕ} {Λ : ℝ} {ω : FieldPair d}
    (hω : IsRegular Λ ω) : IsRegular Λ (reflectEnvironment ω) := by
  refine ⟨fun x => hω.1 (-x), fun x => hω.2.1 (-x), ?_, ?_⟩
  · intro x y ξ
    have h := hω.2.2.1 (-x) (-y) ξ
    have heq : -x - -y = -(x - y) := by abel
    rw [heq, euclideanNorm_neg_reflection] at h
    exact h
  · intro x y
    have h := hω.2.2.2 (-x) (-y)
    have heq : -x - -y = -(x - y) := by abel
    rw [heq, euclideanNorm_neg_reflection] at h
    exact h

/-- Reflected joint observations on `U` depend only on original observations
on the inverse image of `U` under spatial inversion. -/
theorem localSigma_reflectEnvironment_comap_le {d : ℕ} (U : Set (Vec d)) :
    (localSigma U).comap reflectEnvironment ≤
      localSigma ((fun x : Vec d => -x) ⁻¹' U) := by
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro y
  rw [MeasurableSpace.comap_comp]
  exact le_iSup_of_le ⟨-y.1, by simpa only [Set.mem_preimage, neg_neg] using y.2⟩ le_rfl

/-- Full inversion preserves the strict Euclidean separation gap and joint
finite range, with the original range constant. -/
theorem hasFiniteRange_reflectedJointLaw {d : ℕ} {r₀ : ℝ}
    {Q : Measure (FieldPair d)} (hQ : HasFiniteRange r₀ Q) :
    HasFiniteRange r₀ (Q.map reflectEnvironment) := by
  intro U W hU hW hgap
  have hgap' : ∃ s : ℝ, r₀ < s ∧
      ∀ x ∈ (fun x : Vec d => -x) ⁻¹' U,
      ∀ y ∈ (fun x : Vec d => -x) ⁻¹' W, s ≤ euclideanNorm (x - y) := by
    rcases hgap with ⟨s, hs, hsep⟩
    refine ⟨s, hs, fun x hx y hy => ?_⟩
    have h := hsep (-x) hx (-y) hy
    have heq : -x - -y = -(x - y) := by abel
    simpa only [heq, euclideanNorm_neg_reflection] using h
  have hind := hQ _ _ (hU.preimage measurable_neg) (hW.preimage measurable_neg) hgap'
  rw [ProbabilityTheory.Indep_iff] at hind ⊢
  intro s t hs ht
  have hsB := EinsteinRelation.Probability.localSigma_le_borel U s hs
  have htB := EinsteinRelation.Probability.localSigma_le_borel W t ht
  have hlocalU := Measurable.of_comap_le (localSigma_reflectEnvironment_comap_le U)
  have hlocalW := Measurable.of_comap_le (localSigma_reflectEnvironment_comap_le W)
  have hm := (continuous_reflectEnvironment (d := d)).measurable
  rw [Measure.map_apply hm (hsB.inter htB), Measure.map_apply hm hsB,
    Measure.map_apply hm htB, Set.preimage_inter]
  exact hind _ _ (hlocalU hs) (hlocalW ht)

/-- The actual reflected environment law satisfies the same structural
parameters; equality with the original law is not required. -/
noncomputable def reflectedEnvironmentLaw {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) : EnvironmentLaw d Λ r₀ where
  measure := Q.measure.map reflectEnvironment
  probability := inferInstance
  ellipticity_parameter := Q.ellipticity_parameter
  range_parameter := Q.range_parameter
  regular := by
    apply (reflectEnvironmentHomeomorph d).measurableEmbedding.ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω
    exact isRegular_reflectEnvironment hω
  stationary := isStationary_reflectedJointLaw Q.stationary
  finiteRange := hasFiniteRange_reflectedJointLaw Q.finiteRange

@[simp] theorem reflectedEnvironmentLaw_measure {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) :
    (reflectedEnvironmentLaw Q).measure = Q.measure.map reflectEnvironment := rfl

/-- Spatial pullback of the joint matrix and potential, without modifying
matrix values or imposing isotropy. -/
def scaleEnvironment {d : ℕ} (c : ℝ) (ω : FieldPair d) : FieldPair d :=
  (ω.1.comp ⟨fun x => c • x, continuous_const.fun_smul continuous_id⟩,
    ω.2.comp ⟨fun x => c • x, continuous_const.fun_smul continuous_id⟩)

@[simp] theorem scaleEnvironment_matrix {d : ℕ} (c : ℝ) (ω : FieldPair d) (x : Vec d) :
    (scaleEnvironment c ω).1 x = ω.1 (c • x) := rfl

@[simp] theorem scaleEnvironment_potential {d : ℕ} (c : ℝ) (ω : FieldPair d) (x : Vec d) :
    (scaleEnvironment c ω).2 x = ω.2 (c • x) := rfl

theorem continuous_scaleEnvironment {d : ℕ} (c : ℝ) :
    Continuous (scaleEnvironment (d := d) c) := by
  exact ((ContinuousMap.continuous_precomp
    (⟨fun x : Vec d => c • x, continuous_const.fun_smul continuous_id⟩ :
      C(Vec d, Vec d))).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_precomp
      (⟨fun x : Vec d => c • x, continuous_const.fun_smul continuous_id⟩ :
        C(Vec d, Vec d))).comp continuous_snd)

theorem scaleEnvironment_inv {d : ℕ} {c : ℝ} (hc : c ≠ 0) (ω : FieldPair d) :
    scaleEnvironment c⁻¹ (scaleEnvironment c ω) = ω := by
  apply Prod.ext <;> ext x <;>
    simp only [scaleEnvironment_matrix, scaleEnvironment_potential, smul_smul,
      mul_inv_cancel₀ hc, one_smul]

/-- Nonzero spatial scaling is a homeomorphism of the joint carrier. -/
noncomputable def scaleEnvironmentHomeomorph (d : ℕ) (c : ℝ) (hc : c ≠ 0) :
    FieldPair d ≃ₜ FieldPair d where
  toFun := scaleEnvironment c
  invFun := scaleEnvironment c⁻¹
  left_inv := scaleEnvironment_inv hc
  right_inv := by
    intro ω
    simpa only [inv_inv] using scaleEnvironment_inv (inv_ne_zero hc) ω
  continuous_toFun := continuous_scaleEnvironment c
  continuous_invFun := continuous_scaleEnvironment c⁻¹

@[simp] theorem scaleEnvironmentHomeomorph_coe (d : ℕ) (c : ℝ) (hc : c ≠ 0) :
    (scaleEnvironmentHomeomorph d c hc : FieldPair d → FieldPair d) =
      scaleEnvironment c := rfl

/-- Spatial scaling conjugates the corresponding translations. -/
theorem scaleEnvironment_translate {d : ℕ} (c : ℝ) (x : Vec d) (ω : FieldPair d) :
    scaleEnvironment c (translate (c • x) ω) = translate x (scaleEnvironment c ω) := by
  apply Prod.ext <;> ext y <;>
    simp only [scaleEnvironment_matrix, scaleEnvironment_potential,
      translate_matrix, translate_scalar, smul_add]

theorem isStationary_scaledJointLaw {d : ℕ} {Q : Measure (FieldPair d)}
    (hQ : IsStationary Q) (c : ℝ) : IsStationary (Q.map (scaleEnvironment c)) := by
  intro x
  have hm := (continuous_scaleEnvironment (d := d) c).measurable
  rw [Measure.map_map (EinsteinRelation.Probability.measurable_translate x) hm]
  have heq : translate x ∘ scaleEnvironment c =
      scaleEnvironment c ∘ translate (c • x) := by
    funext ω
    exact (scaleEnvironment_translate c x ω).symm
  rw [heq, ← Measure.map_map hm
    (EinsteinRelation.Probability.measurable_translate (c • x)), hQ (c • x)]

/-- Contraction of the coefficient argument retains the same regularity
constant, using the manuscript's Euclidean operator bounds. -/
theorem isRegular_scaleEnvironment {d : ℕ} {Λ c : ℝ} {ω : FieldPair d}
    (hω : IsRegular Λ ω) (hc : |c| ≤ 1) : IsRegular Λ (scaleEnvironment c ω) := by
  have hΛ : 0 ≤ Λ := (abs_nonneg (ω.2 0)).trans (hω.2.1 0)
  have hdist (x y : Vec d) : euclideanNorm (c • x - c • y) ≤ euclideanNorm (x - y) := by
    rw [← smul_sub, TimeChange.euclideanNorm_smul]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) hc
  refine ⟨fun x => hω.1 (c • x), fun x => hω.2.1 (c • x), ?_, ?_⟩
  · intro x y ξ
    exact (hω.2.2.1 (c • x) (c • y) ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hdist x y) hΛ)
        (Real.sqrt_nonneg _))
  · intro x y
    exact (hω.2.2.2 (c • x) (c • y)).trans
      (mul_le_mul_of_nonneg_left (hdist x y) hΛ)

/-- Local observations scale with the joint coefficient argument. -/
theorem localSigma_scaleEnvironment_comap_le {d : ℕ} {c : ℝ} (hc : c ≠ 0)
    (U : Set (Vec d)) :
    (localSigma U).comap (scaleEnvironment c) ≤
      localSigma ((fun x : Vec d => c⁻¹ • x) ⁻¹' U) := by
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro y
  rw [MeasurableSpace.comap_comp]
  exact le_iSup_of_le ⟨c • y.1, by
    simpa only [Set.mem_preimage, smul_smul, inv_mul_cancel₀ hc, one_smul] using y.2⟩ le_rfl

/-- Positive spatial pullback transports joint finite range to `r₀ / c`,
retaining the strict separation gap. -/
theorem hasFiniteRange_scaledJointLaw {d : ℕ} {r₀ c : ℝ}
    {Q : Measure (FieldPair d)} (hQ : HasFiniteRange r₀ Q) (hc : 0 < c) :
    HasFiniteRange (r₀ / c) (Q.map (scaleEnvironment c)) := by
  intro U W hU hW hgap
  have hgap' : ∃ s : ℝ, r₀ < s ∧
      ∀ x ∈ (fun x : Vec d => c⁻¹ • x) ⁻¹' U,
      ∀ y ∈ (fun x : Vec d => c⁻¹ • x) ⁻¹' W,
        s ≤ euclideanNorm (x - y) := by
    rcases hgap with ⟨s, hs, hsep⟩
    refine ⟨c * s, ?_, fun x hx y hy => ?_⟩
    · simpa only [mul_comm] using (div_lt_iff₀ hc).mp hs
    · have h := hsep (c⁻¹ • x) hx (c⁻¹ • y) hy
      rw [← smul_sub, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hc)] at h
      have hmul := mul_le_mul_of_nonneg_left h hc.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hmul
  have hinv : Measurable (fun x : Vec d => c⁻¹ • x) :=
    (continuous_const.fun_smul continuous_id).measurable
  have hind := hQ _ _ (hU.preimage hinv) (hW.preimage hinv) hgap'
  rw [ProbabilityTheory.Indep_iff] at hind ⊢
  intro s t hs ht
  have hsB := EinsteinRelation.Probability.localSigma_le_borel U s hs
  have htB := EinsteinRelation.Probability.localSigma_le_borel W t ht
  have hlocalU := Measurable.of_comap_le (localSigma_scaleEnvironment_comap_le hc.ne' U)
  have hlocalW := Measurable.of_comap_le (localSigma_scaleEnvironment_comap_le hc.ne' W)
  have hm := (continuous_scaleEnvironment (d := d) c).measurable
  rw [Measure.map_apply hm (hsB.inter htB), Measure.map_apply hm hsB,
    Measure.map_apply hm htB, Set.preimage_inter]
  exact hind _ _ (hlocalU hs) (hlocalW ht)

/-- The actual spatially scaled joint law, with explicit enlarged range. -/
noncomputable def scaledEnvironmentLaw {d : ℕ} {Λ r₀ c : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (hc : 0 < c) (hc1 : c ≤ 1) :
    EnvironmentLaw d Λ (r₀ / c) where
  measure := Q.measure.map (scaleEnvironment c)
  probability := inferInstance
  ellipticity_parameter := Q.ellipticity_parameter
  range_parameter := (le_div_iff₀ hc).mpr (by
    simpa only [one_mul] using hc1.trans Q.range_parameter)
  regular := by
    apply (scaleEnvironmentHomeomorph d c hc.ne').measurableEmbedding.ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω
    exact isRegular_scaleEnvironment hω (by simpa only [abs_of_pos hc] using hc1)
  stationary := isStationary_scaledJointLaw Q.stationary c
  finiteRange := hasFiniteRange_scaledJointLaw Q.finiteRange hc

@[simp] theorem scaledEnvironmentLaw_measure {d : ℕ} {Λ r₀ c : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (hc : 0 < c) (hc1 : c ≤ 1) :
    (scaledEnvironmentLaw Q hc hc1).measure = Q.measure.map (scaleEnvironment c) := rfl

/-- The actual path kernel paired with the scaled joint coefficient law.
The path transform is `gamma(t) ↦ c⁻¹ • gamma(c²*t)`. -/
noncomputable def scaledEnvironmentKernel {d : ℕ}
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (c : ℝ) (hc : 0 < c) :
    ProbabilityTheory.Kernel (FieldPair d) (Path d) :=
  reindexVelocityKernel P (scaleEnvironmentHomeomorph d c hc.ne').toMeasurableEquiv
    c⁻¹ ((NNReal.mk c hc.le) ^ (2 : ℕ))

/-- Exact path-law pushforward at the corresponding scaled environment. -/
theorem scaledEnvironmentKernel_apply {d : ℕ}
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (c : ℝ) (hc : 0 < c) (ω : FieldPair d) :
    scaledEnvironmentKernel P c hc (scaleEnvironment c ω) =
      (P ω).map (velocityPathTransform c⁻¹ ((NNReal.mk c hc.le) ^ (2 : ℕ))) := by
  simpa only [scaledEnvironmentKernel, Homeomorph.toMeasurableEquiv_coe,
    scaleEnvironmentHomeomorph_coe] using
    reindexVelocityKernel_apply P
      (scaleEnvironmentHomeomorph d c hc.ne').toMeasurableEquiv
      c⁻¹ ((NNReal.mk c hc.le) ^ (2 : ℕ)) ω

/-- Simultaneous coefficient and parabolic path scaling transports velocity
under the actual pushed-forward joint law. -/
theorem hasQuenchedVelocity_scaledJointLaw {d : ℕ}
    {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {v : Vec d}
    (hv : HasQuenchedVelocity Q P v) {c : ℝ} (hc : 0 < c) :
    HasQuenchedVelocity (Q.map (scaleEnvironment c))
      (scaledEnvironmentKernel P c hc) (c • v) := by
  have h := hasQuenchedVelocity_reindexVelocityKernel hv
    (scaleEnvironmentHomeomorph d c hc.ne').toMeasurableEquiv c⁻¹
    (b := (NNReal.mk c hc.le) ^ (2 : ℕ))
    (sq_pos_of_pos (show (0 : ℝ≥0) < (NNReal.mk c hc.le) from hc))
  simpa only [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_mk, pow_two, ← mul_assoc,
    inv_mul_cancel₀ hc.ne', one_mul, Homeomorph.toMeasurableEquiv_coe,
    scaledEnvironmentKernel, scaleEnvironmentHomeomorph_coe] using h

/-- The coordinate chain rule under scalar spatial precomposition. -/
theorem coordinateDerivative_comp_spatialScale {d : ℕ} (c : ℝ)
    (j : Fin d) (f : Vec d → ℝ) (x : Vec d) :
    coordinateDerivative j (fun y => f (c • y)) x =
      c * coordinateDerivative j f (c • x) := by
  simp only [coordinateDerivative, fderiv_comp_smul, smul_apply,
    smul_eq_mul]

/-- The gradient chain rule retains all coordinate directions. -/
theorem gradient_comp_spatialScale {d : ℕ} (c : ℝ)
    (f : Vec d → ℝ) (x : Vec d) :
    gradient (fun y => f (c • y)) x = c • gradient f (c • x) := by
  ext j
  exact coordinateDerivative_comp_spatialScale c j f x

/-- Divergence of a vector field precomposed by spatial scaling. -/
theorem divergence_comp_spatialScale {d : ℕ} (c : ℝ)
    (F : Vec d → Vec d) (x : Vec d) :
    divergence (fun y => F (c • y)) x = c * divergence F (c • x) := by
  unfold divergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact coordinateDerivative_comp_spatialScale c j (fun y => F y j) x

/-- Scalar multiplication of the output commutes with divergence, including
at points where the total derivative is defined by zero. -/
theorem divergence_const_smul {d : ℕ} (c : ℝ)
    (F : Vec d → Vec d) (x : Vec d) :
    divergence (fun y => c • F y) x = c * divergence F x := by
  unfold divergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (fderiv ℝ (c • (fun y => F y j)) x) (unitVector j) =
    c * (fderiv ℝ (fun y => F y j) x) (unitVector j)
  rw [congrFun (fderiv_const_smul_field c) x]
  rfl

/-- Spatial scaling conjugates the actual physical generator, with force
scaled by the same signed scalar and the full matrix field retained. -/
theorem physicalGenerator_scaleEnvironment {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam c : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    physicalGenerator i (scaleEnvironment c ω) (c * lam)
      (fun y => f (c • y)) x =
      c ^ 2 * physicalGenerator i ω lam f (c • x) := by
  have hfield : (fun y =>
      (reducedCoefficient (scaleEnvironment c ω) y).mulVec
        (gradient (fun z => f (c • z)) y)) =
      (fun y => c • ((reducedCoefficient ω (c • y)).mulVec
        (gradient f (c • y)))) := by
    funext y
    rw [gradient_comp_spatialScale, Matrix.mulVec_smul]
    rfl
  have hdot (v w : Vec d) : dot v (c • w) = c * dot v w := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    congr 1
    funext j
    ring
  unfold physicalGenerator
  rw [hfield, divergence_const_smul,
    divergence_comp_spatialScale c
      (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x]
  rw [gradient_comp_spatialScale, hdot]
  simp only [scaleEnvironment_matrix, scaleEnvironment_potential]
  ring

@[simp] theorem scaleEnvironment_neg_one {d : ℕ} (ω : FieldPair d) :
    scaleEnvironment (-1) ω = reflectEnvironment ω := by
  apply Prod.ext <;> ext x <;> simp [scaleEnvironment, reflectEnvironment]

/-- Reflection reverses the signed force in the physical generator. -/
theorem physicalGenerator_reflectEnvironment {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    physicalGenerator i (reflectEnvironment ω) (-lam) (fun y => f (-y)) x =
      physicalGenerator i ω lam f (-x) := by
  simpa only [scaleEnvironment_neg_one, neg_one_mul, neg_smul, one_smul,
    neg_one_sq, one_mul] using physicalGenerator_scaleEnvironment i ω lam (-1) f x

/-- The inverse-scaled test form used with the parabolic path map. -/
theorem physicalGenerator_scaleEnvironment_inverseTest {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam c : ℝ) (hc : c ≠ 0)
    (f : Vec d → ℝ) (x : Vec d) :
    physicalGenerator i (scaleEnvironment c ω) (c * lam) f x =
      c ^ 2 * physicalGenerator i ω lam (fun y => f (c⁻¹ • y)) (c • x) := by
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using
    physicalGenerator_scaleEnvironment i ω lam c (fun y => f (c⁻¹ • y)) x

/-- The spatial scalar homeomorphism used to transport compact tests. -/
noncomputable def velocitySpatialHomeomorph (d : ℕ) (c : ℝ) (hc : c ≠ 0) :
    Vec d ≃ₜ Vec d where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := by simp [smul_smul, hc]
  right_inv x := by simp [smul_smul, hc]
  continuous_toFun := continuous_const.fun_smul continuous_id
  continuous_invFun := continuous_const.fun_smul continuous_id

theorem smooth_comp_spatialScale {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f (c • x)) :=
  hf.comp (contDiff_const_smul c)

theorem compactSupport_comp_spatialScale {d : ℕ} {f : Vec d → ℝ}
    (hf : HasCompactSupport f) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport (fun x => f (c • x)) :=
  hf.comp_homeomorph (velocitySpatialHomeomorph d c hc)

/-- The transformed path up to time `t` only uses the original path up to
`b*t`. This is a statement about the actual canonical past sigma algebras. -/
theorem measurable_velocityPathTransform_past {d : ℕ} (a : ℝ) (b t : ℝ≥0) :
    Measurable[pathFiltration d (b * t), pathFiltration d t]
      (velocityPathTransform (d := d) a b) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (velocityPathTransform a b)
    (⨆ j, ⨆ (_ : j ≤ t), MeasurableSpace.comap (pathPosition j) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun j => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hj => ?_
  rw [MeasurableSpace.comap_comp]
  have hm : Measurable[pathFiltration d (b * t)] (pathPosition (d := d) (b * j)) :=
    ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable)
      (b * j)).measurable).mono
      ((pathFiltration d).mono (mul_le_mul_of_nonneg_left hj (show 0 ≤ b from zero_le))) le_rfl
  exact ((measurable_const (a := a)).smul hm).comap_le

/-- Reflection identifies the actual compensated tests at the same time. -/
theorem compensatedTest_reflectedPath {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) (f : Vec d → ℝ) (t : ℝ≥0) (γ : Path d) :
    compensatedTest (physicalGenerator i (reflectEnvironment ω) (-lam)) f t
      (velocityPathTransform (-1) 1 γ) =
    compensatedTest (physicalGenerator i ω lam) (fun y => f (-y)) t γ := by
  have hgen (y : Vec d) :
      physicalGenerator i (reflectEnvironment ω) (-lam) f (-y) =
      physicalGenerator i ω lam (fun z => f (-z)) y := by
    simpa only [neg_neg] using
      physicalGenerator_reflectEnvironment i ω lam (fun z => f (-z)) (-y)
  simp only [compensatedTest, velocityPathTransform, ContinuousMap.coe_mk,
    one_mul, neg_smul, one_smul, hgen]

/-- Reflection is an involution on the actual continuous path space. -/
theorem velocityPathTransform_reflection_involutive {d : ℕ} :
    Function.Involutive (velocityPathTransform (d := d) (-1) 1) := by
  intro γ
  ext t j
  simp [velocityPathTransform]

/-- Reflection transports the physical martingale problem under the actual
path pushforward, with the starting point and signed force reflected. -/
theorem solvesMartingaleProblem_reflectedPath {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) (x : Vec d) {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    SolvesMartingaleProblem (physicalGenerator i (reflectEnvironment ω) (-lam))
      (-x) (P.map (velocityPathTransform (-1) 1)) := by
  obtain ⟨hprob, hstart, htests⟩ := hP
  have : IsProbabilityMeasure P := hprob
  let Φ := velocityPathTransform (d := d) (-1) 1
  have hΦ : Measurable Φ := measurable_velocityPathTransform (-1) 1
  have hΦpast (t : ℝ≥0) : Measurable[pathFiltration d t, pathFiltration d t] Φ := by
    change Measurable[pathFiltration d t, pathFiltration d t]
      (velocityPathTransform (d := d) (-1) 1)
    have h := measurable_velocityPathTransform_past (d := d) (-1) 1 t
    rw [one_mul] at h
    exact h
  have hinv (γ : Path d) : Φ (Φ γ) = γ :=
    velocityPathTransform_reflection_involutive γ
  refine ⟨inferInstance, ?_, ?_⟩
  · apply (velocityPathHomeomorph (d := d) (a := -1) (by norm_num)
      (b := 1) (by norm_num)).measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hstart] with γ hγ
    change (velocityPathTransform (-1) 1 γ) 0 = -x
    simp only [velocityPathTransform, ContinuousMap.coe_mk, mul_zero,
      neg_smul, one_smul, hγ]
  · intro f hfs hfc
    let g : Vec d → ℝ := fun y => f (-y)
    have hgs : ContDiff ℝ (⊤ : ℕ∞) g := by
      simpa only [neg_smul, one_smul] using smooth_comp_spatialScale hfs (-1)
    have hgc : HasCompactSupport g := by
      simpa only [neg_smul, one_smul] using
        compactSupport_comp_spatialScale hfc (c := -1) (by norm_num)
    obtain ⟨hint, hmint, hmart⟩ := htests g hgs hgc
    let M := compensatedTest (physicalGenerator i ω lam) g
    let N := compensatedTest (physicalGenerator i (reflectEnvironment ω) (-lam)) f
    have he (t : ℝ≥0) (γ : Path d) : N t (Φ γ) = M t γ :=
      compensatedTest_reflectedPath i ω lam f t γ
    have he' (t : ℝ≥0) : N t = M t ∘ Φ := by
      funext γ
      change N t γ = M t (Φ γ)
      exact (congrArg (N t) (hinv γ)).symm.trans (he t (Φ γ))
    have hNad : StronglyAdapted (pathFiltration d) N := by
      intro t
      rw [he']
      exact (hmart.1 t).comp_measurable (hΦpast t)
    have hNm (t : ℝ≥0) : StronglyMeasurable (N t) :=
      (hNad t).mono ((pathFiltration d).le t)
    have hNint (t : ℝ≥0) : Integrable (N t) (P.map Φ) := by
      apply (integrable_map_measure (hNm t).aestronglyMeasurable hΦ.aemeasurable).2
      have heq : N t ∘ Φ = M t := funext (he t)
      rw [heq]
      exact hmint t
    refine ⟨?_, hNint, hNad, ?_⟩
    · intro t
      apply (velocityPathHomeomorph (d := d) (a := -1) (by norm_num)
        (b := 1) (by norm_num)).measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hint t] with γ hγ
      have hgen (y : Vec d) :
          physicalGenerator i (reflectEnvironment ω) (-lam) f (-y) =
          physicalGenerator i ω lam g y := by
        simpa only [g, neg_neg] using
          physicalGenerator_reflectEnvironment i ω lam g (-y)
      change IntervalIntegrable (fun u : ℝ =>
        physicalGenerator i (reflectEnvironment ω) (-lam) f
          ((velocityPathTransform (-1) 1 γ) u.toNNReal)) volume 0 (t : ℝ)
      simpa only [velocityPathTransform, ContinuousMap.coe_mk,
        one_mul, neg_smul, one_smul, hgen] using hγ
    · intro r s hrs
      refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration d).le r)
        (hNint s) (fun B _ _ => (hNint r).integrableOn) ?_
        (hNad r).aestronglyMeasurable).symm
      intro B hB _
      have hBm : MeasurableSet B := (pathFiltration d).le r B hB
      rw [setIntegral_map hBm (hNm r).aestronglyMeasurable hΦ.aemeasurable,
        setIntegral_map hBm (hNm s).aestronglyMeasurable hΦ.aemeasurable]
      have heq (t : ℝ≥0) : (fun γ => N t (Φ γ)) = M t := funext (he t)
      simp only [heq]
      exact hmart.setIntegral_eq hrs (hΦpast r hB)

/-- Deterministic positive-time substitution, retaining the real-time
`toNNReal` evaluation used by the actual martingale-problem definition. -/
theorem intervalIntegral_nonneg_timeScale (H : ℝ≥0 → ℝ) (b t : ℝ≥0) :
    (∫ u in (0 : ℝ)..(t : ℝ), (b : ℝ) * H (b * u.toNNReal)) =
      ∫ u in (0 : ℝ)..((b * t : ℝ≥0) : ℝ), H u.toNNReal := by
  have he (u : ℝ) : b * u.toNNReal = ((b : ℝ) * u).toNNReal := by
    rw [Real.toNNReal_mul b.coe_nonneg, Real.toNNReal_coe]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  simpa only [NNReal.coe_mul, mul_zero, smul_eq_mul] using
    intervalIntegral.smul_integral_comp_mul_left (fun u : ℝ => H u.toNNReal)
      (a := 0) (b := (t : ℝ)) (b : ℝ)

/-- The actual parabolic path map identifies compensated tests at the
corresponding deterministic time in the original physical problem. -/
theorem compensatedTest_scaledPath {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam c : ℝ) (hc : 0 < c)
    (f : Vec d → ℝ) (t : ℝ≥0) (γ : Path d) :
    compensatedTest (physicalGenerator i (scaleEnvironment c ω) (c * lam)) f t
      (velocityPathTransform c⁻¹ ((NNReal.mk c hc.le) ^ (2 : ℕ)) γ) =
    compensatedTest (physicalGenerator i ω lam) (fun y => f (c⁻¹ • y))
      (((NNReal.mk c hc.le) ^ (2 : ℕ)) * t) γ := by
  let b : ℝ≥0 := (NNReal.mk c hc.le) ^ (2 : ℕ)
  have hb : (b : ℝ) = c ^ 2 := by simp [b]
  have hgen (y : Vec d) :
      physicalGenerator i (scaleEnvironment c ω) (c * lam) f (c⁻¹ • y) =
        c ^ 2 * physicalGenerator i ω lam (fun z => f (c⁻¹ • z)) y := by
    simpa only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using
      physicalGenerator_scaleEnvironment_inverseTest i ω lam c hc.ne' f (c⁻¹ • y)
  change compensatedTest _ f t (velocityPathTransform c⁻¹ b γ) =
    compensatedTest _ (fun y => f (c⁻¹ • y)) (b * t) γ
  simp only [compensatedTest, velocityPathTransform, ContinuousMap.coe_mk,
    mul_zero, hgen]
  rw [← hb, intervalIntegral_nonneg_timeScale
    (fun u => physicalGenerator i ω lam (fun z => f (c⁻¹ • z)) (γ u)) b t]

/-- Parabolic scaling transports the actual physical martingale problem,
including the canonical past, all compact smooth tests and integrability. -/
theorem solvesMartingaleProblem_scaledPath {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam c : ℝ) (hc : 0 < c) (x : Vec d)
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    SolvesMartingaleProblem (physicalGenerator i (scaleEnvironment c ω) (c * lam))
      (c⁻¹ • x) (P.map
        (velocityPathTransform c⁻¹ ((NNReal.mk c hc.le) ^ (2 : ℕ)))) := by
  obtain ⟨hprob, hstart, htests⟩ := hP
  have : IsProbabilityMeasure P := hprob
  let b : ℝ≥0 := (NNReal.mk c hc.le) ^ (2 : ℕ)
  have hb : 0 < b := sq_pos_of_pos (show (0 : ℝ≥0) < NNReal.mk c hc.le from hc)
  let e := velocityPathHomeomorph (d := d) (a := c⁻¹) (inv_ne_zero hc.ne') hb
  let Φ := velocityPathTransform (d := d) c⁻¹ b
  have hΦ : Measurable Φ := measurable_velocityPathTransform c⁻¹ b
  have hΦpast (t : ℝ≥0) :
      Measurable[pathFiltration d (b * t), pathFiltration d t] Φ :=
    measurable_velocityPathTransform_past c⁻¹ b t
  have hΨpast (t : ℝ≥0) :
      Measurable[pathFiltration d t, pathFiltration d (b * t)] e.symm := by
    change Measurable[pathFiltration d t, pathFiltration d (b * t)]
      (velocityPathTransform (c⁻¹)⁻¹ b⁻¹)
    have h := measurable_velocityPathTransform_past (d := d) (c⁻¹)⁻¹ b⁻¹ (b * t)
    rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul] at h
    exact h
  refine ⟨inferInstance, ?_, ?_⟩
  · apply e.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hstart] with γ hγ
    change (velocityPathTransform c⁻¹ b γ) 0 = c⁻¹ • x
    simp only [velocityPathTransform, ContinuousMap.coe_mk, mul_zero, hγ]
  · intro f hfs hfc
    let g : Vec d → ℝ := fun y => f (c⁻¹ • y)
    have hgs : ContDiff ℝ (⊤ : ℕ∞) g := smooth_comp_spatialScale hfs c⁻¹
    have hgc : HasCompactSupport g :=
      compactSupport_comp_spatialScale hfc (inv_ne_zero hc.ne')
    obtain ⟨hint, hmint, hmart⟩ := htests g hgs hgc
    let M := compensatedTest (physicalGenerator i ω lam) g
    let N := compensatedTest (physicalGenerator i (scaleEnvironment c ω) (c * lam)) f
    have he (t : ℝ≥0) (γ : Path d) : N t (Φ γ) = M (b * t) γ :=
      compensatedTest_scaledPath i ω lam c hc f t γ
    have he' (t : ℝ≥0) : N t = M (b * t) ∘ e.symm := by
      funext γ
      change N t γ = M (b * t) (e.symm γ)
      have h := he t (e.symm γ)
      change N t (e (e.symm γ)) = _ at h
      rw [e.apply_symm_apply] at h
      exact h
    have hNad : StronglyAdapted (pathFiltration d) N := by
      intro t
      rw [he']
      exact (hmart.1 (b * t)).comp_measurable (hΨpast t)
    have hNm (t : ℝ≥0) : StronglyMeasurable (N t) :=
      (hNad t).mono ((pathFiltration d).le t)
    have hNint (t : ℝ≥0) : Integrable (N t) (P.map Φ) := by
      apply (integrable_map_measure (hNm t).aestronglyMeasurable hΦ.aemeasurable).2
      have heq : N t ∘ Φ = M (b * t) := funext (he t)
      rw [heq]
      exact hmint (b * t)
    refine ⟨?_, hNint, hNad, ?_⟩
    · intro t
      apply e.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hint (b * t)] with γ hγ
      have hgen (y : Vec d) :
          physicalGenerator i (scaleEnvironment c ω) (c * lam) f (c⁻¹ • y) =
            (b : ℝ) * physicalGenerator i ω lam g y := by
        simpa only [b, NNReal.coe_pow, NNReal.coe_mk, smul_smul,
          mul_inv_cancel₀ hc.ne', one_smul] using
          physicalGenerator_scaleEnvironment_inverseTest i ω lam c hc.ne' f (c⁻¹ • y)
      have heval (u : ℝ) : b * u.toNNReal = ((b : ℝ) * u).toNNReal := by
        rw [Real.toNNReal_mul b.coe_nonneg, Real.toNNReal_coe]
      have hscaled := hγ.comp_mul_left (c := (b : ℝ))
      have hscaled' : IntervalIntegrable
          (fun u : ℝ => physicalGenerator i ω lam g (γ (b * u.toNNReal)))
          volume 0 (t : ℝ) := by
        simpa only [NNReal.coe_mul, zero_div, mul_div_cancel_left₀ (t : ℝ)
          (show (b : ℝ) ≠ 0 from NNReal.coe_ne_zero.mpr hb.ne'), ← heval] using hscaled
      change IntervalIntegrable (fun u : ℝ =>
        physicalGenerator i (scaleEnvironment c ω) (c * lam) f
          ((velocityPathTransform c⁻¹ b γ) u.toNNReal)) volume 0 (t : ℝ)
      simpa only [velocityPathTransform, ContinuousMap.coe_mk, hgen] using
        hscaled'.const_mul (b : ℝ)
    · intro r s hrs
      refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration d).le r)
        (hNint s) (fun B _ _ => (hNint r).integrableOn) ?_
        (hNad r).aestronglyMeasurable).symm
      intro B hB _
      have hBm : MeasurableSet B := (pathFiltration d).le r B hB
      rw [setIntegral_map hBm (hNm r).aestronglyMeasurable hΦ.aemeasurable,
        setIntegral_map hBm (hNm s).aestronglyMeasurable hΦ.aemeasurable]
      have heq (t : ℝ≥0) : (fun γ => N t (Φ γ)) = M (b * t) := funext (he t)
      simp only [heq]
      exact hmart.setIntegral_eq (mul_le_mul_of_nonneg_left hrs
        (show 0 ≤ b from zero_le)) (hΦpast r hB)

/-- The physical origin martingale problem transports simultaneously with the
actual joint environment law and its measurably reindexed path kernel. -/
theorem solvesMartingaleProblem_scaledJointLaw {d : ℕ} (i : Fin d)
    {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} (lam c : ℝ) (hc : 0 < c)
    (hP : ∀ᵐ ω ∂Q, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (P ω)) :
    ∀ᵐ ω ∂Q.map (scaleEnvironment c),
      SolvesMartingaleProblem (physicalGenerator i ω (c * lam)) 0
        (scaledEnvironmentKernel P c hc ω) := by
  apply (scaleEnvironmentHomeomorph d c hc.ne').measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hP] with ω hω
  change SolvesMartingaleProblem
    (physicalGenerator i (scaleEnvironment c ω) (c * lam)) 0
    (scaledEnvironmentKernel P c hc (scaleEnvironment c ω))
  rw [scaledEnvironmentKernel_apply]
  simpa only [smul_zero] using
    solvesMartingaleProblem_scaledPath i ω lam c hc 0 hω

end EinsteinFull
