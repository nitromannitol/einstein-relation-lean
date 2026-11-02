import EinsteinRelation.Diffusion.CanonicalKernelStrongContinuitySupport
import EinsteinRelation.Diffusion.FellerKernelUniquenessSupport
import EinsteinRelation.Calculus.GeneratorMeasurability
import EinsteinRelation.Environment.Smooth
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Full compact-test integration by parts and finite-time integration for the supplied GMP law.

These results use the actual differential expression and every supplied start.
They do not assume that the law solves a martingale problem. -/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section
namespace EinsteinFull.Work.W5
open EinsteinRelation
open External.GantertSection7Support

/-- Coordinate differentiation preserves smoothness of an actual test. -/
theorem gantert_contDiff_coordinateDerivative {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j f) := by
  exact ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const)

/-- The actual physical differential expression is smooth for smooth fields. -/
theorem gantert_contDiff_physicalGenerator {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalGenerator i ω lam f) := by
  have hg j := gantert_contDiff_coordinateDerivative hf j
  have ha j k : ContDiff ℝ (⊤ : ℕ∞) (fun x => reducedCoefficient ω x j k) :=
    ((contDiff_const.mul hω.2).exp).mul (hω.1 j k)
  have hflux j : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (reducedCoefficient ω x).mulVec (gradient f x) j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ k : Fin d, _ * _)
    exact ContDiff.sum fun k _ => (ha j k).mul (hg k)
  have hdiv : ContDiff ℝ (⊤ : ℕ∞)
      (divergence (fun x => (reducedCoefficient ω x).mulVec (gradient f x))) :=
    ContDiff.sum fun j _ => gantert_contDiff_coordinateDerivative (hflux j) j
  have hforce : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => dot ((ω.1 x).mulVec (unitVector i)) (gradient f x)) := by
    apply ContDiff.sum
    intro j _
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => (∑ k : Fin d, ω.1 x j k * unitVector i k) * _)
    exact (ContDiff.sum fun k _ => (hω.1 j k).mul contDiff_const).mul (hg j)
  exact ((contDiff_const.mul hω.2).exp.div_const 2 |>.mul hdiv).add
    (contDiff_const.mul hforce)

/-- Product rule for the actual spatial divergence, retaining all coordinates. -/
theorem gantert_divergence_scalar_mul {d : ℕ} (w : Vec d → ℝ) (F : Vec d → Vec d)
    (hw : Differentiable ℝ w) (hF : ∀ j, Differentiable ℝ (fun x => F x j))
    (x : Vec d) :
    divergence (fun y => w y • F y) x =
      w x * divergence F x + dot (gradient w x) (F x) := by
  unfold divergence dot gradient coordinateDerivative
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fderiv_fun_mul (hw x) (hF _ x), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The literal exponential force weight has its signed coordinate derivative. -/
theorem gantert_coordinateDerivative_forceWeight {d : ℕ} (hd : 2 ≤ d)
    (lam : ℝ) (j : Fin d) (x : Vec d) :
    coordinateDerivative j (physicalForceWeight hd lam) x =
      physicalForceWeight hd lam x * (2 * lam) * unitVector (firstCoordinateIndex hd) j := by
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) (firstCoordinateIndex hd) x).const_mul
    (2 * lam)).exp
  change fderiv ℝ (fun y : Vec d => Real.exp (2 * lam * y (firstCoordinateIndex hd)))
    x (unitVector j) = _
  simp only [h.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, physicalForceWeight]
  have he : unitVector j (firstCoordinateIndex hd) = unitVector (firstCoordinateIndex hd) j := by
    simp only [unitVector, Pi.single_apply, eq_comm]
  rw [he]
  ring

/-- The true reversible density times the physical generator is the divergence
of the true weighted symmetric flux, with the source factor one half. -/
theorem gantert_density_mul_physicalGenerator {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω)
    (hsymm : ∀ x, (ω.1 x).transpose = ω.1 x) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec d) :
    physicalReversibleDensity ω hd lam x *
        physicalGenerator (firstCoordinateIndex hd) ω lam f x =
      (1 / 2 : ℝ) * divergence
        (fun y => physicalForceWeight hd lam y •
          (reducedCoefficient ω y).mulVec (gradient f y)) x := by
  have hw : Differentiable ℝ (physicalForceWeight hd lam : Vec d → ℝ) :=
    ((contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd))).exp :
      ContDiff ℝ (⊤ : ℕ∞) _).differentiable (by simp)
  have hflux j : Differentiable ℝ
      (fun y => (reducedCoefficient ω y).mulVec (gradient f y) j) := by
    apply ContDiff.differentiable (n := (⊤ : ℕ∞)) _ (by simp)
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k : Fin d, _ * _)
    exact ContDiff.sum fun k _ =>
      (((contDiff_const.mul hω.2).exp).mul (hω.1 j k)).mul
        (gantert_contDiff_coordinateDerivative hf k)
  have hsym : (reducedCoefficient ω x).transpose = reducedCoefficient ω x := by
    simp only [reducedCoefficient, Matrix.transpose_smul, hsymm x]
  have hforce : dot ((reducedCoefficient ω x).mulVec (unitVector (firstCoordinateIndex hd)))
      (gradient f x) = (reducedCoefficient ω x).mulVec (gradient f x) (firstCoordinateIndex hd) := by
    simp only [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply Finset.sum_congr rfl
    intro j _
    have he := congrFun (congrFun hsym j) (firstCoordinateIndex hd)
    exact congrArg (fun a => a * gradient f x j) he.symm
  rw [gantert_divergence_scalar_mul _ _ hw hflux]
  have hdot : dot (gradient (physicalForceWeight hd lam) x)
      ((reducedCoefficient ω x).mulVec (gradient f x)) =
      physicalForceWeight hd lam x * (2 * lam) *
        (reducedCoefficient ω x).mulVec (gradient f x) (firstCoordinateIndex hd) := by
    simp only [dot, gradient, gantert_coordinateDerivative_forceWeight, unitVector,
      Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hdot]
  change (physicalForceWeight hd lam x * clockDensity ω x) * _ = _
  rw [mul_assoc, clockDensity_mul_physicalGenerator]
  unfold reducedGenerator
  rw [hforce]
  ring

/-- Integration by parts against every member of the full weak-gradient graph.
There is no smooth-test restriction on the Sobolev argument. -/
theorem gantert_weakGradient_integral_divergence {d : ℕ} {m : Measure (Vec d)}
    (u : SpatialDirichlet.WeightedSobolevGraph m) (F : Vec d → Vec d)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (hc : ∀ j, HasCompactSupport (fun x => F x j)) :
    (∫ x, u.value x * divergence F x ∂volume) =
      -(∫ x, dot (WithLp.ofLp (u.weakGradient x)) (F x) ∂volume) := by
  classical
  by_cases he : IsEmpty (Fin d)
  · letI := he
    simp [divergence, dot]
  haveI : Nonempty (Fin d) := not_isEmpty_iff.mp he
  have hv : LocallyIntegrable u.value volume :=
    locallyIntegrableOn_univ.mp (u.distributionalGradient (Classical.arbitrary (Fin d))).1
  have hg j : LocallyIntegrable (fun x => WithLp.ofLp (u.weakGradient x) j) volume :=
    locallyIntegrableOn_univ.mp (u.distributionalGradient j).2.1
  have hd j : HasCompactSupport (coordinateDerivative j (fun x => F x j)) := by
    exact (hc j).fderiv_apply (𝕜 := ℝ) (unitVector j)
  have hi j : Integrable (fun x => u.value x * coordinateDerivative j (fun y => F y j) x)
      volume := by
    simpa only [smul_eq_mul] using hv.integrable_smul_right_of_hasCompactSupport
      (gantert_contDiff_coordinateDerivative (hF j) j).continuous (hd j)
  have hj j : Integrable (fun x => WithLp.ofLp (u.weakGradient x) j * F x j) volume := by
    simpa only [smul_eq_mul] using (hg j).integrable_smul_right_of_hasCompactSupport
      (hF j).continuous (hc j)
  simp only [divergence, dot, Finset.mul_sum]
  rw [integral_finset_sum _ (fun j _ => hi j), integral_finset_sum _ (fun j _ => hj j), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [setIntegral_univ] using
    (u.distributionalGradient j).2.2 (fun x => F x j) ⟨hF j, hc j, Set.subset_univ _⟩

/-- Rewriting physical integration keeps the literal strictly positive density. -/
theorem gantert_integral_physicalMeasure {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (g : Vec d → ℝ) :
    (∫ x, g x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, physicalReversibleDensity ω hd lam x * g x ∂volume := by
  rw [physicalReversibleMeasure, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x))
    (ENNReal.measurable_ofReal.comp (physicalReversibleDensity_continuous ω hd lam).measurable)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (physicalReversibleDensity_pos ω hd lam _).le, smul_eq_mul]

/-- A compact smooth physical test satisfies the weighted integration-by-parts
identity against EVERY member of the full Sobolev graph. -/
theorem gantert_fullForm_compactTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω)
    (hsymm : ∀ x, (ω.1 x).transpose = ω.1 x) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam)) :
    (∫ x, u.value x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
      ∂physicalReversibleMeasure ω hd lam) =
    -(∫ x, (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
      ((ω.1 x).mulVec (gradient f x)) ∂physicalReversibleMeasure ω hd lam) := by
  let F : Vec d → Vec d := fun y => physicalForceWeight hd lam y •
    (reducedCoefficient ω y).mulVec (gradient f y)
  have hF j : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j) := by
    apply ContDiff.mul
      ((contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd))).exp)
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ k : Fin d, _ * _)
    exact ContDiff.sum fun k _ =>
      (((contDiff_const.mul hω.2).exp).mul (hω.1 j k)).mul
        (gantert_contDiff_coordinateDerivative hf k)
  have hFc j : HasCompactSupport (fun x => F x j) := by
    apply hc.mono'
    intro x hx
    by_contra hxnot
    have hg : gradient f x = 0 := by
      ext k
      simp only [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxnot,
        ContinuousLinearMap.zero_apply, Pi.zero_apply]
    exact hx (by simp [F, hg])
  have h := gantert_weakGradient_integral_divergence u F hF hFc
  rw [gantert_integral_physicalMeasure, gantert_integral_physicalMeasure]
  calc
    _ = (1 / 2 : ℝ) * ∫ x, u.value x * divergence F x ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        have he := gantert_density_mul_physicalGenerator hd ω hω hsymm lam hf x
        change _ = (1 / 2 : ℝ) * (u.value x * divergence F x)
        change physicalReversibleDensity ω hd lam x * _ = _
        rw [mul_left_comm, he]
        ring
    _ = -(∫ x, physicalReversibleDensity ω hd lam x * ((1 / 2 : ℝ) *
        dot (WithLp.ofLp (u.weakGradient x)) ((ω.1 x).mulVec (gradient f x))) ∂volume) := by
      rw [h, mul_neg, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (1 / 2 : ℝ) * dot _ (physicalForceWeight hd lam x •
          (reducedCoefficient ω x).mulVec (gradient f x)) = _
        rw [reducedCoefficient, Matrix.smul_mulVec]
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          physicalReversibleDensity]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- The total differential expression vanishes off the test's closed support,
including at nonsmooth coefficients. -/
theorem gantert_physicalGenerator_support_subset {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) (f : Vec d → ℝ) :
    Function.support (physicalGenerator i ω lam f) ⊆ tsupport f := by
  intro x hx
  by_contra hnot
  have hz : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hnot
  have hg : gradient f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hz.fderiv (𝕜 := ℝ)] with y hy
    funext j
    simp only [gradient, coordinateDerivative, hy, fderiv_const_apply, ContinuousLinearMap.zero_apply,
      Pi.zero_apply]
  have hflux : (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) =ᶠ[𝓝 x]
      fun _ => 0 := hg.mono fun y hy => by simp only [hy, Matrix.mulVec_zero]
  have hd : divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x = 0 := by
    unfold divergence coordinateDerivative
    apply Finset.sum_eq_zero
    intro j _
    have hcoord : (fun y => (reducedCoefficient ω y).mulVec (gradient f y) j) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := hflux.mono fun y hy => congrFun hy j
    have he := hcoord.fderiv_eq (𝕜 := ℝ)
    simp only [fderiv_const_apply] at he
    rw [he, ContinuousLinearMap.zero_apply]
  have hgx := hg.eq_of_nhds
  exact hx (by simp only [physicalGenerator, hd, hgx, dot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add])

/-- Compact support belongs to the literal generator, without changing its representative. -/
theorem gantert_hasCompactSupport_physicalGenerator {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) {f : Vec d → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (physicalGenerator i ω lam f) :=
  hc.mono' (gantert_physicalGenerator_support_subset i ω lam f)

/-- Package a literal continuous compact test without modifying its values. -/
def gantertCompactObservable {d : ℕ} (f : Vec d → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Vec d →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (Classical.choose (hc.exists_bound_of_continuous hf))
    (Classical.choose_spec (hc.exists_bound_of_continuous hf))

@[simp] theorem gantertCompactObservable_apply {d : ℕ} (f : Vec d → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) (x : Vec d) :
    gantertCompactObservable f hf hc x = f x := rfl

/-- The physical speed measure is locally finite for the genuine potential. -/
theorem gantert_physicalMeasure_locallyFinite {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) :
    IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
  SpatialDirichlet.densityWeightedMeasure_locallyFinite _
    (physicalReversibleDensity_continuous ω hd lam)

/-- The actual generator representative lies in the actual weighted L2 space. -/
theorem gantert_memLp_physicalGenerator {d : ℕ} (hd : 2 ≤ d) (i : Fin d)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    MemLp (physicalGenerator i ω lam f) 2 (physicalReversibleMeasure ω hd lam) := by
  letI := gantert_physicalMeasure_locallyFinite hd ω lam
  exact (gantert_contDiff_physicalGenerator i ω hω lam hf).continuous.memLp_of_hasCompactSupport
    (gantert_hasCompactSupport_physicalGenerator i ω lam hc)

/-- Pathwise time integrability holds for every continuous path and finite interval. -/
theorem gantert_intervalIntegrable_physicalGenerator {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (γ : Path d) (a b : ℝ) :
    IntervalIntegrable (fun u => physicalGenerator i ω lam f (γ u.toNNReal)) volume a b :=
  ((gantert_contDiff_physicalGenerator i ω hω lam hf).continuous.comp
    (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable a b

section Realization
variable {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h₀ h₁)

/-- A positive-time transition charges no exceptional set of the actual physical measure. -/
theorem gantert_transition_absolutelyContinuous (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    R.transitionKernel t x ≪ physicalReversibleMeasure ω hd lam := by
  rw [R.transitionKernel_eq_heatKernel t ht x]
  apply Measure.AbsolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  intro A hA
  have hnull : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, y ∉ A :=
    measure_eq_zero_iff_ae_notMem.mp hA
  exact measure_eq_zero_iff_ae_notMem.mpr
    ((SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
      _ (physicalReversibleDensity_continuous ω hd lam)
        (physicalReversibleDensity_pos ω hd lam) _).mp hnull)

/-- Almost-everywhere representatives can be substituted after any positive time,
at every starting point. No spatial continuity of a transition is presumed. -/
theorem gantert_transition_integral_congr_ae (t : ℝ≥0) (ht : 0 < t) (x : Vec d)
    {f g : Vec d → ℝ} (hfg : f =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    (∫ y, f y ∂R.transitionKernel t x) = ∫ y, g y ∂R.transitionKernel t x :=
  integral_congr_ae ((gantert_transition_absolutelyContinuous hd Λ hΛ ω hω lam h₀ h₁ R
    t ht x).ae_le hfg)

/-- Time continuity holds at each start, including time zero, by continuous paths. -/
theorem gantert_continuous_transition_time (f : Vec d →ᵇ ℝ) (x : Vec d) :
    Continuous (fun t : ℝ≥0 => ∫ y, f y ∂R.transitionKernel t x) := by
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have he (t : ℝ≥0) : (∫ y, f y ∂R.transitionKernel t x) =
      ∫ γ, f (γ t) ∂R.pathLaw x := by
    rw [← R.pathLaw_endpoint t x]
    exact integral_map (measurable_pathPosition t).aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t
    exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  · intro t
    exact Eventually.of_forall fun γ => f.norm_coe_le_norm (γ t)
  · exact integrable_const _
  · exact Eventually.of_forall fun γ => f.continuous.comp γ.continuous

/-- The actual transition tends to evaluation at every specified start. -/
theorem gantert_transition_tendsto_zero (f : Vec d →ᵇ ℝ) (x : Vec d) :
    Tendsto (fun t : ℝ≥0 => ∫ y, f y ∂R.transitionKernel t x) (𝓝 0) (𝓝 (f x)) := by
  have he : (∫ y, f y ∂R.transitionKernel 0 x) = f x := by
    rw [R.transitionKernel_zero, ProbabilityTheory.Kernel.id_apply, integral_dirac]
  simpa only [he] using
    (gantert_continuous_transition_time hd Λ hΛ ω hω lam h₀ h₁ R f x).tendsto 0

private theorem gantert_integrable_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Eventually.of_forall hB)⟩

/-- Fubini for occupation of a bounded continuous test under the SAME supplied
law, derived from its one-time marginals. -/
theorem gantert_integral_occupation (g : Vec d →ᵇ ℝ) (x : Vec d) (T : ℝ≥0) :
    (∫ γ, (∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) ∂R.pathLaw x) =
      ∫ u in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel u.toNNReal x := by
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let H : Path d × ℝ → ℝ := fun p => g (p.1 p.2.toNNReal)
  have hH : Measurable H := by
    apply g.continuous.measurable.comp
    exact (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hint : Integrable H ((R.pathLaw x).prod ν) :=
    gantert_integrable_bounded _ hH ‖g‖ (fun p => g.norm_coe_le_norm _)
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  calc
    _ = ∫ u, ∫ γ, H (γ, u) ∂R.pathLaw x ∂ν := integral_integral_swap hint
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        change (∫ γ, g (γ u.toNNReal) ∂R.pathLaw x) =
          ∫ y, g y ∂R.transitionKernel u.toNNReal x
        rw [← R.pathLaw_endpoint u.toNNReal x]
        exact (integral_map (measurable_pathPosition u.toNNReal).aemeasurable
          g.continuous.aestronglyMeasurable).symm

/-- Occupation is integrable before any martingale identity is known. -/
theorem gantert_integrable_occupation (g : Vec d →ᵇ ℝ) (x : Vec d) (T : ℝ≥0) :
    Integrable (fun γ => ∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) (R.pathLaw x) := by
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let H : Path d × ℝ → ℝ := fun p => g (p.1 p.2.toNNReal)
  have hH : Measurable H := by
    apply g.continuous.measurable.comp
    exact (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hint : Integrable H ((R.pathLaw x).prod ν) :=
    gantert_integrable_bounded _ hH ‖g‖ (fun p => g.norm_coe_le_norm _)
  simpa only [intervalIntegral.integral_of_le T.coe_nonneg] using hint.integral_prod_left

/-- The actual compensated compact test is integrable at every start without
inserting a martingale-problem premise. -/
theorem gantert_integrable_compensatedTest (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : Vec d) (T : ℝ≥0) :
    Integrable (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T)
      (R.pathLaw x) := by
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let fB := gantertCompactObservable f hf.continuous hc
  let gB := gantertCompactObservable
    (physicalGenerator (firstCoordinateIndex hd) ω lam f)
    (gantert_contDiff_physicalGenerator _ ω hSmooth lam hf).continuous
    (gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
  have hi (t : ℝ≥0) : Integrable (fun γ : Path d => f (γ t)) (R.pathLaw x) :=
    gantert_integrable_bounded _
      (hf.continuous.comp (continuous_eval_const t)).measurable ‖fB‖
        (fun γ => fB.norm_coe_le_norm (γ t))
  exact ((hi T).sub (hi 0)).sub
    (gantert_integrable_occupation hd Λ hΛ ω hω lam h₀ h₁ R gB x T)

/-- Exact mean of the literal compensated test under the supplied GMP law.
Vanishing of this displayed residual still requires the generator evolution identity. -/
theorem gantert_integral_compensatedTest (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : Vec d) (T : ℝ≥0) :
    (∫ γ, compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T γ
      ∂R.pathLaw x) =
      (∫ y, f y ∂R.transitionKernel T x) - f x -
        ∫ u in (0 : ℝ)..(T : ℝ),
          ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam f y
            ∂R.transitionKernel u.toNNReal x := by
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let fB := gantertCompactObservable f hf.continuous hc
  let gB := gantertCompactObservable
    (physicalGenerator (firstCoordinateIndex hd) ω lam f)
    (gantert_contDiff_physicalGenerator _ ω hSmooth lam hf).continuous
    (gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
  have hi (t : ℝ≥0) : Integrable (fun γ : Path d => f (γ t)) (R.pathLaw x) :=
    gantert_integrable_bounded _
      (hf.continuous.comp (continuous_eval_const t)).measurable ‖fB‖
        (fun γ => fB.norm_coe_le_norm (γ t))
  have he (t : ℝ≥0) : (∫ γ, f (γ t) ∂R.pathLaw x) =
      ∫ y, f y ∂R.transitionKernel t x := by
    rw [← R.pathLaw_endpoint t x]
    exact (integral_map (measurable_pathPosition t).aemeasurable
      hf.continuous.aestronglyMeasurable).symm
  change (∫ γ, (f (γ T) - f (γ 0)) -
    (∫ u in (0 : ℝ)..(T : ℝ), gB (γ u.toNNReal)) ∂R.pathLaw x) = _
  have hisub : Integrable (fun γ : Path d => f (γ T) - f (γ 0)) (R.pathLaw x) :=
    (hi T).sub (hi 0)
  rw [integral_sub hisub
    (gantert_integrable_occupation hd Λ hΛ ω hω lam h₀ h₁ R gB x T),
    integral_sub (hi T) (hi 0), he T, he 0,
    gantert_integral_occupation hd Λ hΛ ω hω lam h₀ h₁ R gB x T,
    R.transitionKernel_zero, ProbabilityTheory.Kernel.id_apply, integral_dirac]
  rfl

end Realization
end EinsteinFull.Work.W5
