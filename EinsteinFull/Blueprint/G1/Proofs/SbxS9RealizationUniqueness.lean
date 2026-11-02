import EinsteinFull.Blueprint.G1.Proofs.SbxS4RemainderMoment
import MarkovProcess.Semigroup.Resolvent
import MarkovProcess.Semigroup.GeneratorUniqueness
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Tactic.Linter

/-!
# The full L² generator of an actual fixed-environment realization

The action below is the actual transition-kernel action on the physical
reversible measure. Its full generator domain embeds in the source weighted
H¹ domain, and its diagonal generator pairing is the actual closed-form energy.
The common full closed form then identifies the actual resolvents and semigroups
of any two realizations. Finite-measure indicator tests and a countable
generating algebra identify their transition kernels almost everywhere at each
time. Upgrading entrance laws at every start remains a separate obligation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal InnerProductSpace Topology

noncomputable section

namespace EinsteinFull.SbxS9RealizationUniqueness

open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.C8GMP
open MarkovProcess.Semigroup

variable {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)

/-- The genuine transition action as a bounded linear operator. Linearity follows
from actual detailed balance, without a smoothness or locality assumption. -/
def actualL2Operator (t : ℝ≥0) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  LinearMap.mkContinuous
    { toFun := R.kernelL2Action hd hΛ t
      map_add' := fun f g => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_add_left,
          inner_add_left, ← kernelL2Action_symmetric hd hΛ R,
          ← kernelL2Action_symmetric hd hΛ R]
      map_smul' := fun c f => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_smul_left,
          inner_smul_left, ← kernelL2Action_symmetric hd hΛ R]
        simp }
    1 (fun f => by
      change ‖R.kernelL2Action hd hΛ t f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact R.kernelL2Action_norm_le hd hΛ t f)

theorem actualL2Operator_zero :
    actualL2Operator hd hΛ R 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel 0) := R.transitionKernel_isMarkovKernel 0
  have hk := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ 0) f
  change R.kernelL2Action hd hΛ 0 f =ᵐ[_] _ at hk
  filter_upwards [hk] with x hx
  change R.kernelL2Action hd hΛ 0 f x = f x
  rw [hx]
  simp only [WeightedKernelL2.kernelIntegral, R.transitionKernel_zero,
    Kernel.id_apply, integral_dirac]

theorem actualL2Operator_add (s t : ℝ≥0) :
    actualL2Operator hd hΛ R (s + t) =
      (actualL2Operator hd hΛ R s).comp (actualL2Operator hd hΛ R t) := by
  apply ContinuousLinearMap.ext
  intro f
  change R.kernelL2Action hd hΛ (s + t) f =
    R.kernelL2Action hd hΛ s (R.kernelL2Action hd hΛ t f)
  exact kernelL2Action_add hd hΛ R s t f

theorem actualL2Operator_norm_le (t : ℝ≥0) :
    ‖actualL2Operator hd hΛ R t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖R.kernelL2Action hd hΛ t f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using R.kernelL2Action_norm_le hd hΛ t f

/-- The actual reversible physical-L² contraction semigroup, with continuity
deduced from the realization's full closed-form fields. -/
def actualL2Semigroup :
    StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) where
  operator := actualL2Operator hd hΛ R
  operator_zero := actualL2Operator_zero hd hΛ R
  operator_add := actualL2Operator_add hd hΛ R
  opNorm_le_one := actualL2Operator_norm_le hd hΛ R
  continuous_orbit := SbxS4Dynkin.kernelL2Action_continuous hd hΛ R

/-- The bundled semigroup acts by the original kernel integration. -/
theorem actualL2Semigroup_apply (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    actualL2Semigroup hd hΛ R t f = R.kernelL2Action hd hΛ t f := rfl

/-- Difference quotients of a full generator-domain vector are uniformly
bounded over every positive time, including times away from zero. -/
theorem generator_differenceQuotient_bounded
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      ‖(actualL2Semigroup hd hΛ R).differenceQuotient f t‖ ≤ C := by
  let S := actualL2Semigroup hd hΛ R
  let g := S.generator f
  have hg := S.tendsto_generator f
  obtain ⟨δ, hδ, ht⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hg) 1 zero_lt_one
  refine ⟨max (‖g‖ + 1) (δ⁻¹ * (2 * ‖(f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖)), fun t ht0 => ?_⟩
  by_cases hsmall : (t : ℝ) < δ
  · have hh := ht ht0 (by
      change |(t : ℝ) - 0| < δ
      simpa only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ t from t.property)] using hsmall)
    have hn := norm_le_norm_add_norm_sub g (S.differenceQuotient f t)
    rw [norm_sub_rev g] at hn
    rw [dist_eq_norm] at hh
    exact (by linarith : ‖S.differenceQuotient f t‖ ≤ ‖g‖ + 1).trans
      (le_max_left _ _)
  · have htpos : 0 < (t : ℝ) := ht0
    have hinv : (t : ℝ)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (le_of_not_gt hsmall)
    have hn : ‖S t f - f‖ ≤ 2 * ‖(f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖ :=
      (norm_sub_le _ _).trans (by linarith [S.norm_apply_le t f])
    rw [StronglyContinuousContractionSemigroup.differenceQuotient_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    exact (mul_le_mul hinv hn (norm_nonneg _) (le_of_lt (inv_pos.mpr hδ))).trans
      (le_max_right _ _)

/-- Every vector of the actual full generator domain belongs to the literal
physical weighted H¹ domain. No compact-test core assumption is used. -/
theorem generator_mem_physicalH1
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    physicalH1Member ω hd lam (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) := by
  obtain ⟨C, hC⟩ := generator_differenceQuotient_bounded hd hΛ R f
  apply (R.closedForm_domain (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (Lp.memLp _)).mp
  refine ⟨C * ‖(f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖, fun t ht => ?_⟩
  rw [semigroupFormDifferenceQuotient_eq_inner hd hΛ R]
  have he : (1 / (t : ℝ)) *
      inner ℝ ((f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - R.kernelL2Action hd hΛ t f) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =
      -inner ℝ ((actualL2Semigroup hd hΛ R).differenceQuotient f t)
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) := by
    rw [StronglyContinuousContractionSemigroup.differenceQuotient_apply]
    simp only [actualL2Semigroup_apply, real_inner_smul_left, inner_sub_left, one_div]
    ring
  rw [he]
  exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _)))

/-- On the entire generator domain, the quadratic form converges to the
negative actual generator pairing. -/
theorem generator_form_tendsto
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      R.transitionKernel t (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (-inner ℝ ((actualL2Semigroup hd hΛ R).generator f) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))) := by
  have h := (((actualL2Semigroup hd hΛ R).tendsto_generator f).inner
    (𝕜 := ℝ) (tendsto_const_nhds (x := (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))))).neg
  apply h.congr'
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [semigroupFormDifferenceQuotient_eq_inner hd hΛ R,
      StronglyContinuousContractionSemigroup.differenceQuotient_apply]
    simp only [actualL2Semigroup_apply, real_inner_smul_left, inner_sub_left, one_div]
    ring)

/-- Any actual H¹ representative of a full generator-domain vector has the
source energy given by its negative generator pairing. -/
theorem generator_energy_eq
    (f : (actualL2Semigroup hd hΛ R).generatorDomain)
    (q : DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[
      physicalReversibleMeasure ω hd lam] (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
    (u : WeightedSobolevGraph
      (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) :
    physicalH1FormEnergy ω hd lam u =
      -inner ℝ ((actualL2Semigroup hd hΛ R).generator f) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) := by
  exact tendsto_nhds_unique (R.closedForm_value _ q hq u hu)
    (generator_form_tendsto hd hΛ R f)

/-- Every actual positive-shift resolvent value belongs to physical weighted H¹.
The resolvent is constructed from the actual semigroup, not supplied as an input. -/
theorem resolvent_mem_physicalH1 (μ : PositiveShift)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalH1Member ω hd lam ((actualL2Semigroup hd hΛ R).resolvent μ f) :=
  generator_mem_physicalH1 hd hΛ R
    ⟨_, (actualL2Semigroup hd hΛ R).resolvent_mem_generatorDomain μ f⟩

/-- Closed-form values agree between two actual realizations on the entire
full generator domain of either realization. -/
theorem generator_form_tendsto_other
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      R'.transitionKernel t (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (-inner ℝ ((actualL2Semigroup hd hΛ R).generator f)
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))) := by
  obtain ⟨q, hq⟩ := generator_mem_physicalH1 hd hΛ R f
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q
  have hvalue : densityWeightedH1Value (physicalForceWeight hd lam)
      (Quotient.mk _ u) =ᵐ[physicalReversibleMeasure ω hd lam] u.value := by
    exact (Measure.absolutelyContinuous_of_le_smul
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq
      u.value_memLp.coeFn_toLp
  have hu := hvalue.symm.trans hq
  have he := generator_energy_eq hd hΛ R f (Quotient.mk _ u) hq u hu
  rw [← he]
  exact R'.closedForm_value _ (Quotient.mk _ u) hq u hu

/-- A full generator-domain vector may be paired with any physical L² vector. -/
theorem generator_mixed_tendsto
    (f : (actualL2Semigroup hd hΛ R).generatorDomain)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) * inner ℝ
      ((f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - R.kernelL2Action hd hΛ t f) g)
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (-inner ℝ ((actualL2Semigroup hd hΛ R).generator f) g)) := by
  have h := (((actualL2Semigroup hd hΛ R).tendsto_generator f).inner
    (𝕜 := ℝ) (tendsto_const_nhds (x := g))).neg
  apply h.congr'
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [StronglyContinuousContractionSemigroup.differenceQuotient_apply]
    simp only [actualL2Semigroup_apply, real_inner_smul_left, inner_sub_left, one_div]
    ring)

/-- Contraction makes every actual quadratic form quotient nonnegative. -/
theorem formQuotient_nonneg (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f := by
  rw [semigroupFormDifferenceQuotient_eq_inner hd hΛ R]
  apply mul_nonneg (div_nonneg zero_le_one t.property)
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  apply sub_nonneg.mpr
  calc
    inner ℝ (R.kernelL2Action hd hΛ t f) f ≤
        ‖R.kernelL2Action hd hΛ t f‖ * ‖f‖ := real_inner_le_norm _ _
    _ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right
      (R.kernelL2Action_norm_le hd hΛ t f) (norm_nonneg _)
    _ = ‖f‖ ^ 2 := (pow_two _).symm

/-- Comparing resolvents only uses the full closed-form diagonal agreement and
actual reversibility; no compact-test core or uniqueness input is imposed. -/
theorem resolvent_comparison_nonneg
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (μ : PositiveShift) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    let U := (actualL2Semigroup hd hΛ R).resolvent μ f
    let V := (actualL2Semigroup hd hΛ R').resolvent μ f
    0 ≤ -inner ℝ ((μ : ℝ) • U - f) U - inner ℝ ((μ : ℝ) • V - f) V +
      2 * inner ℝ ((μ : ℝ) • U - f) V := by
  let S := actualL2Semigroup hd hΛ R
  let T := actualL2Semigroup hd hΛ R'
  let U := S.resolvent μ f
  let V := T.resolvent μ f
  let u : S.generatorDomain := ⟨U, S.resolvent_mem_generatorDomain μ f⟩
  let v : T.generatorDomain := ⟨V, T.resolvent_mem_generatorDomain μ f⟩
  have hU := generator_form_tendsto hd hΛ R u
  have hV := generator_form_tendsto_other hd hΛ R' R v
  have hUV := generator_mixed_tendsto hd hΛ R u V
  have hlim := (hU.add hV).sub (hUV.const_mul 2)
  change Tendsto _ _ (𝓝 (-inner ℝ (S.generator u) U + -inner ℝ (T.generator v) V -
    2 * -inner ℝ (S.generator u) V)) at hlim
  have heq : -inner ℝ (S.generator u) U + -inner ℝ (T.generator v) V -
      2 * -inner ℝ (S.generator u) V =
      -inner ℝ (S.generator u) U - inner ℝ (T.generator v) V +
        2 * inner ℝ (S.generator u) V := by ring
  rw [heq] at hlim
  have hdiff : Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      R.transitionKernel t (U - V : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (-inner ℝ (S.generator u) U - inner ℝ (T.generator v) V +
        2 * inner ℝ (S.generator u) V)) := by
    apply hlim.congr'
    apply Eventually.of_forall
    intro t
    have hp := kernelL2Action_quotient_polarization hd hΛ R t U V
    change semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t U +
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t V -
      2 * ((1 / (t : ℝ)) * inner ℝ (U - R.kernelL2Action hd hΛ t U) V) = _
    linarith
  have hn := ge_of_tendsto hdiff
    (Eventually.of_forall (fun t => formQuotient_nonneg hd hΛ R t (U - V)))
  have hgu : S.generator u = (μ : ℝ) • U - f := S.generator_resolvent μ f
  have hgv : T.generator v = (μ : ℝ) • V - f := T.generator_resolvent μ f
  simpa only [hgu, hgv] using hn

/-- Two actual realizations of the same nonsmooth environment have identical
physical L² resolvents. The actual full closed form discharges uniqueness. -/
theorem actualL2Resolvent_eq
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (μ : PositiveShift) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (actualL2Semigroup hd hΛ R).resolvent μ f =
      (actualL2Semigroup hd hΛ R').resolvent μ f := by
  let U := (actualL2Semigroup hd hΛ R).resolvent μ f
  let V := (actualL2Semigroup hd hΛ R').resolvent μ f
  have huv := resolvent_comparison_nonneg hd hΛ R R' μ f
  have hvu := resolvent_comparison_nonneg hd hΛ R' R μ f
  change 0 ≤ -inner ℝ ((μ : ℝ) • U - f) U - inner ℝ ((μ : ℝ) • V - f) V +
    2 * inner ℝ ((μ : ℝ) • U - f) V at huv
  change 0 ≤ -inner ℝ ((μ : ℝ) • V - f) V - inner ℝ ((μ : ℝ) • U - f) U +
    2 * inner ℝ ((μ : ℝ) • V - f) U at hvu
  simp only [inner_sub_left, real_inner_smul_left] at huv hvu
  rw [real_inner_comm U V] at hvu
  have hsq : ‖U - V‖ ^ 2 = inner ℝ U U - 2 * inner ℝ U V + inner ℝ V V := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm U V]
    ring
  have hle : (μ : ℝ) * ‖U - V‖ ^ 2 ≤ 0 := by
    rw [hsq]
    linarith
  have hz : ‖U - V‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hle μ.property) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The entire generator graphs agree, hence the actual physical L² semigroups
agree for two realizations of the same nonsmooth environment. -/
theorem actualL2Semigroup_eq
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    actualL2Semigroup hd hΛ R = actualL2Semigroup hd hΛ R' := by
  let S := actualL2Semigroup hd hΛ R
  let T := actualL2Semigroup hd hΛ R'
  let μ : PositiveShift := ⟨(1 : ℝ), by norm_num [PositiveShift]⟩
  have hres : S.resolvent μ = T.resolvent μ := by
    apply ContinuousLinearMap.ext
    intro f
    exact actualL2Resolvent_eq hd hΛ R R' μ f
  have hdom : S.generatorDomain = T.generatorDomain := by
    apply SetLike.coe_injective
    rw [S.generatorDomain_eq_range_resolvent μ, T.generatorDomain_eq_range_resolvent μ,
      hres]
  apply S.ext_of_generator T hdom
  intro f hf hg
  have hrange : f ∈ Set.range (S.resolvent μ) := by
    rw [← S.generatorDomain_eq_range_resolvent μ]
    exact hf
  obtain ⟨x, hx⟩ := hrange
  have hy : T.resolvent μ x = f := by rw [← hres]; exact hx
  rw [S.generator_eq_of_resolvent_eq μ hf hx, T.generator_eq_of_resolvent_eq μ hg hy]

/-- Actual transition integration agrees in physical L² at every time. This is
an almost-everywhere action statement, before the all-start entrance upgrade. -/
theorem kernelL2Action_eq
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    R.kernelL2Action hd hΛ t f = R'.kernelL2Action hd hΛ t f := by
  exact congrArg (fun S : StronglyContinuousContractionSemigroup
    (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) => S t f)
    (actualL2Semigroup_eq hd hΛ R R')

/-- Kernel integrals of each physical L² function agree almost everywhere.
The exceptional set here may depend on the test function and time. -/
theorem transition_integral_eq_ae
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    (fun x => ∫ y, f y ∂R.transitionKernel t x) =ᵐ[physicalReversibleMeasure ω hd lam]
      (fun x => ∫ y, f y ∂R'.transitionKernel t x) := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  let : IsMarkovKernel (R'.transitionKernel t) := R'.transitionKernel_isMarkovKernel t
  let F := hf.toLp f
  have hR := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ t) F
  have hR' := WeightedKernelL2.kernelIntegralL2_coe
    (R'.transitionKernel_invariant hd hΛ t) F
  have hc := WeightedKernelL2.kernelIntegral_ae_congr
    (R.transitionKernel_invariant hd hΛ t) hf.coeFn_toLp
  have hc' := WeightedKernelL2.kernelIntegral_ae_congr
    (R'.transitionKernel_invariant hd hΛ t) hf.coeFn_toLp
  change R.kernelL2Action hd hΛ t F =ᵐ[_] _ at hR
  change R'.kernelL2Action hd hΛ t F =ᵐ[_] _ at hR'
  have he := Lp.ext_iff.mp (kernelL2Action_eq hd hΛ R R' t F)
  exact hc.symm.trans (hR.symm.trans (he.trans (hR'.trans hc')))


/-- The actual transition kernels agree on each measurable set almost everywhere.
Finite-measure truncations make their indicator tests physical L² functions. -/
theorem transition_apply_eq_ae
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (s : Set (Vec d)) (hs : MeasurableSet s) :
    (fun x => R.transitionKernel t x s) =ᵐ[physicalReversibleMeasure ω hd lam]
      (fun x => R'.transitionKernel t x s) := by
  let μ := physicalReversibleMeasure ω hd lam
  let : SigmaFinite μ :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  let : IsMarkovKernel (R'.transitionKernel t) := R'.transitionKernel_isMarkovKernel t
  have htrunc (n : ℕ) :
      (fun x => R.transitionKernel t x (s ∩ spanningSets μ n)) =ᵐ[μ]
        (fun x => R'.transitionKernel t x (s ∩ spanningSets μ n)) := by
    have hsn := hs.inter (measurableSet_spanningSets μ n)
    have hf : MemLp ((s ∩ spanningSets μ n).indicator (fun _ => (1 : ℝ))) 2 μ :=
      memLp_indicator_const 2 hsn 1 (Or.inr (ne_of_lt
        (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (measure_spanningSets_lt_top μ n))))
    have he := transition_integral_eq_ae hd hΛ R R' t _ hf
    filter_upwards [he] with x hx
    simp only [integral_indicator_const (1 : ℝ) hsn, smul_eq_mul, mul_one] at hx
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hx
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ,
      R.transitionKernel t x (s ∩ spanningSets μ n) =
        R'.transitionKernel t x (s ∩ spanningSets μ n) := ae_all_iff.mpr htrunc
  have hm : Monotone (fun n => s ∩ spanningSets μ n) :=
    fun i j hij => Set.inter_subset_inter_right s (spanningSets_mono hij)
  have hu : (⋃ n : ℕ, s ∩ spanningSets μ n) = s := by
    rw [← Set.inter_iUnion, iUnion_spanningSets μ, Set.inter_univ]
  filter_upwards [hall] with x hx
  calc
    R.transitionKernel t x s = ⨆ n, R.transitionKernel t x (s ∩ spanningSets μ n) := by
      simpa only [hu] using (hm.measure_iUnion (μ := R.transitionKernel t x))
    _ = ⨆ n, R'.transitionKernel t x (s ∩ spanningSets μ n) := iSup_congr hx
    _ = R'.transitionKernel t x s := by
      rw [← hm.measure_iUnion, hu]

/-- A countable generating algebra yields a common exceptional set for the
entire actual transition measure at each time. No all-start regularity is used. -/
theorem transitionKernel_eq_ae
    (R' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) :
    R.transitionKernel t =ᵐ[physicalReversibleMeasure ω hd lam] R'.transitionKernel t := by
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  let : IsMarkovKernel (R'.transitionKernel t) := R'.transitionKernel_isMarkovKernel t
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet (Vec d))
  have hC : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  have hgen : (inferInstance : MeasurableSpace (Vec d)) = MeasurableSpace.generateFrom C := by
    simp only [C, generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
  have hall : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∀ s ∈ C, R.transitionKernel t x s = R'.transitionKernel t x s := by
    apply (ae_ball_iff hC).mpr
    intro s hs
    apply transition_apply_eq_ae hd hΛ R R' t s
    exact hgen.ge s (MeasurableSpace.measurableSet_generateFrom hs)
  filter_upwards [hall] with x hx
  exact Measure.ext_of_generateFrom_of_iUnion C (fun _ : ℕ => Set.univ) hgen
    (fun s hs u hu _ => isSetAlgebra_generateSetAlgebra.inter_mem hs hu)
    (by simp only [Set.iUnion_const])
    (fun _ => isSetAlgebra_generateSetAlgebra.univ_mem)
    (fun _ => measure_ne_top _ _) hx

end EinsteinFull.SbxS9RealizationUniqueness

#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Operator
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Operator_zero
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Operator_add
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Operator_norm_le
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Semigroup
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Semigroup_apply
#print axioms EinsteinFull.SbxS9RealizationUniqueness.generator_differenceQuotient_bounded
#print axioms EinsteinFull.SbxS9RealizationUniqueness.generator_mem_physicalH1
#print axioms EinsteinFull.SbxS9RealizationUniqueness.generator_form_tendsto
#print axioms EinsteinFull.SbxS9RealizationUniqueness.generator_energy_eq
#print axioms EinsteinFull.SbxS9RealizationUniqueness.resolvent_mem_physicalH1
#print axioms EinsteinFull.SbxS9RealizationUniqueness.generator_form_tendsto_other
#print axioms EinsteinFull.SbxS9RealizationUniqueness.generator_mixed_tendsto
#print axioms EinsteinFull.SbxS9RealizationUniqueness.formQuotient_nonneg
#print axioms EinsteinFull.SbxS9RealizationUniqueness.resolvent_comparison_nonneg
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Resolvent_eq
#print axioms EinsteinFull.SbxS9RealizationUniqueness.actualL2Semigroup_eq
#print axioms EinsteinFull.SbxS9RealizationUniqueness.kernelL2Action_eq
#print axioms EinsteinFull.SbxS9RealizationUniqueness.transition_integral_eq_ae
#print axioms EinsteinFull.SbxS9RealizationUniqueness.transition_apply_eq_ae
#print axioms EinsteinFull.SbxS9RealizationUniqueness.transitionKernel_eq_ae
#lint
