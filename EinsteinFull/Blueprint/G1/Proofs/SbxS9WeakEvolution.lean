import EinsteinFull.Blueprint.G1.Proofs.SbxS9RealizationUniqueness
import EinsteinRelation.Correctors.PairedParabolicEquation
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual weighted weak generator pairing and domain-orbit energy.

All graphs below represent the supplied realization's physical L² vectors.
The form retains its Euclidean gradient, full coefficient, and factor `1/2`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal InnerProductSpace Topology

noncomputable section

namespace EinsteinFull.SbxS9WeakEvolution

open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.C8GMP EinsteinFull.SbxS9RealizationUniqueness
open MarkovProcess.Semigroup

variable {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)

include hΛ hω in
/-- Every pair of full force-weighted H¹ graphs has an integrable physical form. -/
theorem physical_mixed_integrable
    (u v : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    Integrable (weightedFormIntegrand ω.1 u v) (physicalReversibleMeasure ω hd lam) := by
  exact (physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω u v).of_measure_le_smul
    ENNReal.ofReal_ne_top (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)

/-- Pointwise subtraction in the full weighted weak-gradient graph. -/
def graphSub (u v : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) where
  value := fun x => u.value x - v.value x
  weakGradient := fun x => u.weakGradient x - v.weakGradient x
  value_memLp := u.value_memLp.sub v.value_memLp
  gradient_memLp := u.gradient_memLp.sub v.gradient_memLp
  distributionalGradient := by
    simpa only [Pi.sub_apply, WithLp.ofLp_sub] using
      Correctors.hasWeakGradient_sub u.distributionalGradient v.distributionalGradient

private theorem dot_matrix_symm (A : Mat d) (hA : A.transpose = A) (u v : Vec d) :
    dot u (A.mulVec v) = dot v (A.mulVec u) := by
  have hu : Matrix.vecMul u A = A.mulVec u := by
    calc
      Matrix.vecMul u A = Matrix.vecMul u A.transpose.transpose := by
        rw [Matrix.transpose_transpose]
      _ = A.transpose.mulVec u := Matrix.vecMul_transpose A.transpose u
      _ = A.mulVec u := by rw [hA]
  rw [show dot u (A.mulVec v) = dotProduct (Matrix.vecMul u A) v from
    Matrix.dotProduct_mulVec u A v, hu]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

include hΛ hω in
/-- Polarization on arbitrary full H¹ graphs, before any generator restriction. -/
theorem physical_energy_polarization
    (u v : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    (physicalH1FormEnergy ω hd lam u + physicalH1FormEnergy ω hd lam v -
      physicalH1FormEnergy ω hd lam (graphSub hd u v)) / 2 =
        ∫ x, weightedFormIntegrand ω.1 u v x ∂physicalReversibleMeasure ω hd lam := by
  have hiu := physical_mixed_integrable hd hΛ (hω := hω) u u
  have hiv := physical_mixed_integrable hd hΛ (hω := hω) v v
  have his := physical_mixed_integrable hd hΛ (hω := hω) (graphSub hd u v) (graphSub hd u v)
  have hp : ∀ x, weightedFormIntegrand ω.1 u u x + weightedFormIntegrand ω.1 v v x -
      weightedFormIntegrand ω.1 (graphSub hd u v) (graphSub hd u v) x =
      2 * weightedFormIntegrand ω.1 u v x := by
    intro x
    have hc := dot_matrix_symm (ω.1 x) (hω.1 x).1
      (WithLp.ofLp (u.weakGradient x)) (WithLp.ofLp (v.weakGradient x))
    unfold weightedFormIntegrand
    simp only [graphSub, Pi.sub_apply, WithLp.ofLp_sub, Matrix.mulVec_sub,
      dot, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib] at ⊢
    change (∑ i, _ * _) = (∑ i, _ * _) at hc
    linarith only [hc]
  have he := integral_congr_ae (ae_of_all (physicalReversibleMeasure ω hd lam) hp)
  change (∫ x, ((weightedFormIntegrand ω.1 u u + weightedFormIntegrand ω.1 v v) -
    weightedFormIntegrand ω.1 (graphSub hd u v) (graphSub hd u v)) x
    ∂physicalReversibleMeasure ω hd lam) = _ at he
  rw [integral_sub' (hiu.add hiv) his, integral_add' hiu hiv, integral_const_mul] at he
  unfold physicalH1FormEnergy
  linarith only [he]

include hω in
/-- A graph representative's quotient value agrees under the physical measure. -/
theorem graph_quotient_value_ae
    (u : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    densityWeightedH1Value (physicalForceWeight hd lam) (Quotient.mk _ u) =ᵐ[
      physicalReversibleMeasure ω hd lam] u.value :=
  (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq u.value_memLp.coeFn_toLp

include hω in
/-- Physical almost-everywhere values determine the actual weak gradients. -/
theorem physical_gradient_congr
    (u v : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (huv : u.value =ᵐ[physicalReversibleMeasure ω hd lam] v.value) :
    u.weakGradient =ᵐ[physicalReversibleMeasure ω hd lam] v.weakGradient := by
  have hv := (Measure.absolutelyContinuous_of_le_smul
    (sourceReducedMeasure_le_physical ω hd lam Λ hω)).ae_eq huv
  have hg := densityWeightedGraph_gradient_ae_of_value_ae (physicalForceWeight hd lam)
    (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) u v hv
  exact (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hg

include hω in
/-- The mixed physical form is independent of both graph representatives. -/
theorem physical_mixed_congr
    (u u' v v' : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] u'.value)
    (hv : v.value =ᵐ[physicalReversibleMeasure ω hd lam] v'.value) :
    (∫ x, weightedFormIntegrand ω.1 u v x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, weightedFormIntegrand ω.1 u' v' x ∂physicalReversibleMeasure ω hd lam := by
  apply integral_congr_ae
  filter_upwards [physical_gradient_congr hd (hω := hω) u u' hu,
    physical_gradient_congr hd (hω := hω) v v' hv] with x hx hy
  simp only [weightedFormIntegrand, hx, hy]

include hΛ hω in
/-- Ellipticity makes the actual physical form energy nonnegative. -/
theorem physical_energy_nonneg
    (u : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    0 ≤ physicalH1FormEnergy ω hd lam u := by
  apply integral_nonneg
  intro x
  have hs : 0 ≤ euclideanSq (WithLp.ofLp (u.weakGradient x)) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have he := ((hω.1 x).2 (WithLp.ofLp (u.weakGradient x))).1
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ((mul_nonneg (inv_nonneg.mpr (by linarith : 0 ≤ Λ)) hs).trans he)

include hΛ hω in
/-- The full anisotropic energy controls the physical Euclidean gradient norm. -/
theorem physical_gradient_energy_le
    (u : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam)) :
    (∫ x, ‖u.weakGradient x‖ ^ 2 ∂physicalReversibleMeasure ω hd lam) ≤
      2 * Λ * physicalH1FormEnergy ω hd lam u := by
  have hgrad := (u.gradient_memLp.of_measure_le_smul ENNReal.ofReal_ne_top
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)
  have hform := physical_mixed_integrable hd hΛ (hω := hω) u u
  have hp : ∀ x, ‖u.weakGradient x‖ ^ 2 ≤ 2 * Λ * weightedFormIntegrand ω.1 u u x := by
    intro x
    have he := ((hω.1 x).2 (WithLp.ofLp (u.weakGradient x))).1
    have hn : euclideanSq (WithLp.ofLp (u.weakGradient x)) = ‖u.weakGradient x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]
    rw [hn] at he
    have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
    have hm := mul_le_mul_of_nonneg_left he hΛ0.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hΛ0), one_mul] at hm
    unfold weightedFormIntegrand
    nlinarith only [hm]
  have he := integral_mono_ae hgrad (hform.const_mul (2 * Λ)) (ae_of_all _ hp)
  rw [integral_const_mul] at he
  exact he

/-- The full actual generator paired with an arbitrary weighted H¹ test.
The test need not belong to the generator domain. -/
theorem actual_generator_weak_pairing
    (f : (actualL2Semigroup hd hΛ R).generatorDomain)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (u v : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam]
      (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
    (hv : v.value =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    -inner ℝ ((actualL2Semigroup hd hΛ R).generator f) g =
      ∫ x, weightedFormIntegrand ω.1 u v x ∂physicalReversibleMeasure ω hd lam := by
  have hs : (graphSub hd u v).value =ᵐ[physicalReversibleMeasure ω hd lam]
      (f - g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) := by
    filter_upwards [hu, hv, Lp.coeFn_sub (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) g]
      with x hx hy hz
    exact (congrArg₂ (· - ·) hx hy).trans hz.symm
  have hf := R.closedForm_value _ (Quotient.mk _ u)
    ((graph_quotient_value_ae hd (hω := hω) u).trans hu) u hu
  have hg := R.closedForm_value _ (Quotient.mk _ v)
    ((graph_quotient_value_ae hd (hω := hω) v).trans hv) v hv
  have hfg := R.closedForm_value _ (Quotient.mk _ (graphSub hd u v))
    ((graph_quotient_value_ae hd (hω := hω) (graphSub hd u v)).trans hs) _ hs
  have hlim := ((hf.add hg).sub hfg).div_const 2
  rw [physical_energy_polarization hd hΛ (hω := hω) u v] at hlim
  apply tendsto_nhds_unique (generator_mixed_tendsto hd hΛ R f g)
  exact hlim.congr (fun t => (kernelL2Action_quotient_polarization hd hΛ R t f g).symm)

/-- Every generator-domain vector has an actual force-weighted graph representative. -/
theorem generator_graph_exists
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    ∃ u : WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam),
      u.value =ᵐ[physicalReversibleMeasure ω hd lam]
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) := by
  obtain ⟨q, hq⟩ := generator_mem_physicalH1 hd hΛ R f
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q
  exact ⟨u, (graph_quotient_value_ae hd (hω := hω) u).symm.trans hq⟩

/-- A selected spatial graph for an actual generator-domain vector. This is only
spatial choice; it makes no claim of joint time-space measurability. -/
def generatorGraph (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) :=
  (generator_graph_exists hd hΛ R f).choose

theorem generatorGraph_value
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    (generatorGraph hd hΛ R f).value =ᵐ[physicalReversibleMeasure ω hd lam]
      (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
  (generator_graph_exists hd hΛ R f).choose_spec

/-- The selected graph's energy equals the actual negative generator pairing. -/
theorem generatorGraph_energy
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    physicalH1FormEnergy ω hd lam (generatorGraph hd hΛ R f) =
      -inner ℝ ((actualL2Semigroup hd hΛ R).generator f)
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
  (actual_generator_weak_pairing hd hΛ R f f _ _
    (generatorGraph_value hd hΛ R f) (generatorGraph_value hd hΛ R f)).symm

/-- The actual semigroup orbit lifted to its invariant full generator domain. -/
def domainOrbit (f : (actualL2Semigroup hd hΛ R).generatorDomain) (t : ℝ≥0) :
    (actualL2Semigroup hd hΛ R).generatorDomain :=
  ⟨actualL2Semigroup hd hΛ R t f,
    (actualL2Semigroup hd hΛ R).operator_mem_generatorDomain f t⟩

/-- The actual physical graph energy along a generator-domain orbit. -/
def orbitEnergy (f : (actualL2Semigroup hd hΛ R).generatorDomain) (t : ℝ) : ℝ :=
  physicalH1FormEnergy ω hd lam
    (generatorGraph hd hΛ R (domainOrbit hd hΛ R f (Real.toNNReal t)))

/-- Energy along the domain orbit is a continuous scalar generator pairing. -/
theorem orbitEnergy_eq
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) (t : ℝ) :
    orbitEnergy hd hΛ R f t =
      -inner ℝ (actualL2Semigroup hd hΛ R (Real.toNNReal t)
        ((actualL2Semigroup hd hΛ R).generator f))
        (actualL2Semigroup hd hΛ R (Real.toNNReal t) f) := by
  unfold orbitEnergy
  rw [generatorGraph_energy]
  exact congrArg (fun z => -inner ℝ z (actualL2Semigroup hd hΛ R (Real.toNNReal t) f))
    ((actualL2Semigroup hd hΛ R).generator_operator f (Real.toNNReal t))

theorem orbitEnergy_continuous
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) :
    Continuous (orbitEnergy hd hΛ R f) := by
  have he : orbitEnergy hd hΛ R f = fun t =>
      -inner ℝ (actualL2Semigroup hd hΛ R (Real.toNNReal t)
        ((actualL2Semigroup hd hΛ R).generator f))
        (actualL2Semigroup hd hΛ R (Real.toNNReal t) f) :=
    funext (orbitEnergy_eq hd hΛ R f)
  rw [he]
  exact (((actualL2Semigroup hd hΛ R).continuous_operator_toNNReal _).inner
    ((actualL2Semigroup hd hΛ R).continuous_operator_toNNReal _)).neg

/-- Dissipation of the physical L² norm square, with the source factor two. -/
theorem orbit_norm_sq_hasDerivAt
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ‖actualL2Semigroup hd hΛ R (Real.toNNReal s) f‖ ^ 2)
      (-2 * orbitEnergy hd hΛ R f t) t := by
  have h := (actualL2Semigroup hd hΛ R).hasDerivAt_operator_toNNReal f ht
  have hi := h.inner ℝ h
  simp only [real_inner_self_eq_norm_sq] at hi
  convert hi using 1
  rw [orbitEnergy_eq, real_inner_comm]
  ring

/-- Exact integrated energy for domain data on every finite interval starting at zero. -/
theorem orbit_energy_identity
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) (T : ℝ≥0) :
    ‖actualL2Semigroup hd hΛ R T f‖ ^ 2 +
      2 * (∫ t in (0 : ℝ)..(T : ℝ), orbitEnergy hd hΛ R f t) =
      ‖(f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖ ^ 2 := by
  have hcont : Continuous (fun t : ℝ =>
      ‖actualL2Semigroup hd hΛ R (Real.toNNReal t) f‖ ^ 2) :=
    ((actualL2Semigroup hd hΛ R).continuous_operator_toNNReal f).norm.pow 2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le T.coe_nonneg
    hcont.continuousOn
    (fun t ht => orbit_norm_sq_hasDerivAt hd hΛ R f ht.1)
    (((orbitEnergy_continuous hd hΛ R f).const_mul (-2)).intervalIntegrable 0 T)
  simp only [intervalIntegral.integral_const_mul, Real.toNNReal_coe,
    Real.toNNReal_zero, StronglyContinuousContractionSemigroup.zero_apply] at he
  linarith only [he]

/-- The spacetime energy bound for domain data, in the actual physical form. -/
theorem orbit_energy_le
    (f : (actualL2Semigroup hd hΛ R).generatorDomain) (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..(T : ℝ), orbitEnergy hd hΛ R f t) ≤
      ‖(f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖ ^ 2 / 2 := by
  have he := orbit_energy_identity hd hΛ R f T
  have hn := sq_nonneg ‖actualL2Semigroup hd hΛ R T f‖
  linarith only [he, hn]

/-- Differences of domain data obey the same integrated energy estimate. -/
theorem orbit_difference_energy_le
    (f g : (actualL2Semigroup hd hΛ R).generatorDomain) (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..(T : ℝ), orbitEnergy hd hΛ R (f - g) t) ≤
      ‖(f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) -
        (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))‖ ^ 2 / 2 :=
  orbit_energy_le hd hΛ R (f - g) T

/-- A uniform-in-time value estimate for approximation by domain vectors. -/
theorem orbit_difference_norm_le
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) :
    ‖actualL2Semigroup hd hΛ R t f - actualL2Semigroup hd hΛ R t g‖ ≤ ‖f - g‖ := by
  rw [← map_sub]
  exact (actualL2Semigroup hd hΛ R).norm_apply_le t (f - g)

/-- Every physical L² vector admits approximation by actual generator-domain vectors. -/
theorem exists_domain_approximation
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∃ u : ℕ → (actualL2Semigroup hd hΛ R).generatorDomain,
      Tendsto (fun n => (u n : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) atTop (𝓝 f) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp
    ((actualL2Semigroup hd hΛ R).dense_generatorDomain f)
  exact ⟨fun n => ⟨u n, hu n⟩, hlim⟩

/-- L² approximation propagates uniformly over all nonnegative times. -/
theorem domain_approximation_uniform
    (u : ℕ → (actualL2Semigroup hd hΛ R).generatorDomain)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hu : Tendsto (fun n => (u n : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) atTop (𝓝 f)) :
    TendstoUniformly (fun n t => actualL2Semigroup hd hΛ R t (u n))
      (fun t => actualL2Semigroup hd hΛ R t f) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hu ε hε] with n hn t
  exact ((actualL2Semigroup hd hΛ R).dist_apply_le t f (u n)).trans_lt
    (by simpa only [dist_comm] using hn)

/-- Two domain approximations of the same L² vector have vanishing spacetime energy difference. -/
theorem domain_approximation_energy
    (u v : ℕ → (actualL2Semigroup hd hΛ R).generatorDomain)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hu : Tendsto (fun n => (u n : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) atTop (𝓝 f))
    (hv : Tendsto (fun n => (v n : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) atTop (𝓝 f))
    (T : ℝ≥0) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(T : ℝ),
      orbitEnergy hd hΛ R (u n - v n) t) atTop (𝓝 0) := by
  have hlim := (((hu.sub hv).norm).pow 2).div_const 2
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at hlim
  apply squeeze_zero (fun n => ?_) (fun n => orbit_difference_energy_le hd hΛ R (u n) (v n) T) hlim
  apply intervalIntegral.integral_nonneg_of_forall T.coe_nonneg
  intro t
  exact physical_energy_nonneg hd hΛ (hω := hω)
    (generatorGraph hd hΛ R (domainOrbit hd hΛ R (u n - v n) (Real.toNNReal t)))

#print axioms dot_matrix_symm

end EinsteinFull.SbxS9WeakEvolution

#print axioms EinsteinFull.SbxS9WeakEvolution.physical_mixed_integrable
#print axioms EinsteinFull.SbxS9WeakEvolution.graphSub
#print axioms EinsteinFull.SbxS9WeakEvolution.physical_energy_polarization
#print axioms EinsteinFull.SbxS9WeakEvolution.graph_quotient_value_ae
#print axioms EinsteinFull.SbxS9WeakEvolution.physical_gradient_congr
#print axioms EinsteinFull.SbxS9WeakEvolution.physical_mixed_congr
#print axioms EinsteinFull.SbxS9WeakEvolution.physical_energy_nonneg
#print axioms EinsteinFull.SbxS9WeakEvolution.physical_gradient_energy_le
#print axioms EinsteinFull.SbxS9WeakEvolution.actual_generator_weak_pairing
#print axioms EinsteinFull.SbxS9WeakEvolution.generator_graph_exists
#print axioms EinsteinFull.SbxS9WeakEvolution.generatorGraph
#print axioms EinsteinFull.SbxS9WeakEvolution.generatorGraph_value
#print axioms EinsteinFull.SbxS9WeakEvolution.generatorGraph_energy
#print axioms EinsteinFull.SbxS9WeakEvolution.domainOrbit
#print axioms EinsteinFull.SbxS9WeakEvolution.orbitEnergy
#print axioms EinsteinFull.SbxS9WeakEvolution.orbitEnergy_eq
#print axioms EinsteinFull.SbxS9WeakEvolution.orbitEnergy_continuous
#print axioms EinsteinFull.SbxS9WeakEvolution.orbit_norm_sq_hasDerivAt
#print axioms EinsteinFull.SbxS9WeakEvolution.orbit_energy_identity
#print axioms EinsteinFull.SbxS9WeakEvolution.orbit_energy_le
#print axioms EinsteinFull.SbxS9WeakEvolution.orbit_difference_energy_le
#print axioms EinsteinFull.SbxS9WeakEvolution.orbit_difference_norm_le
#print axioms EinsteinFull.SbxS9WeakEvolution.exists_domain_approximation
#print axioms EinsteinFull.SbxS9WeakEvolution.domain_approximation_uniform
#print axioms EinsteinFull.SbxS9WeakEvolution.domain_approximation_energy
#lint
