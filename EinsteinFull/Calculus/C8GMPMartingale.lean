import EinsteinFull.Work.W5.GantertWeightedFormDynkinProof
import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import EinsteinRelation.SpatialDirichlet.CanonicalPhysicalFormAgreementSupport
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Compact smooth tests in the actual GMP closed form.

The form limit below is a prerequisite for generator identification. It does
not assert a Dynkin identity or a martingale problem for the supplied path law.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal ProbabilityTheory
noncomputable section
namespace EinsteinFull.C8GMP
open EinsteinRelation
open EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Work.W5

/-- Rectangle detailed balance determines the full joint transition measure. -/
theorem reversible_compProd_swap {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K μ) :
    (μ ⊗ₘ K).map Prod.swap = μ ⊗ₘ K := by
  symm
  apply Measure.ext_of_generateFrom_of_iUnion _
    (fun n => spanningSets μ n ×ˢ Set.univ)
    generateFrom_prod.symm isPiSystem_prod
  · rw [← Set.iUnion_prod_const, iUnion_spanningSets, Set.univ_prod_univ]
  · intro n
    exact ⟨spanningSets μ n, measurableSet_spanningSets μ n,
      Set.univ, MeasurableSet.univ, rfl⟩
  · intro n
    rw [Measure.compProd_apply_prod (measurableSet_spanningSets μ n)
      MeasurableSet.univ]
    simpa using (measure_spanningSets_lt_top μ n).ne
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    rw [Measure.map_apply measurable_swap (hs.prod ht), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod ht hs]
    exact hrev hs ht

/-- Detailed balance exchanges arbitrary square-integrable kernel pairings. -/
theorem reversible_kernel_pairing {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (K : Kernel α α) [IsMarkovKernel K]
    (hrev : Kernel.IsReversible K μ) (f g : Lp ℝ 2 μ) :
    (∫ x, f x * (∫ y, g y ∂K x) ∂μ) =
      ∫ x, g x * (∫ y, f y ∂K x) ∂μ := by
  have hfst : MeasurePreserving Prod.fst (μ ⊗ₘ K) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ K⟩
  have hsnd : MeasurePreserving Prod.snd (μ ⊗ₘ K) μ := by
    refine ⟨measurable_snd, ?_⟩
    exact (Measure.snd_compProd μ K).trans hrev.invariant.def
  have hfg : Integrable (fun z : α × α => f z.1 * g z.2) (μ ⊗ₘ K) :=
    ((Lp.memLp f).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp g).comp_measurePreserving hsnd)
  have hgf : Integrable (fun z : α × α => g z.1 * f z.2) (μ ⊗ₘ K) :=
    ((Lp.memLp g).comp_measurePreserving hfst).integrable_mul
      ((Lp.memLp f).comp_measurePreserving hsnd)
  calc
    _ = ∫ z, f z.1 * g z.2 ∂(μ ⊗ₘ K) := by
      rw [Measure.integral_compProd hfg]
      simp only [integral_const_mul]
    _ = ∫ z, g z.1 * f z.2 ∂(μ ⊗ₘ K) := by
      have hswap := integral_map_of_stronglyMeasurable (μ := μ ⊗ₘ K)
        measurable_swap
        (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).mul
          ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))
      rw [reversible_compProd_swap μ K hrev] at hswap
      simpa only [Pi.mul_apply, Function.comp_apply, Prod.swap, mul_comm] using hswap
    _ = _ := by
      rw [Measure.integral_compProd hgf]
      simp only [integral_const_mul]

/-- The actual reversible transition action is symmetric on physical L². -/
theorem kernelL2Action_symmetric {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    inner ℝ f (R.kernelL2Action hd hΛ t g) =
      inner ℝ (R.kernelL2Action hd hΛ t f) g := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  have hrev : Kernel.IsReversible (R.transitionKernel t)
      (physicalReversibleMeasure ω hd lam) := by
    intro A B hA hB
    exact R.transitionKernel_reversible t A B hA hB
  have hf := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ t) f
  have hg := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ t) g
  change R.kernelL2Action hd hΛ t f =ᵐ[_] _ at hf
  change R.kernelL2Action hd hΛ t g =ᵐ[_] _ at hg
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, f x * (∫ y, g y ∂R.transitionKernel t x)
        ∂physicalReversibleMeasure ω hd lam := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      simp [hx, RCLike.inner_apply, WeightedKernelL2.kernelIntegral, mul_comm]
    _ = ∫ x, g x * (∫ y, f y ∂R.transitionKernel t x)
        ∂physicalReversibleMeasure ω hd lam :=
      reversible_kernel_pairing _ _ hrev f g
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      simp [hx, RCLike.inner_apply, WeightedKernelL2.kernelIntegral]

/-- Chapman–Kolmogorov holds for the actual physical L² action. -/
theorem kernelL2Action_add {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (s t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    R.kernelL2Action hd hΛ (s + t) f =
      R.kernelL2Action hd hΛ s (R.kernelL2Action hd hΛ t f) := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel s) := R.transitionKernel_isMarkovKernel s
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  let : IsMarkovKernel (R.transitionKernel (s + t)) :=
    R.transitionKernel_isMarkovKernel (s + t)
  exact WeightedKernelL2.kernelIntegralL2_semigroup_step
    (fun u => R.transitionKernel_invariant hd hΛ u) (R.transitionKernel_add s t) f

/-- Half-time factorization makes the reversible transition action positive. -/
theorem kernelL2Action_inner_nonneg {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ inner ℝ (R.kernelL2Action hd hΛ t f) f := by
  conv_rhs => rw [← add_halves t, kernelL2Action_add hd hΛ R]
  rw [← kernelL2Action_symmetric hd hΛ R (t / 2)]
  exact real_inner_self_nonneg

/-- The source quadratic quotient is literally the actual physical L² quotient. -/
theorem semigroupFormDifferenceQuotient_eq_inner {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f =
      (1 / (t : ℝ)) * inner ℝ (f - R.kernelL2Action hd hΛ t f) f := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  have hk := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ t) f
  change R.kernelL2Action hd hΛ t f =ᵐ[_] _ at hk
  unfold semigroupFormDifferenceQuotient
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hk, Lp.coeFn_sub f (R.kernelL2Action hd hΛ t f)] with x hx hs
  change (f x - ∫ y, f y ∂R.transitionKernel t x) * f x =
    inner ℝ ((f - R.kernelL2Action hd hΛ t f) x) (f x)
  rw [hs]
  simp [Pi.sub_apply, hx, RCLike.inner_apply, WeightedKernelL2.kernelIntegral, mul_comm]

/-- Reversibility polarizes the actual quotient without a resolvent assumption. -/
theorem kernelL2Action_quotient_polarization {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (1 / (t : ℝ)) * inner ℝ (f - R.kernelL2Action hd hΛ t f) g =
      (semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f +
        semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t g -
        semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t
          (f - g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) / 2 := by
  rw [semigroupFormDifferenceQuotient_eq_inner hd hΛ R,
    semigroupFormDifferenceQuotient_eq_inner hd hΛ R,
    semigroupFormDifferenceQuotient_eq_inner hd hΛ R,
    R.kernelL2Action_sub hd hΛ]
  simp only [inner_sub_left, inner_sub_right]
  have hcross : inner ℝ (R.kernelL2Action hd hΛ t g) f =
      inner ℝ (R.kernelL2Action hd hΛ t f) g := by
    rw [← kernelL2Action_symmetric hd hΛ R t g f, real_inner_comm]
  rw [real_inner_comm g f, hcross]
  ring

/-- Passing between the full graph and its quotient preserves the actual value. -/
theorem fullDomain_quotient_value_ae {d : ℕ} (hd : 2 ≤ d)
    (Λ : ℝ) (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (physicalForceWeight hd lam)
      ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm u)
      =ᵐ[physicalReversibleMeasure ω hd lam]
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value := by
  let ρ := sourceReducedDensity hd lam
  let E := densityWeightedH1GraphEquiv ρ
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
  let q := E.symm u
  let g := densityWeightedH1SpaceRepresentative ρ
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  have hEq : E q = u := E.apply_symm_apply u
  have hp := physicalH1Representative_pair_eq_quotient_pair hd lam q
  have hLp : g.value_memLp.toLp g.value = densityWeightedH1Value ρ q := by
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value_memLp.toLp
      (densityWeightedH1SpaceRepresentative ρ
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value = _
    rw [← hEq]
    exact congrArg Prod.fst hp
  have hAE : densityWeightedH1Value ρ q =ᵐ[densityWeightedMeasure ρ] g.value := by
    filter_upwards [Lp.ext_iff.mp hLp.symm, g.value_memLp.coeFn_toLp] with x hx hy
    exact hx.trans hy
  have hphysical := (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hAE
  exact hphysical

/-- The literal Euclidean gradient of a smooth spatial test. -/
def testGradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (gradient f x)

/-- Compact smooth tests give actual representatives in the full weighted graph. -/
def compactTestGraph {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    WeightedSobolevGraph (physicalForceMeasure hd lam) := by
  letI : IsLocallyFiniteMeasure (physicalForceMeasure hd lam) :=
    densityWeightedMeasure_locallyFinite _ (physicalForceWeight_continuous hd lam)
  have hg : Continuous (testGradient f) := by
    apply (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
    apply continuous_pi
    intro j
    exact (gantert_contDiff_coordinateDerivative hf j).continuous
  have hgc : HasCompactSupport (testGradient f) := by
    apply hc.mono'
    intro x hx
    by_contra hnot
    apply hx
    have hz : gradient f x = 0 := by
      funext j
      simp only [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hnot,
        zero_apply, Pi.zero_apply]
    simp only [testGradient, hz, WithLp.toLp_zero]
  refine ⟨f, testGradient f, hf.continuous.memLp_of_hasCompactSupport hc,
    hg.memLp_of_hasCompactSupport hgc, ?_⟩
  intro j
  exact hasWeakPartialDerivative_of_contDiff j f (hf.of_le (by simp))

@[simp] theorem compactTestGraph_value {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (compactTestGraph hd lam f hf hc).value = f := rfl

@[simp] theorem compactTestGraph_gradient {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (x : Vec d) :
    WithLp.ofLp ((compactTestGraph hd lam f hf hc).weakGradient x) = gradient f x := rfl

/-- The actual compact-test energy equals minus the physical generator pairing. -/
theorem compactTest_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω)
    (hsymm : ∀ x, (ω.1 x).transpose = ω.1 x) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    physicalH1FormEnergy ω hd lam (compactTestGraph hd lam f hf hc) =
      -(∫ x, f x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
        ∂physicalReversibleMeasure ω hd lam) := by
  have h := gantert_fullForm_compactTest hd ω hω hsymm lam hf hc
    (compactTestGraph hd lam f hf hc)
  change (∫ x, f x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
    ∂physicalReversibleMeasure ω hd lam) =
    -physicalH1FormEnergy ω hd lam (compactTestGraph hd lam f hf hc) at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- Compact smooth tests belong to the actual weighted form domain. -/
theorem compactTest_mem_physicalH1 {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    physicalH1Member ω hd lam f := by
  let u := compactTestGraph hd lam f hf hc
  refine ⟨Quotient.mk _ u, ?_⟩
  apply (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq
  exact u.value_memLp.coeFn_toLp

/-- The full supplied closed-form domain gives the compact-test form bound. -/
theorem compactTest_formBounded {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h₀ h₁)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f ≤ C := by
  let := gantert_physicalMeasure_locallyFinite hd ω lam
  exact (R.closedForm_domain f (hf.continuous.memLp_of_hasCompactSupport hc)).mpr
    (compactTest_mem_physicalH1 hd Λ ω hω lam f hf hc)

/-- The supplied GMP closed form has the correct compact-test physical generator
pairing as its short-time quadratic limit. This is a form limit, not yet a
strong generator derivative or a pointwise transition evolution identity. -/
theorem compactTest_formLimit {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h₀ h₁)
    (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      R.transitionKernel t f) (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (-(∫ x, f x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
        ∂physicalReversibleMeasure ω hd lam))) := by
  let u := compactTestGraph hd lam f hf hc
  obtain ⟨q, hq⟩ := compactTest_mem_physicalH1 hd Λ ω hω lam f hf hc
  have h := R.closedForm_value f q hq u (EventuallyEq.rfl)
  rw [compactTest_energy hd ω hSmooth (fun x => (hω.1 x).1) lam f hf hc] at h
  exact h

/-- A compact smooth test in the actual full weighted Hilbert form domain. -/
def compactTestDomain {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) :=
  densityWeightedH1GraphEquiv _ _ _ (Quotient.mk _ (compactTestGraph hd lam f hf hc))

/-- Reconstructing the full-domain test preserves its literal gradient almost
 everywhere for the physical reversible measure. -/
theorem compactTestDomain_gradient {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (compactTestDomain hd lam f hf hc)).weakGradient =ᵐ[
        physicalReversibleMeasure ω hd lam] testGradient f := by
  let g := compactTestGraph hd lam f hf hc
  let v := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (compactTestDomain hd lam f hf hc)
  have hp := physicalH1Representative_pair_eq_quotient_pair hd lam (Quotient.mk _ g)
  have hmk := densityWeightedH1GraphPair_quotient_mk (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) g
  have hp := hp.trans hmk
  have hg : v.gradient_memLp.toLp v.weakGradient =
      g.gradient_memLp.toLp g.weakGradient := congrArg Prod.snd hp
  have hae : v.weakGradient =ᵐ[physicalForceMeasure hd lam] g.weakGradient := by
    exact v.gradient_memLp.coeFn_toLp.symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp (EuclideanSpace ℝ (Fin d)) 2
        (physicalForceMeasure hd lam) => (z : Vec d → EuclideanSpace ℝ (Fin d))) hg)).trans g.gradient_memLp.coeFn_toLp)
  exact (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hae

/-- The actual full-domain test also retains the compact test value in the
 physical reversible measure. -/
theorem compactTestDomain_value {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (compactTestDomain hd lam f hf hc)).value =ᵐ[
        physicalReversibleMeasure ω hd lam] f := by
  let g := compactTestGraph hd lam f hf hc
  let v := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (compactTestDomain hd lam f hf hc)
  have hp := physicalH1Representative_pair_eq_quotient_pair hd lam (Quotient.mk _ g)
  have hmk := densityWeightedH1GraphPair_quotient_mk (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) g
  have hv : v.value_memLp.toLp v.value = g.value_memLp.toLp g.value :=
    congrArg Prod.fst (hp.trans hmk)
  have hae : v.value =ᵐ[physicalForceMeasure hd lam] g.value := by
    exact v.value_memLp.coeFn_toLp.symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2
        (physicalForceMeasure hd lam) => (z : Vec d → ℝ)) hv)).trans g.value_memLp.coeFn_toLp)
  exact (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hae

/-- The mixed full-domain physical form has the actual physical generator as
 its compact-test representer. The first argument ranges over the entire domain. -/
theorem compactTest_fullDomain_pairing {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (hSmooth : IsSmoothFieldPair ω)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u
      (compactTestDomain hd lam f hf hc) =
    -(∫ x, (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x *
      physicalGenerator (firstCoordinateIndex hd) ω lam f x
      ∂physicalReversibleMeasure ω hd lam) := by
  let gu := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  have hibp := gantert_fullForm_compactTest hd ω hSmooth
    (fun x => (hω.1 x).1) lam hf hc gu
  rw [hibp, neg_neg]
  apply integral_congr_ae
  filter_upwards [compactTestDomain_gradient hd Λ ω hω lam f hf hc] with x hx
  change (1 / 2 : ℝ) * dot (WithLp.ofLp (gu.weakGradient x))
    ((ω.1 x).mulVec (WithLp.ofLp
      ((densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (compactTestDomain hd lam f hf hc)).weakGradient x))) = _
  rw [hx]
  rfl

/-- The compact-test physical generator as an element of the actual L² space. -/
def compactTestGeneratorL2 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (hSmooth : IsSmoothFieldPair ω) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (gantert_memLp_physicalGenerator hd (firstCoordinateIndex hd) ω hSmooth lam hf hc).toLp _

/-- The full physical form represents the compact-test generator in the actual
 L² inner product, with no restriction of the first argument to smooth tests. -/
theorem compactTest_fullDomain_generatorInner {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (hSmooth : IsSmoothFieldPair ω)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u
      (compactTestDomain hd lam f hf hc) =
    -inner ℝ (sourcePhysicalValue (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u)
      (compactTestGeneratorL2 hd ω hSmooth lam f hf hc) := by
  rw [compactTest_fullDomain_pairing hd Λ ω hω lam hSmooth u f hf hc]
  erw [L2.inner_def]
  congr 1
  let gu := sourcePhysicalGraph (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
  apply integral_congr_ae
  filter_upwards [gu.value_memLp.coeFn_toLp,
    (gantert_memLp_physicalGenerator hd (firstCoordinateIndex hd) ω hSmooth lam hf hc).coeFn_toLp]
    with x hx hy
  change gu.value x * physicalGenerator (firstCoordinateIndex hd) ω lam f x =
    inner ℝ (gu.value_memLp.toLp gu.value x)
      (compactTestGeneratorL2 hd ω hSmooth lam f hf hc x)
  rw [hx]
  change _ = inner ℝ (gu.value x)
    ((gantert_memLp_physicalGenerator hd (firstCoordinateIndex hd) ω hSmooth lam hf hc).toLp _ x)
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

end EinsteinFull.C8GMP
