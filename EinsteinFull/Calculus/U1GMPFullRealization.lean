import EinsteinFull.Calculus.U1GMPNashRepresentation
import EinsteinFull.Calculus.U2GMPHeatDensity
import EinsteinFull.Calculus.S5ExpWeightSupport
import EinsteinFull.Calculus.U7RegularKernelDensity
import EinsteinFull.Calculus.U8RegularUnforcedExponential

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- A uniform almost-everywhere compact-test estimate gives a bounded,
normalized density for the same physical kernel at every starting point. -/
theorem u1_signed_bounded_density_of_compact_test_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (M : ℝ) (hM : 0 < M)
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ≤
          M * ∫ y, f y) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  letI : IsMarkovKernel K := ⟨fun x =>
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩⟩
  have hdom : ∀ x, K x ≤ ENNReal.ofReal M • (volume : Measure (Vec d)) := by
    apply u2_finite_kernel_domination_of_ae_compact_tests K M hM.le
    · intro f
      change Continuous (fun x => ∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup
        hd ω lam Λ hΛ hω hSmooth t x)
      simp_rw [Blueprint.gmpPhysicalC0KernelSemigroup_integral]
      exact (Blueprint.gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth t f).continuous
    · exact hbound
  have hac : ∀ x, K x ≪ (volume : Measure (Vec d)) :=
    fun x => Measure.absolutelyContinuous_of_le_smul (hdom x)
  obtain ⟨p, hp, hn, hr⟩ := u2_kernel_measurable_real_density_of_absolutelyContinuous K hac
  obtain ⟨q, hq, hqb, hqr⟩ := u2_real_density_bounded_of_domination K p hp hn hr M hM.le hdom
  exact ⟨q, hq, hqb,
    u2_markov_real_density_integrable_and_integral K q hq (fun x y => (hqb x y).1) hqr,
    hqr⟩

#print axioms u1_signed_bounded_density_of_compact_test_bound

end EinsteinFull

noncomputable section
namespace EinsteinFull
open EinsteinRelation.SpatialDirichlet PDE Filter

/-- A graph representative of a bounded smooth multiplier of a form-domain
value also belongs to the physical form domain. -/
theorem u1_signed_physical_graph_multiplier_mem_domain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain)
    (u w : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hw : w.value = fun x => φ x * u.value x) :
    w.value_memLp.toLp w.value ∈
      (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain := by
  let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
    hφb.of_measure_le_smul ENNReal.ofReal_ne_top
      (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  let hm : MemLp (fun x => φ x * f x) 2 (physicalReversibleMeasure ω hd lam) :=
    hφp.fun_mul (Lp.memLp f)
  have heq : w.value_memLp.toLp w.value = hm.toLp (fun x => φ x * f x) := by
    apply Lp.ext
    filter_upwards [w.value_memLp.coeFn_toLp, hm.coeFn_toLp, hu] with x hwx hmx hux
    rw [hwx, hmx, hw]
    change φ x * u.value x = φ x * f x
    rw [hux]
  rw [heq]
  exact u1_signed_physical_closedForm_mul_bounded_smooth hd ω lam Λ hΛ hω
    f hf φ hφ hφb hDφ

#print axioms u1_signed_physical_graph_multiplier_mem_domain

/-- The physical form satisfies the exact bounded-multiplier energy identity
for any physical graph representing an element of its domain. -/
theorem u1_signed_physical_domain_multiplier_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (φ : EinsteinRelation.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam)) :
    ∃ w z : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      w.value = (fun x => φ x * u.value x) ∧
      z.value = (fun x => φ x ^ 2 * u.value x) ∧
      (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
          (w.value_memLp.toLp w.value) (w.value_memLp.toLp w.value) =
        (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
          f (z.value_memLp.toLp z.value) +
        ∫ x, (1 / 2 : ℝ) * u.value x ^ 2 *
          dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x))
          ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨w, z, hw, hz, he⟩ :=
    u1_signed_physical_graph_multiplier_energy hd ω lam Λ hΛ hω u φ hφ hφb hDφ
  have hwd := u1_signed_physical_graph_multiplier_mem_domain hd ω lam Λ hΛ hω
    f hf u w hu φ hφ hφb hDφ hw
  have hzw : z.value = fun x => φ x * w.value x := by
    funext x
    rw [hz, hw]
    simp only
    ring
  have hzd := u1_signed_physical_graph_multiplier_mem_domain hd ω lam Λ hΛ hω
    (w.value_memLp.toLp w.value) hwd w z w.value_memLp.coeFn_toLp.symm
    φ hφ hφb hDφ hzw
  refine ⟨w, z, hw, hz, ?_⟩
  rw [u1_signed_physical_closedForm_domain_eq_graph_integral hd ω lam Λ hΛ hω
    _ _ hwd hwd w w w.value_memLp.coeFn_toLp.symm w.value_memLp.coeFn_toLp.symm,
    u1_signed_physical_closedForm_domain_eq_graph_integral hd ω lam Λ hΛ hω
    _ _ hf hzd u z hu z.value_memLp.coeFn_toLp.symm]
  exact he

#print axioms u1_signed_physical_domain_multiplier_energy


/-- The multiplier correction is bounded by the weighted L² norm when the
multiplier has a relative Euclidean gradient bound. -/
theorem u1_signed_physical_multiplier_correction_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u w : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (φ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hw : w.value = fun x => φ x * u.value x)
    (hgrad : ∀ x, euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2)
    (hc : Integrable (fun x => (1 / 2 : ℝ) * u.value x ^ 2 *
      dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x)))
      (physicalReversibleMeasure ω hd lam)) :
    (∫ x, (1 / 2 : ℝ) * u.value x ^ 2 *
      dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x))
      ∂physicalReversibleMeasure ω hd lam) ≤
    (Λ / 2 * q ^ 2) * ‖w.value_memLp.toLp w.value‖ ^ 2 := by
  have hi : Integrable (fun x => w.value x ^ 2) (physicalReversibleMeasure ω hd lam) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      w.value_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hb : ∀ x, (1 / 2 : ℝ) * u.value x ^ 2 *
      dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x)) ≤
      (Λ / 2 * q ^ 2) * w.value x ^ 2 := by
    intro x
    have hA := ((hω.1 x).2 (PDE.classicalGradient φ x)).2
    have hD := hgrad x
    have hΛ0 : 0 ≤ Λ := le_trans (by norm_num) hΛ
    have hscale := mul_le_mul_of_nonneg_left hD hΛ0
    have hu0 := sq_nonneg (u.value x)
    have hφu : w.value x = φ x * u.value x := congrFun hw x
    have hmul := mul_le_mul_of_nonneg_left (le_trans hA hscale)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hu0)
    rw [hφu]
    nlinarith only [hmul]
  have hn : (∫ x, w.value x ^ 2 ∂physicalReversibleMeasure ω hd lam) =
      ‖w.value_memLp.toLp w.value‖ ^ 2 := by
    have he : (∫ x, (w.value_memLp.toLp w.value) x ^ 2
        ∂physicalReversibleMeasure ω hd lam) = ‖w.value_memLp.toLp w.value‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    apply (integral_congr_ae ?_).trans he
    filter_upwards [w.value_memLp.coeFn_toLp] with x hx
    rw [hx]
  calc
    _ ≤ ∫ x, (Λ / 2 * q ^ 2) * w.value x ^ 2 ∂physicalReversibleMeasure ω hd lam :=
      integral_mono_ae hc (hi.const_mul _) (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul, hn]

#print axioms u1_signed_physical_multiplier_correction_le


/-- The actual signed physical form obeys the bounded-weight Davies energy estimate. -/
theorem u1_signed_physical_domain_multiplier_energy_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (φ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hgrad : ∀ x, euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2) :
    ∃ w z : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      w.value = (fun x => φ x * u.value x) ∧
      z.value = (fun x => φ x ^ 2 * u.value x) ∧
      (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
          (w.value_memLp.toLp w.value) (w.value_memLp.toLp w.value) ≤
        (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
          f (z.value_memLp.toLp z.value) +
        (Λ / 2 * q ^ 2) * ‖w.value_memLp.toLp w.value‖ ^ 2 := by
  obtain ⟨a, b, _, _, hab⟩ :=
    u1_signed_physical_graph_multiplier_products hd ω lam Λ hω u φ hφ hφb hDφ
  have hc : Integrable (fun x => (1 / 2 : ℝ) * u.value x ^ 2 *
      dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x)))
      (physicalReversibleMeasure ω hd lam) :=
    (u1_integral_eq_add_of_integrable (physicalReversibleMeasure ω hd lam)
      (weightedFormIntegrand ω.1 a a) (weightedFormIntegrand ω.1 u b)
      (fun x => (1 / 2 : ℝ) * u.value x ^ 2 *
        dot (PDE.classicalGradient φ x) ((ω.1 x).mulVec (PDE.classicalGradient φ x)))
      (physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω a a)
      (physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω u b) hab).1
  obtain ⟨w, z, hw, hz, he⟩ :=
    u1_signed_physical_domain_multiplier_energy hd ω lam Λ hΛ hω f hf u hu φ hφ hφb hDφ
  refine ⟨w, z, hw, hz, ?_⟩
  rw [he]
  exact add_le_add_right
    (u1_signed_physical_multiplier_correction_le hd ω lam Λ hΛ hω u w φ q hw hgrad hc) _

#print axioms u1_signed_physical_domain_multiplier_energy_le


/-- The physical generator satisfies the one-sided multiplier estimate on its
actual domain, expressed through graph representatives of the two products. -/
theorem u1_signed_physical_generator_multiplier_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam]
      (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
    (φ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hgrad : ∀ x, euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2) :
    ∃ w z : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      w.value = (fun x => φ x * u.value x) ∧
      z.value = (fun x => φ x ^ 2 * u.value x) ∧
      inner ℝ ((Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator f)
          (z.value_memLp.toLp z.value) ≤
        (Λ / 2 * q ^ 2) * ‖w.value_memLp.toLp w.value‖ ^ 2 := by
  let E := Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have hf : (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) ∈ E.domain :=
    (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr
      (Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω f)
  obtain ⟨w, z, hw, hz, he⟩ :=
    u1_signed_physical_domain_multiplier_energy_le hd ω lam Λ hΛ hω f hf u hu
      φ q hφ hφb hDφ hgrad
  have hwD : w.value_memLp.toLp w.value ∈ E.domain :=
    u1_signed_physical_graph_multiplier_mem_domain hd ω lam Λ hΛ hω f hf u w hu
      φ hφ hφb hDφ hw
  have hzD : z.value_memLp.toLp z.value ∈ E.domain := by
    obtain ⟨a, b, ha, hb, _⟩ :=
      u1_signed_physical_graph_multiplier_products hd ω lam Λ hω u φ hφ hφb hDφ
    have heq : z.value = b.value := hz.trans hb.symm
    have ht : z.value_memLp.toLp z.value = b.value_memLp.toLp b.value := by
      apply Lp.ext
      filter_upwards [z.value_memLp.coeFn_toLp, b.value_memLp.coeFn_toLp] with x hz' hb'
      rw [hz', hb', heq]
    rw [ht]
    exact u1_signed_physical_graph_multiplier_mem_domain hd ω lam Λ hΛ hω
      (a.value_memLp.toLp a.value) (u1_signed_physical_graph_multiplier_mem_domain
        hd ω lam Λ hΛ hω f hf u a hu φ hφ hφb hDφ ha)
      a b a.value_memLp.coeFn_toLp.symm φ hφ hφb hDφ (by rw [ha, hb]; funext x; ring)
  have hn := E.form_nonneg (w.value_memLp.toLp w.value) hwD
  have hg := Blueprint.gmpPhysicalSemigroup_generator_form hd ω lam Λ hΛ hω f
    (z.value_memLp.toLp z.value) hzD
  change E.form _ _ ≤ E.form _ _ + _ at he
  change inner ℝ _ _ + E.form _ _ = 0 at hg
  exact ⟨w, z, hw, hz, by linarith only [he, hn, hg]⟩

#print axioms u1_signed_physical_generator_multiplier_le


/-- Multiplication by an essentially bounded real function on L². -/
def u1LpMultiplier {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (φ : X → ℝ) (hφ : MemLp φ ∞ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 (hφ.toLp φ)

/-- The L² multiplier agrees with pointwise multiplication almost everywhere. -/
theorem u1LpMultiplier_coe {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (φ : X → ℝ) (hφ : MemLp φ ∞ μ) (f : Lp ℝ 2 μ) :
    u1LpMultiplier φ hφ f =ᵐ[μ] fun x => φ x * f x := by
  have hm := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hφ.toLp φ) f
  filter_upwards [hφ.coeFn_toLp, hm] with x hx hy
  simpa only [u1LpMultiplier, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hx] using hy

/-- Real multiplication is self-adjoint on L². -/
theorem u1LpMultiplier_inner {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (φ : X → ℝ) (hφ : MemLp φ ∞ μ) (f g : Lp ℝ 2 μ) :
    inner ℝ (u1LpMultiplier φ hφ f) g = inner ℝ f (u1LpMultiplier φ hφ g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u1LpMultiplier_coe φ hφ f, u1LpMultiplier_coe φ hφ g] with x hf hg
  rw [hf, hg]
  change inner ℝ (φ x • f x) (g x) = inner ℝ (f x) (φ x • g x)
  rw [real_inner_smul_left, real_inner_smul_right]

#print axioms u1LpMultiplier_inner


/-- The actual signed generator obeys the Davies estimate for bounded smooth
multipliers acting as continuous operators on physical L². -/
theorem u1_signed_physical_generator_LpMultiplier_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hgrad : ∀ x, euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2)
    (f : (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain)
    (u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam]
      (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) :
    let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
      hφb.of_measure_le_smul ENNReal.ofReal_ne_top
        (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
    let M := u1LpMultiplier φ hφp
    inner ℝ (M ((Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator f)) (M f) ≤
      (Λ / 2 * q ^ 2) * ‖M f‖ ^ 2 := by
  let μ := physicalReversibleMeasure ω hd lam
  let hφp : MemLp φ ∞ μ := hφb.of_measure_le_smul ENNReal.ofReal_ne_top
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  let M := u1LpMultiplier φ hφp
  obtain ⟨w, z, hw, hz, hbound⟩ :=
    u1_signed_physical_generator_multiplier_le hd ω lam Λ hΛ hω f u hu φ q hφ hφb hDφ hgrad
  have hwM : w.value_memLp.toLp w.value = M f := by
    apply Lp.ext
    filter_upwards [w.value_memLp.coeFn_toLp, u1LpMultiplier_coe φ hφp f, hu] with x hx hy hu'
    rw [hx, hy, hw]
    change φ x * u.value x = φ x * (f : Lp ℝ 2 μ) x
    rw [hu']
  have hzM : z.value_memLp.toLp z.value = M (M f) := by
    apply Lp.ext
    filter_upwards [z.value_memLp.coeFn_toLp, u1LpMultiplier_coe φ hφp (M f),
      u1LpMultiplier_coe φ hφp f, hu] with x hx hy hy' hu'
    rw [hx, hy, hy', hz]
    change φ x ^ 2 * u.value x = φ x * (φ x * (f : Lp ℝ 2 μ) x)
    rw [hu']
    ring
  rw [hwM, hzM] at hbound
  change inner ℝ (M _) (M f) ≤ (Λ / 2 * q ^ 2) * ‖M f‖ ^ 2
  rw [u1LpMultiplier_inner]
  exact hbound

#print axioms u1_signed_physical_generator_LpMultiplier_le


/-- A weighted Sobolev graph can be transferred to a dominated measure while
preserving its pointwise value and weak gradient. -/
theorem u1_weighted_graph_transfer {d : ℕ} (μ ν : Measure (EinsteinRelation.Vec d))
    (C : ℝ≥0∞) (hC : C ≠ ∞) (hμν : μ ≤ C • ν)
    (u : WeightedSobolevGraph ν) :
    ∃ v : WeightedSobolevGraph μ, v.value = u.value ∧ v.weakGradient = u.weakGradient := by
  let v : WeightedSobolevGraph μ := {
    value := u.value
    weakGradient := u.weakGradient
    value_memLp := u.value_memLp.of_measure_le_smul hC hμν
    gradient_memLp := u.gradient_memLp.of_measure_le_smul hC hμν
    distributionalGradient := u.distributionalGradient }
  exact ⟨v, rfl, rfl⟩

#print axioms u1_weighted_graph_transfer


/-- Every physical form-domain element has a graph over the actual reversible
measure with the same almost-everywhere value. -/
theorem u1_signed_physical_domain_exists_graph {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain) :
    ∃ u : WeightedSobolevGraph (physicalReversibleMeasure ω hd lam),
      u.value =ᵐ[physicalReversibleMeasure ω hd lam] f := by
  obtain ⟨u, hu⟩ := (physicalH1Member_iff_exists_graph ω hd lam f).mp
    ((Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mp hf)
  obtain ⟨v, hv, _⟩ := u1_weighted_graph_transfer
    (physicalReversibleMeasure ω hd lam) (physicalForceMeasure (firstCoordinateIndex hd) lam)
    (ENNReal.ofReal (Real.exp (2 * Λ))) ENNReal.ofReal_ne_top
    (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1 u
  exact ⟨v, hv ▸ hu⟩

#print axioms u1_signed_physical_domain_exists_graph

/-- The actual signed generator satisfies the bounded multiplier estimate on
its entire generator domain. -/
theorem u1_signed_physical_generator_LpMultiplier_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hgrad : ∀ x, euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2)
    (f : (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain) :
    let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
      hφb.of_measure_le_smul ENNReal.ofReal_ne_top
        (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
    let M := u1LpMultiplier φ hφp
    inner ℝ (M ((Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator f)) (M f) ≤
      (Λ / 2 * q ^ 2) * ‖M f‖ ^ 2 := by
  have hf := (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr
    (Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω f)
  obtain ⟨u, hu⟩ := u1_signed_physical_domain_exists_graph hd ω lam Λ hΛ hω f hf
  exact u1_signed_physical_generator_LpMultiplier_le hd ω lam Λ hΛ hω
    φ q hφ hφb hDφ hgrad f u hu

#print axioms u1_signed_physical_generator_LpMultiplier_bound


/-- A generator energy bound gives weighted growth for a real contraction semigroup. -/
theorem u1_real_semigroup_weighted_growth
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H)
    (M : H →L[ℝ] H) (κ : ℝ)
    (hE : ∀ f : S.generatorDomain, inner ℝ (M (S.generator f)) (M f) ≤ κ * ‖M f‖ ^ 2)
    (f : H) (t : ℝ≥0) :
    ‖M (S t f)‖ ≤ Real.exp (κ * (t : ℝ)) * ‖M f‖ := by
  have hdom : ∀ f : S.generatorDomain, ∀ t : ℝ≥0,
      ‖M (S t f)‖ ≤ Real.exp (κ * (t : ℝ)) * ‖M f‖ := by
    intro f t
    let u : ℝ → H := fun s => M (S s.toNNReal f)
    have hu : Continuous u := M.continuous.comp (S.continuous_operator_toNNReal f)
    have hd : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun r => ‖u r‖ ^ 2)
        (2 * inner ℝ (u s) (M (S s.toNNReal (S.generator f)))) (Set.Ici s) s := by
      intro s hs
      have h1 := S.hasDerivWithinAt_Ici f s.toNNReal
      rw [Real.coe_toNNReal s hs] at h1
      have h2 := M.hasFDerivAt.comp_hasDerivWithinAt s h1
      exact h2.norm_sq
    have hb := le_gronwallBound_of_liminf_deriv_right_le
      (f := fun s => ‖u s‖ ^ 2)
      (f' := fun s => 2 * inner ℝ (u s) (M (S s.toNNReal (S.generator f))))
      (δ := ‖u 0‖ ^ 2) (K := 2 * κ) (ε := 0) (a := 0) (b := (t : ℝ))
      (hu.norm.pow 2).continuousOn
      (fun s hs _ hr => (hd s hs.1).liminf_right_slope_le hr)
      le_rfl
      (fun s _ => by
        let g : S.generatorDomain := ⟨S s.toNNReal f, S.operator_mem_generatorDomain f s.toNNReal⟩
        have hs := hE g
        rw [S.generator_operator] at hs
        change 2 * inner ℝ (M (S s.toNNReal f)) (M (S s.toNNReal (S.generator f))) ≤
          2 * κ * ‖M (S s.toNNReal f)‖ ^ 2 + 0
        rw [real_inner_comm]
        linarith only [hs])
      (t : ℝ) ⟨t.property, le_rfl⟩
    rw [gronwallBound_ε0, sub_zero] at hb
    have e2 : Real.exp (2 * κ * (t : ℝ)) = Real.exp (κ * (t : ℝ)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hu0 : u 0 = M f := by
      simp only [u, Real.toNNReal_zero, S.operator_zero, ContinuousLinearMap.id_apply]
    have hut : u (t : ℝ) = M (S t f) := by simp only [u, Real.toNNReal_coe]
    rw [hu0, hut] at hb
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    calc ‖M (S t f)‖ ^ 2 ≤ ‖M f‖ ^ 2 * Real.exp (2 * κ * (t : ℝ)) := hb
      _ = (Real.exp (κ * (t : ℝ)) * ‖M f‖) ^ 2 := by rw [e2]; ring
  let a (r : ℝ≥0) : S.generatorDomain := ⟨(r : ℝ)⁻¹ • S.orbitIntegral f r,
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f r)⟩
  have ha : Tendsto (fun r : ℝ≥0 => (a r : H)) (𝓝[Set.Ioi 0] 0) (𝓝 f) :=
    S.tendsto_inv_smul_orbitIntegral f
  have hl := (((M.continuous.comp (S t).continuous).tendsto f).comp ha).norm
  have hr := (((M.continuous.tendsto f).comp ha).norm).const_mul (Real.exp (κ * (t : ℝ)))
  refine le_of_tendsto_of_tendsto hl hr ?_
  exact Filter.Eventually.of_forall fun r => hdom (a r) t

#print axioms u1_real_semigroup_weighted_growth


/-- Weighted L² growth for the actual signed physical semigroup. -/
theorem u1_signed_physical_semigroup_LpMultiplier_growth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp φ ∞ (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hDφ : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞
      (physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hgrad : ∀ x, euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) :
    let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
      hφb.of_measure_le_smul ENNReal.ofReal_ne_top
        (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
    let M := u1LpMultiplier φ hφp
    ‖M (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f)‖ ≤
      Real.exp ((Λ / 2 * q ^ 2) * (t : ℝ)) * ‖M f‖ := by
  apply u1_real_semigroup_weighted_growth
  exact u1_signed_physical_generator_LpMultiplier_bound hd ω lam Λ hΛ hω
    φ q hφ hφb hDφ hgrad

#print axioms u1_signed_physical_semigroup_LpMultiplier_growth


/-- Smooth Davies weights are bounded multipliers for the physical evolution. -/
theorem u1_signed_physical_semigroup_s5Weight_growth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : EinsteinRelation.Vec d → ℝ) (B q : ℝ) (h : S5Weight φ B q)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) :
    ∃ (hφ : MemLp φ ∞ (physicalReversibleMeasure ω hd lam)),
      ‖u1LpMultiplier φ hφ (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f)‖ ≤
        Real.exp ((Λ / 2 * q ^ 2) * (t : ℝ)) * ‖u1LpMultiplier φ hφ f‖ := by
  let ν := physicalForceMeasure (firstCoordinateIndex hd) lam
  have hnorm (x : EinsteinRelation.Vec d) :
      ‖WithLp.toLp 2 (PDE.classicalGradient φ x)‖ =
        s5Nrm (fun j => coordinateDerivative j φ x) := by
    simp [EuclideanSpace.norm_eq, s5Nrm, PDE.classicalGradient, coordinateDerivative,
      PDE.basisVec, unitVector, Real.norm_eq_abs, pow_two]
  have hgrad (x : EinsteinRelation.Vec d) :
      euclideanSq (PDE.classicalGradient φ x) ≤ q ^ 2 * φ x ^ 2 := by
    have ht := pow_le_pow_left₀ (s5Nrm_nonneg _) (h.grad x) 2
    have he : s5Nrm (fun j => coordinateDerivative j φ x) ^ 2 =
        euclideanSq (PDE.classicalGradient φ x) := by
      unfold s5Nrm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
      simp [euclideanSq, dot, PDE.classicalGradient, coordinateDerivative,
        PDE.basisVec, unitVector, pow_two]
    rw [he] at ht
    simpa only [mul_pow, sq_abs] using ht
  have hφb : MemLp φ ∞ ν := memLp_top_of_bound h.smooth.continuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using h.bound x)
  have hDb : MemLp (fun x => WithLp.toLp 2 (PDE.classicalGradient φ x)) ∞ ν := by
    apply memLp_top_of_bound
      (((PiLp.continuous_toLp 2 _).comp
        (PDE.ContDiff.continuous_classicalGradient (h.smooth.of_le (by simp)))).aestronglyMeasurable)
      (q * B)
    exact Filter.Eventually.of_forall fun x => by
      change ‖WithLp.toLp 2 (PDE.classicalGradient φ x)‖ ≤ q * B
      rw [hnorm]
      exact (h.grad x).trans (mul_le_mul_of_nonneg_left (h.bound x) h.q_nonneg)
  let hφp : MemLp φ ∞ (physicalReversibleMeasure ω hd lam) :=
    hφb.of_measure_le_smul ENNReal.ofReal_ne_top
      (u1_signed_physical_force_measure_comparable hd ω lam Λ hω).1
  exact ⟨hφp, u1_signed_physical_semigroup_LpMultiplier_growth hd ω lam Λ hΛ hω
    φ q h.smooth hφb hDb hgrad f t⟩

#print axioms u1_signed_physical_semigroup_s5Weight_growth


/-- The bounded smooth truncations of an exponential satisfy physical L² growth. -/
theorem u1_signed_physical_semigroup_truncated_exp_growth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (ψ : EinsteinRelation.Vec d → ℝ) (q n : ℝ) (hq : 0 ≤ q)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψgrad : ∀ x, s5Nrm (fun j => coordinateDerivative j ψ x) ≤ 1)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0) :
    ∃ (hφ : MemLp (fun x => s5G q n (ψ x)) ∞ (physicalReversibleMeasure ω hd lam)),
      ‖u1LpMultiplier (fun x => s5G q n (ψ x)) hφ
          (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f)‖ ≤
        Real.exp ((Λ / 2 * q ^ 2) * (t : ℝ)) *
          ‖u1LpMultiplier (fun x => s5G q n (ψ x)) hφ f‖ :=
  u1_signed_physical_semigroup_s5Weight_growth hd ω lam Λ hΛ hω _ _ q
    (s5Weight_G hq n hψ hψgrad) f t

#print axioms u1_signed_physical_semigroup_truncated_exp_growth


/-- Removing the smooth upper truncation yields growth for an exponential weight. -/
theorem u1_signed_physical_semigroup_exp_growth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (ψ : EinsteinRelation.Vec d → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψgrad : ∀ x, s5Nrm (fun j => coordinateDerivative j ψ x) ≤ 1)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0)
    (hf : MemLp (fun x => Real.exp (q * ψ x) * f x) 2
      (physicalReversibleMeasure ω hd lam)) :
    let μ := physicalReversibleMeasure ω hd lam
    let U := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f
    MemLp (fun x => Real.exp (q * ψ x) * U x) 2 μ ∧
      eLpNorm (fun x => Real.exp (q * ψ x) * U x) 2 μ ≤
        ENNReal.ofReal (Real.exp ((Λ / 2 * q ^ 2) * (t : ℝ))) *
          eLpNorm (fun x => Real.exp (q * ψ x) * f x) 2 μ := by
  let μ := physicalReversibleMeasure ω hd lam
  let U := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f
  let K := Real.exp ((Λ / 2 * q ^ 2) * (t : ℝ))
  let fn : ℕ → EinsteinRelation.Vec d → ℝ := fun n x => s5G q n (ψ x) * U x
  let flim : EinsteinRelation.Vec d → ℝ := fun x => Real.exp (q * ψ x) * U x
  have hcont : ∀ n : ℕ, Continuous (fun x => s5G q n (ψ x)) :=
    fun n => ((s5Weight_G hq (n : ℝ) hψ hψgrad).smooth).continuous
  have hfn : ∀ n, AEStronglyMeasurable (fn n) μ := fun n =>
    (hcont n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable U)
  have hflim : AEStronglyMeasurable flim μ :=
    (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable U)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (flim x)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    exact ((tendsto_s5G q (ψ x)).comp tendsto_natCast_atTop_atTop).mul_const (U x)
  have hbound : ∀ n : ℕ, eLpNorm (fn n) 2 μ ≤ ENNReal.ofReal K *
      eLpNorm (fun x => Real.exp (q * ψ x) * f x) 2 μ := by
    intro n
    obtain ⟨hφ, hg⟩ := u1_signed_physical_semigroup_truncated_exp_growth
      hd ω lam Λ hΛ hω ψ q n hq hψ hψgrad f t
    have huf : MemLp (fn n) 2 μ := hφ.fun_mul (Lp.memLp U)
    have hff : MemLp (fun x => s5G q n (ψ x) * f x) 2 μ := hφ.fun_mul (Lp.memLp f)
    have hn : (eLpNorm (fn n) 2 μ).toReal ≤ K *
        (eLpNorm (fun x => s5G q n (ψ x) * f x) 2 μ).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae (u1LpMultiplier_coe _ hφ U),
        Lp.norm_def, eLpNorm_congr_ae (u1LpMultiplier_coe _ hφ f)] at hg
      exact hg
    have hfinite1 := huf.eLpNorm_lt_top.ne
    have hfinite2 := hff.eLpNorm_lt_top.ne
    have hle : eLpNorm (fn n) 2 μ ≤ ENNReal.ofReal K *
        eLpNorm (fun x => s5G q n (ψ x) * f x) 2 μ := by
      rw [← ENNReal.ofReal_toReal hfinite1, ← ENNReal.ofReal_toReal hfinite2,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hn
    refine hle.trans (mul_le_mul' le_rfl ?_)
    refine eLpNorm_mono ((hcont n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) fun x => ?_
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (s5G_pos _ _ _),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (s5G_le_exp hq _ _) (abs_nonneg _)
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (2 : ℝ≥0∞)) (μ := μ)
    hfn flim hflim hlim
  have hcl : atTop.liminf (fun n => eLpNorm (fn n) 2 μ) ≤ ENNReal.ofReal K *
      eLpNorm (fun x => Real.exp (q * ψ x) * f x) 2 μ :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbound).frequently
  have hfinal := hle.trans hcl
  exact ⟨hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top),
    hfinal⟩

#print axioms u1_signed_physical_semigroup_exp_growth


/-- Exponential L² growth holds for either sign of the weight parameter. -/
theorem u1_signed_physical_semigroup_exp_growth_signed {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (ψ : EinsteinRelation.Vec d → ℝ) (q : ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψgrad : ∀ x, s5Nrm (fun j => coordinateDerivative j ψ x) ≤ 1)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (t : ℝ≥0)
    (hf : MemLp (fun x => Real.exp (q * ψ x) * f x) 2
      (physicalReversibleMeasure ω hd lam)) :
    let μ := physicalReversibleMeasure ω hd lam
    let U := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f
    MemLp (fun x => Real.exp (q * ψ x) * U x) 2 μ ∧
      eLpNorm (fun x => Real.exp (q * ψ x) * U x) 2 μ ≤
        ENNReal.ofReal (Real.exp ((Λ / 2 * q ^ 2) * (t : ℝ))) *
          eLpNorm (fun x => Real.exp (q * ψ x) * f x) 2 μ := by
  by_cases hq : 0 ≤ q
  · exact u1_signed_physical_semigroup_exp_growth hd ω lam Λ hΛ hω ψ q hq
      hψ hψgrad f t hf
  · have hq' : 0 ≤ -q := le_of_lt (neg_pos.mpr (lt_of_not_ge hq))
    have hg : ∀ x, s5Nrm (fun j => coordinateDerivative j (-ψ) x) ≤ 1 := by
      intro x
      have he : (fun j => coordinateDerivative j (-ψ) x) =
          (fun j => (-1 : ℝ) * coordinateDerivative j ψ x) := by
        funext j
        simp only [coordinateDerivative, fderiv_neg, neg_apply, neg_one_mul]
      rw [he, s5Nrm_smul]
      simpa using hψgrad x
    have hf' : MemLp (fun x => Real.exp ((-q) * (-ψ) x) * f x) 2
        (physicalReversibleMeasure ω hd lam) := by
      simpa only [Pi.neg_apply, neg_mul_neg] using hf
    have h := u1_signed_physical_semigroup_exp_growth hd ω lam Λ hΛ hω
      (-ψ) (-q) hq' hψ.neg hg f t hf'
    simpa only [Pi.neg_apply, neg_mul_neg, neg_sq] using h

#print axioms u1_signed_physical_semigroup_exp_growth_signed

/-- On a one-sided displacement slab, gauge domination and the unforced
ultracontractive estimate give a uniform signed-kernel volume bound. -/
theorem u1_regular_signed_kernel_one_sided_displacement_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) (R : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (x : EinsteinRelation.Vec d) (s : Set (EinsteinRelation.Vec d)),
      MeasurableSet s →
      (∀ y ∈ s, lam * ((y - x) (firstCoordinateIndex hd)) ≤ R) →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal M * volume s := by
  obtain ⟨C, hC, hg⟩ := u7_regular_signed_kernel_gauge_domination hd ω lam Λ hΛ hω
  obtain ⟨B, hB, hb⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  refine ⟨Real.exp (C * (t : ℝ)) * Real.exp R * B, by positivity, ?_⟩
  intro x s hs hslab
  have h := hg t x s hs
  have hi : (∫⁻ y in s, ENNReal.ofReal
      (Real.exp (lam * ((y - x) ⟨0, by omega⟩)))
      ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ≤
      ENNReal.ofReal (Real.exp R) *
        u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x s := by
    calc
      _ ≤ ∫⁻ _ in s, ENNReal.ofReal (Real.exp R)
          ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with y hy
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        simpa [firstCoordinateIndex] using hslab y hy
      _ = _ := by simp
  calc
    _ ≤ ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        (ENNReal.ofReal (Real.exp R) *
          u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x s) :=
      h.trans (mul_le_mul' le_rfl hi)
    _ ≤ ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        (ENNReal.ofReal (Real.exp R) * (ENNReal.ofReal B * volume s)) := by
      gcongr
      simpa only [Measure.smul_apply, smul_eq_mul] using hb x s
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)),
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ring

#print axioms u1_regular_signed_kernel_one_sided_displacement_bound



/-- The signed regular kernel has a uniform square-root volume bound at every start. -/
theorem u1_regular_signed_kernel_sqrt_volume_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (x : EinsteinRelation.Vec d) (s : Set (EinsteinRelation.Vec d)),
      MeasurableSet s →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal A * (ENNReal.ofReal B * volume s) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hg⟩ := u7_regular_signed_kernel_gauge_domination hd ω lam Λ hΛ hω
  obtain ⟨D, hD, hm⟩ := u8_regular_unforced_kernel_coordinate_exponential_increment
    hd ω Λ hΛ hω (firstCoordinateIndex hd) (2 * lam)
  obtain ⟨B, hB, hb⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  refine ⟨Real.exp (C * (t : ℝ)) * Real.exp (D * (t : ℝ) / 2), B,
    by positivity, hB, ?_⟩
  intro x s hs
  let μ := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x
  let g : EinsteinRelation.Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal
    (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))) )
  have hgm : Measurable g := (Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply _).sub continuous_const))).measurable.ennreal_ofReal
  have hg2 : ∀ y, g y ^ (2 : ℝ) = ENNReal.ofReal
      (Real.exp ((2 * lam) * ((y - x) (firstCoordinateIndex hd)))) := by
    intro y
    rw [ENNReal.rpow_two]
    dsimp [g]
    rw [pow_two, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1 <;> ring
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s)
    Real.HolderConjugate.two_two (g := fun _ => 1) hgm.aemeasurable aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at hh
  have hmoment : (∫⁻ y in s, g y ^ (2 : ℝ) ∂μ) ≤
      ENNReal.ofReal (Real.exp (D * (t : ℝ))) := by
    calc
      _ ≤ ∫⁻ y, g y ^ (2 : ℝ) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ _ := by simpa only [hg2] using hm t x
  have hmass : μ s ≤ ENNReal.ofReal B * volume s := by
    simpa only [Measure.smul_apply, smul_eq_mul] using hb x s
  have hr : ENNReal.ofReal (Real.exp (D * (t : ℝ))) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.exp (D * (t : ℝ) / 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (by norm_num), ← Real.exp_mul]
    congr 1 <;> ring
  have h := hg t x s hs
  calc
    _ ≤ ENNReal.ofReal (Real.exp (C * (t : ℝ))) * ∫⁻ y in s, g y ∂μ := by
      simpa [g, μ, firstCoordinateIndex] using h
    _ ≤ ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
        ((ENNReal.ofReal (Real.exp (D * (t : ℝ)))) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal B * volume s) ^ (1 / 2 : ℝ)) := by
      gcongr
      exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hmoment (by norm_num))
        (ENNReal.rpow_le_rpow (by simpa [hs] using hmass) (by norm_num)))
    _ = _ := by rw [hr, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]

#print axioms u1_regular_signed_kernel_sqrt_volume_bound

/-- A uniform Lebesgue domination estimate yields a bounded normalized
joint density for the regular signed kernel at every starting point. -/
theorem u1_regular_signed_bounded_normalized_density_of_domination {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (M : ℝ) (hM : 0 < M)
    (hdom : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≤
      ENNReal.ofReal M • (volume : Measure (EinsteinRelation.Vec d))) :
    ∃ p : EinsteinRelation.Vec d → EinsteinRelation.Vec d → ℝ,
      Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsMarkovKernel (P t) := ⟨fun x =>
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩⟩
  have hac : ∀ x, P t x ≪ (volume : Measure (EinsteinRelation.Vec d)) :=
    fun x => Measure.absolutelyContinuous_of_le_smul (hdom x)
  obtain ⟨p, hp, hn, hr⟩ := u2_kernel_measurable_real_density_of_absolutelyContinuous (P t) hac
  obtain ⟨q, hq, hqb, hqr⟩ :=
    u2_real_density_bounded_of_domination (P t) p hp hn hr M hM.le hdom
  exact ⟨q, hq, hqb,
    u2_markov_real_density_integrable_and_integral (P t) q hq
      (fun x y => (hqb x y).1) hqr, hqr⟩

#print axioms u1_regular_signed_bounded_normalized_density_of_domination

/-- A Gaussian density estimate gives a uniform normalized density at each
positive time. The constants here are for the same physical kernel. -/
theorem u1_regular_signed_bounded_normalized_density_of_gaussian {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (p : EinsteinRelation.Vec d → EinsteinRelation.Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hb : ∀ x y, 0 ≤ p x y ∧ p x y ≤
      C * (t : ℝ) ^ (-(d : ℝ) / 2) *
        Real.exp (C * (t : ℝ) - c * euclideanNorm (y - x) ^ 2 / (t : ℝ)))
    (hr : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
      volume.withDensity (fun y => ENNReal.ofReal (p x y))) :
    ∃ (M : ℝ) (q : EinsteinRelation.Vec d → EinsteinRelation.Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry q) ∧
      (∀ x y, 0 ≤ q x y ∧ q x y ≤ M) ∧
      (∀ x, Integrable (q x) volume ∧ ∫ y, q x y = 1) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (q x y)) := by
  let M := C * (t : ℝ) ^ (-(d : ℝ) / 2) * Real.exp (C * (t : ℝ))
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hM : 0 < M := by dsimp [M]; positivity
  have hpbound : ∀ x y, 0 ≤ p x y ∧ p x y ≤ M := by
    intro x y
    refine ⟨(hb x y).1, (hb x y).2.trans ?_⟩
    dsimp [M]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : 0 ≤ c * euclideanNorm (y - x) ^ 2 / (t : ℝ) := by positivity
    linarith
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let : IsMarkovKernel K := ⟨fun x =>
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩⟩
  exact ⟨M, p, hM, hp, hpbound,
    u2_markov_real_density_integrable_and_integral K p hp
      (fun x y => (hpbound x y).1) hr, hr⟩

#print axioms u1_regular_signed_bounded_normalized_density_of_gaussian

end EinsteinFull
