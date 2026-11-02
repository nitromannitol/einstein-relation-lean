import EinsteinFull.Calculus.U2GMPRegularRealization
import EinsteinFull.Calculus.U2GMPHeatAbsoluteContinuity
import EinsteinFull.Calculus.U2KernelMinorizationUpgrade
import EinsteinFull.Calculus.U8PhysicalUltracontractive
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- An everywhere absolutely continuous finite kernel admits a jointly measurable
Lebesgue density. This is the measurable Radon--Nikodym step independently of
any particular construction of the kernel. -/
theorem u2_kernel_measurable_density_of_absolutelyContinuous {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) [IsFiniteKernel K]
    (hK : ∀ x, K x ≪ (volume : Measure (Vec d))) :
    ∃ p : Vec d → Vec d → ℝ≥0∞, Measurable (Function.uncurry p) ∧
      ∀ x, K x = (volume : Measure (Vec d)).withDensity (p x) := by
  let μ : Measure (Vec d) := volume
  let ν := μ.toFinite
  let η : Kernel (Vec d) (Vec d) := Kernel.const _ ν
  let q := ν.rnDeriv μ
  let p : Vec d → Vec d → ℝ≥0∞ := fun x y => q y * K.rnDeriv η x y
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hp : Measurable (Function.uncurry p) :=
    (hq.comp measurable_snd).mul (Kernel.measurable_rnDeriv K η)
  refine ⟨p, hp, fun x => ?_⟩
  have hν : μ.withDensity q = ν := Measure.withDensity_rnDeriv_eq ν μ
    (toFinite_absolutelyContinuous μ)
  have hKν : K x ≪ ν := (hK x).trans (absolutelyContinuous_toFinite μ)
  have heq := Kernel.withDensity_rnDeriv_eq (κ := K) (η := η) hKν
  rw [Kernel.withDensity_apply η (Kernel.measurable_rnDeriv K η)] at heq
  change ν.withDensity (K.rnDeriv η x) = K x at heq
  change K x = μ.withDensity (fun y => q y * K.rnDeriv η x y)
  rw [show (fun y => q y * K.rnDeriv η x y) = q * K.rnDeriv η x by rfl,
    withDensity_mul μ hq (Kernel.measurable_rnDeriv_right K η x), hν]
  exact heq.symm

/-- A finite absolutely continuous kernel has a jointly measurable nonnegative
real-valued Lebesgue density. -/
theorem u2_kernel_measurable_real_density_of_absolutelyContinuous {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) [IsFiniteKernel K]
    (hK : ∀ x, K x ≪ (volume : Measure (Vec d))) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      ∀ x, K x = (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨q, hq, hrep⟩ := u2_kernel_measurable_density_of_absolutelyContinuous K hK
  refine ⟨fun x y => (q x y).toReal, ENNReal.measurable_toReal.comp hq,
    fun x y => ENNReal.toReal_nonneg, fun x => ?_⟩
  have hqx : Measurable (q x) := hq.comp (measurable_const.prodMk measurable_id)
  have hfin : (∫⁻ y, q x y ∂(volume : Measure (Vec d))) ≠ ∞ := by
    have hm : (volume : Measure (Vec d)).withDensity (q x) Set.univ ≠ ∞ := by
      rw [← hrep x]
      exact measure_ne_top (K x) Set.univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm
  have hae := ae_lt_top hqx hfin
  rw [hrep x]
  apply withDensity_congr_ae
  filter_upwards [hae] with y hy
  exact (ENNReal.ofReal_toReal hy.ne).symm

/-- Measure domination bounds each real density almost everywhere. -/
theorem u2_real_density_ae_le_of_domination {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) (p : Vec d → Vec d → ℝ)
    (hp : Measurable (Function.uncurry p))
    (hrep : ∀ x, K x = (volume : Measure (Vec d)).withDensity
      (fun y => ENNReal.ofReal (p x y)))
    (M : ℝ) (hM : 0 ≤ M)
    (hdom : ∀ x, K x ≤ ENNReal.ofReal M • (volume : Measure (Vec d))) :
    ∀ x, ∀ᵐ y ∂(volume : Measure (Vec d)), p x y ≤ M := by
  intro x
  have hpmeas : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
  have hae : (fun y => ENNReal.ofReal (p x y)) ≤ᵐ[volume]
      (fun _ => ENNReal.ofReal M) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hpmeas.ennreal_ofReal.aemeasurable
    intro s hs _
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs,
      withDensity_const, ← hrep x]
    exact Measure.le_iff.mp (hdom x) s hs
  filter_upwards [hae] with y hy
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp hy


/-- A dominated nonnegative density can be chosen jointly measurable and
bounded everywhere, without changing any of the represented measures. -/
theorem u2_real_density_bounded_of_domination {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) (p : Vec d → Vec d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hnonneg : ∀ x y, 0 ≤ p x y)
    (hrep : ∀ x, K x = (volume : Measure (Vec d)).withDensity
      (fun y => ENNReal.ofReal (p x y)))
    (M : ℝ) (hM : 0 ≤ M)
    (hdom : ∀ x, K x ≤ ENNReal.ofReal M • (volume : Measure (Vec d))) :
    ∃ q : Vec d → Vec d → ℝ, Measurable (Function.uncurry q) ∧
      (∀ x y, 0 ≤ q x y ∧ q x y ≤ M) ∧
      ∀ x, K x = (volume : Measure (Vec d)).withDensity
        (fun y => ENNReal.ofReal (q x y)) := by
  refine ⟨fun x y => min (p x y) M, hp.min measurable_const, ?_, ?_⟩
  · intro x y
    exact ⟨le_min (hnonneg x y) hM, min_le_right _ _⟩
  · intro x
    rw [hrep x]
    apply withDensity_congr_ae
    filter_upwards [u2_real_density_ae_le_of_domination K p hp hrep M hM hdom x] with y hy
    simp only [min_eq_left hy]


/-- A nonnegative real density of a Markov kernel has unit mass at each start. -/
theorem u2_markov_real_density_integrable_and_integral {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) [IsMarkovKernel K]
    (p : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hnonneg : ∀ x y, 0 ≤ p x y)
    (hrep : ∀ x, K x = (volume : Measure (Vec d)).withDensity
      (fun y => ENNReal.ofReal (p x y))) :
    ∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1 := by
  intro x
  have hpmeas : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
  have hm : (∫⁻ y, ENNReal.ofReal (p x y) ∂(volume : Measure (Vec d))) = 1 := by
    have he := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hrep x)
    simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using he.symm
  have hf : Integrable (fun y => (ENNReal.ofReal (p x y)).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hpmeas.ennreal_ofReal.aemeasurable (by rw [hm]; simp)
  have hi : Integrable (p x) volume := by
    simpa only [ENNReal.toReal_ofReal (hnonneg x _)] using hf
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hnonneg x))
  rw [hm] at he
  have := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (hnonneg x)), ENNReal.toReal_one] using this


/-- The actual physical L¹-to-L∞ estimate gives a jointly measurable density
at every starting point of the actual unforced kernel. -/
theorem u2_unforced_kernel_real_density_of_L1_to_Linfty {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ (g : Vec d → ℝ) (hg1 : Integrable g volume)
      (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)),
      ∀ᵐ x ∂(physicalReversibleMeasure ω hd 0),
        |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g) x| ≤
          M * ∫ y, |g y|) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      ∀ x, Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x =
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p x y)) := by
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t
  let : IsMarkovKernel K := ⟨fun x =>
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω 0 Λ hΛ hω hSmooth t x⟩⟩
  apply u2_kernel_measurable_real_density_of_absolutelyContinuous K
  intro x
  exact Measure.absolutelyContinuous_of_le_smul
    (u2_unforced_kernel_domination_of_L1_to_Linfty hd ω Λ hΛ hω hSmooth t M hM hbound x)

/-- A physical L¹-to-L∞ estimate supplies a bounded, normalized, jointly
measurable density representing all kernel integrals at every start. -/
theorem u2_unforced_kernel_bounded_density_of_L1_to_Linfty {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ (g : Vec d → ℝ) (hg1 : Integrable g volume)
      (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)),
      ∀ᵐ x ∂(physicalReversibleMeasure ω hd 0),
        |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g) x| ≤
          M * ∫ y, |g y|) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x (f : Vec d → ℝ),
        (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x) =
          ∫ y, p x y * f y := by
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t
  let : IsMarkovKernel K := ⟨fun x =>
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω 0 Λ hΛ hω hSmooth t x⟩⟩
  obtain ⟨p, hp, hn, hr⟩ :=
    u2_unforced_kernel_real_density_of_L1_to_Linfty hd ω Λ hΛ hω hSmooth t M hM hbound
  have hdom : ∀ x, K x ≤ ENNReal.ofReal M • (volume : Measure (Vec d)) :=
    u2_unforced_kernel_domination_of_L1_to_Linfty hd ω Λ hΛ hω hSmooth t M hM hbound
  obtain ⟨q, hq, hqbound, hqrep⟩ := u2_real_density_bounded_of_domination K p hp hn hr M hM hdom
  refine ⟨q, hq, hqbound, u2_markov_real_density_integrable_and_integral K q hq
    (fun x y => (hqbound x y).1) hqrep, ?_⟩
  intro x f
  have hqmeas : Measurable (q x) := hq.comp (measurable_const.prodMk measurable_id)
  rw [hqrep x, integral_withDensity_eq_integral_toReal_smul hqmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal ((hqbound x _).1), smul_eq_mul]

/-- At positive times the unforced physical kernel is absolutely continuous
with respect to Lebesgue measure at every starting point. -/
theorem u2_unforced_kernel_absolutelyContinuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x ≪
      (volume : Measure (Vec d)) := by
  exact u2_gmpPhysicalC0KernelSemigroup_unforced_absolutelyContinuous
    hd ω Λ hΛ hω hSmooth t ht x

/-- A jointly measurable Lebesgue density for the actual unforced physical
kernel at every starting point. -/
theorem u2_gmpPhysicalC0KernelSemigroup_unforced_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ p : Vec d → Vec d → ℝ≥0∞, Measurable (Function.uncurry p) ∧
      ∀ x, Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x =
        (volume : Measure (Vec d)).withDensity (p x) := by
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t
  let : IsMarkovKernel K := ⟨fun x =>
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω 0 Λ hΛ hω hSmooth t x⟩⟩
  exact u2_kernel_measurable_density_of_absolutelyContinuous K
    (u2_gmpPhysicalC0KernelSemigroup_unforced_absolutelyContinuous hd ω Λ hΛ hω hSmooth t ht)

/-- At positive times the actual unforced kernel has a bounded, jointly measurable
Lebesgue density representing its integrals at every starting point. -/
theorem u2_unforced_kernel_bounded_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∃ p : Vec d → Vec d → ℝ,
      Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x (f : Vec d → ℝ),
        (∫ y, f y ∂Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x) =
          ∫ y, p x y * f y := by
  obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
  exact ⟨M, hM, u2_unforced_kernel_bounded_density_of_L1_to_Linfty
    hd ω Λ hΛ hω hSmooth t M hM.le hbound⟩

/-- The actual unforced kernel itself is Lebesgue measure with a jointly
measurable nonnegative real density at every positive time and starting point. -/
theorem u2_unforced_kernel_real_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      ∀ x, Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x =
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
  exact u2_unforced_kernel_real_density_of_L1_to_Linfty
    hd ω Λ hΛ hω hSmooth t M hM.le hbound





/-- An almost-everywhere compact-test bound for a Feller kernel holds at every start. -/
theorem u2_finite_kernel_domination_of_ae_compact_tests {d : ℕ}
    (K : ProbabilityTheory.Kernel (Vec d) (Vec d)) [ProbabilityTheory.IsFiniteKernel K]
    (M : ℝ) (hM : 0 ≤ M)
    (hcont : ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      Continuous (fun x => ∫ y, f y ∂K x))
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂K x) ≤ M * ∫ y, f y) :
    ∀ x, K x ≤ ENNReal.ofReal M • (volume : Measure (Vec d)) := by
  intro x
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal M • (volume : Measure (Vec d))) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  apply u2_measure_le_of_compact_continuous_tests
  intro f hf hfc hfn
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have hc : Continuous (fun x => ∫ y, f y ∂K x) := hcont g
  have hclosed : IsClosed {x : Vec d | (∫ y, f y ∂K x) ≤ M * ∫ y, f y} :=
    isClosed_le hc continuous_const
  have hdense := Measure.dense_of_ae (hbound f hf hfc hfn)
  have hall : {x : Vec d | (∫ y, f y ∂K x) ≤ M * ∫ y, f y} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hx : (∫ y, f y ∂K x) ≤ M * ∫ y, f y := by
    have : x ∈ {x : Vec d | (∫ y, f y ∂K x) ≤ M * ∫ y, f y} := by
      rw [hall]
      exact Set.mem_univ x
    exact this
  simpa [integral_smul_measure, ENNReal.toReal_ofReal hM, smul_eq_mul] using hx

/-- The unforced regular physical kernel has a uniform Lebesgue domination bound
at every starting point, including for nonsmooth coefficients. -/
theorem u2_regular_unforced_kernel_domination {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ M : ℝ, 0 < M ∧ ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        ENNReal.ofReal M • (volume : Measure (Vec d)) := by
  obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
  refine ⟨M, hM, ?_⟩
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  apply u2_finite_kernel_domination_of_ae_compact_tests (P t) M hM.le
  · intro f
    change Continuous (fun x => ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x))
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω 0 Λ hΛ hω t f).continuous
  · intro f hf hfc hfn
    have hf1 : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
    have hf2 := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 f hf hfc
    let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
    have hac : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
      Measure.absolutelyContinuous_of_le_smul
        (u4_unforced_physical_measure_comparable hd ω Λ hω).2
    have he := u2RegularC0KernelSemigroup_integral_ae hd ω 0 Λ hΛ hω t g
      (hf2.toLp f) hf2.coeFn_toLp
    filter_upwards [hac.ae_eq he, hac.ae_le (hbound f hf1 hf2)] with x he hb
    change (∫ y, f y ∂P t x) = _ at he
    rw [he]
    calc
      _ ≤ |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hf2.toLp f) x| := le_abs_self _
      _ ≤ M * ∫ y, |f y| := hb
      _ = M * ∫ y, f y := by simp only [abs_of_nonneg (hfn _)]

/-- At each positive time the unforced regular physical kernel has a jointly
measurable, bounded Lebesgue density at every starting point. -/
theorem u2_regular_unforced_kernel_bounded_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (p : Vec d → Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry p) ∧ (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hac : ∀ x, P t x ≪ (volume : Measure (Vec d)) :=
    fun x => Measure.absolutelyContinuous_of_le_smul (hdom x)
  obtain ⟨p, hp, hn, hr⟩ := u2_kernel_measurable_real_density_of_absolutelyContinuous (P t) hac
  obtain ⟨q, hq, hqb, hqr⟩ := u2_real_density_bounded_of_domination (P t) p hp hn hr M hM.le hdom
  exact ⟨M, q, hM, hq, hqb, hqr⟩

/-- The positive-time unforced regular kernel has a bounded, normalized,
jointly measurable Lebesgue density representing its integrals at every start. -/
theorem u2_regular_unforced_kernel_normalized_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (p : Vec d → Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry p) ∧ (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x (f : Vec d → ℝ),
        (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) =
          ∫ y, p x y * f y := by
  obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
    u2_regular_unforced_kernel_bounded_density hd ω Λ hΛ hω t ht
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let : IsMarkovKernel (P t) := ⟨fun x =>
    ⟨u2_regular_kernel_conservative hd ω 0 Λ hΛ hω t x⟩⟩
  refine ⟨M, p, hM, hp, hpb,
    u2_markov_real_density_integrable_and_integral (P t) p hp (fun x y => (hpb x y).1) hrep, ?_⟩
  intro x f
  have hpmeas : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
  rw [hrep x, integral_withDensity_eq_integral_toReal_smul hpmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) f]
  simp only [ENNReal.toReal_ofReal ((hpb x _).1), smul_eq_mul]

/-- The positive-time unforced kernel maps Lebesgue-integrable functions to
continuous functions, using the uniform density bound and compact approximations. -/
theorem u2_regular_unforced_kernel_integral_continuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (f : Vec d → ℝ) (hf : Integrable f volume) :
    Continuous (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) := by
  obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  have htransfer : ∀ (g : Vec d → ℝ), Integrable g volume → ∀ x, Integrable g (P t x) := by
    intro g hg x
    exact memLp_one_iff_integrable.mp <| (memLp_one_iff_integrable.mpr hg).of_measure_le_smul
      (c := ENNReal.ofReal M) ENNReal.ofReal_ne_top (hdom x)
  have hbound : ∀ (g : Vec d → ℝ), Integrable g volume → ∀ x,
      |∫ y, g y ∂P t x| ≤ M * ∫ y, |g y| := by
    intro g hg x
    calc
      |∫ y, g y ∂P t x| ≤ ∫ y, |g y| ∂P t x := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm g
      _ ≤ M * ∫ y, |g y| := by
        apply integral_le_const_mul_of_measure_le (P t x) volume M hM.le (hdom x)
          (fun y => |g y|) (Filter.Eventually.of_forall fun y => abs_nonneg _)
        simpa only [Real.norm_eq_abs] using hg.norm
  apply Metric.continuous_iff.mpr
  intro x ε hε
  let δ : ℝ := ε / (3 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hgcomp, hgapprox, hgcont, hgint⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le hδ
  let g₀ : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g, hgcont⟩, hgcomp.is_zero_at_infty⟩
  have hcont : Continuous (fun x => ∫ y, g y ∂P t x) := by
    change Continuous (fun x => ∫ y, g₀ y ∂P t x)
    have hc := (u2RegularC0Semigroup hd ω 0 Λ hΛ hω t g₀).continuous
    convert hc using 1
    funext z
    exact u2RegularC0KernelSemigroup_integral hd ω 0 Λ hΛ hω t g₀ z
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (ε / 3) (by positivity)
  refine ⟨η, hη, fun z hz => ?_⟩
  have herror : ∀ z, |(∫ y, f y ∂P t z) - ∫ y, g y ∂P t z| ≤ M * δ := by
    intro z
    rw [← integral_sub (htransfer f hf z) (htransfer g hgint z)]
    calc
      _ ≤ M * ∫ y, |(f - g) y| := hbound (f - g) (hf.sub hgint) z
      _ ≤ M * δ := mul_le_mul_of_nonneg_left (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hgapprox) hM.le
  have hclose := hηbound hz
  simp only [Real.dist_eq] at hclose ⊢
  have hsmall : M * δ < ε / 3 := by
    dsimp [δ]
    have hden : 0 < 3 * (M + 1) := by positivity
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    rw [show M * (ε / (3 * (M + 1))) * 3 = (3 * M * ε) / (3 * (M + 1)) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith
  have ha := abs_sub_le (∫ y, f y ∂P t z) (∫ y, g y ∂P t z) (∫ y, f y ∂P t x)
  have hb := abs_sub_le (∫ y, g y ∂P t z) (∫ y, g y ∂P t x) (∫ y, f y ∂P t x)
  have hc := herror x
  rw [abs_sub_comm] at hc
  have hzerr := herror z
  linarith


/-- At positive time the unforced regular kernel sees the square-cutoff
 generator estimate at every start, uniformly over centers and scales. -/
theorem u2_regular_unforced_kernel_squareCutoff_generator_ae_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (x : Vec d) (t : ℝ≥0), 0 < t →
      ∀ᵐ y ∂(u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x),
        ∀ (z : Vec d) (k : Fin d) (a : ℝ), 0 < a →
          |physicalGenerator (firstCoordinateIndex hd) ω 0
            (Blueprint.gmpPhysicalCoordinateMomentCutoff z k 1 a) y| ≤ A * |y k - z k| + B := by
  obtain ⟨A, B, hA, hB, hg⟩ :=
    u2_regular_coordinateSquareCutoff_generator_ae_bound hd ω 0 Λ hΛ hω
  refine ⟨A, B, hA, hB, ?_⟩
  intro x t ht
  obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  have hac : u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := Measure.absolutelyContinuous_of_le_smul (hdom x)
  exact (Measure.ae_le_iff_absolutelyContinuous.mpr hac)
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mp hg)

/-- The unforced regular square-cutoff generator is integrable at every
positive time and its expectation grows at most linearly with time. -/
theorem u2_regular_unforced_kernel_squareCutoff_generator_integral_le {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ (t : ℝ≥0), 0 < t →
        Integrable (physicalGenerator (firstCoordinateIndex hd) ω 0
          (Blueprint.gmpPhysicalCoordinateMomentCutoff x k 1 a))
          (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) ∧
        (∫ y, physicalGenerator (firstCoordinateIndex hd) ω 0
          (Blueprint.gmpPhysicalCoordinateMomentCutoff x k 1 a) y ∂
          (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x)) ≤ A + B * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hbound⟩ :=
    u2_regular_unforced_kernel_squareCutoff_generator_ae_bound hd ω Λ hΛ hω
  obtain ⟨C, hC, hm⟩ := u2_regular_kernel_coordinateAbs_integrable_le hd ω 0 Λ hΛ hω
  refine ⟨A + B, A * C, add_nonneg hA hB, mul_nonneg hA hC, ?_⟩
  intro x k a ha t ht
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let μ := P t x
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let : IsProbabilityMeasure μ := ⟨u2_regular_kernel_conservative hd ω 0 Λ hΛ hω t x⟩
  obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
  have hv : μ ≪ (volume : Measure (Vec d)) := Measure.absolutelyContinuous_of_le_smul (hdom x)
  have hp : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
    Measure.absolutelyContinuous_of_le_smul (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  let φ := Blueprint.gmpPhysicalCoordinateMomentCutoff x k 1 a
  have hφ := Blueprint.gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hgmeas : AEStronglyMeasurable (physicalGenerator (firstCoordinateIndex hd) ω 0 φ) μ :=
    (sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω 0 hφ.1 hφ.2.1).aestronglyMeasurable.mono_ac (hv.trans hp)
  have hi := (hm x k t).1
  have hh : Integrable (fun y => A * |y k - x k| + B) μ :=
    (hi.const_mul A).add (integrable_const B)
  have he := hbound x t ht
  have hg : Integrable (physicalGenerator (firstCoordinateIndex hd) ω 0 φ) μ := by
    apply hh.mono' hgmeas
    filter_upwards [he] with y hy
    simpa only [Real.norm_eq_abs] using hy x k a ha
  refine ⟨hg, ?_⟩
  have h := integral_mono_ae hg hh (he.mono fun y hy => (abs_le.mp (hy x k a ha)).2)
  have hcalc : (∫ y, A * |y k - x k| + B ∂μ) =
      A * (∫ y, |y k - x k| ∂μ) + B := by
    rw [integral_add (hi.const_mul A) (integrable_const B), integral_const_mul]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rfl
  rw [hcalc] at h
  have hmul := mul_le_mul_of_nonneg_left (hm x k t).2 hA
  change (∫ y, physicalGenerator (firstCoordinateIndex hd) ω 0 φ y ∂μ) ≤ _
  nlinarith





/-- On an open set, compact-test lower bounds for the regular physical kernel
that hold almost everywhere extend to every starting point. -/
theorem u2_regular_kernel_lower_of_ae_compact_tests {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (ν : Measure (Vec d)) [IsLocallyFiniteMeasure ν] [ν.InnerRegular]
    (U : Set (Vec d)) (hU : IsOpen U)
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)).restrict U,
        (∫ y, f y ∂ν) ≤
          ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) :
    ∀ x ∈ U, ν ≤ u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x := by
  let : IsMarkovKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) :=
    ⟨fun x => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩⟩
  apply u2_kernel_lower_of_ae_compact_tests _ ν U hU
  · intro f
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t f).continuous
  · exact hbound

/-- A compact-test lower estimate for the weighted physical evolution transfers
to the actual regular kernel at every start in the open set. -/
theorem u2_regular_unforced_kernel_lower_of_l2_compact_tests {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (ν : Measure (Vec d)) [IsLocallyFiniteMeasure ν] [ν.InnerRegular]
    (U : Set (Vec d)) (hU : IsOpen U)
    (hbound : ∀ (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f),
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)).restrict U,
        (∫ y, f y ∂ν) ≤
          Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
            ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 f hf hfc).toLp f) x) :
    ∀ x ∈ U, ν ≤ u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  apply u2_regular_kernel_lower_of_ae_compact_tests hd ω 0 Λ hΛ hω t ν U hU
  intro f hf hfc hfn
  have hf2 := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 f hf hfc
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have hac : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
    Measure.absolutelyContinuous_of_le_smul
      (u4_unforced_physical_measure_comparable hd ω Λ hω).2
  have he := u2RegularC0KernelSemigroup_integral_ae hd ω 0 Λ hΛ hω t g
    (hf2.toLp f) hf2.coeFn_toLp
  filter_upwards [ae_restrict_of_ae (hac.ae_eq he), hbound f hf hfc hfn] with x he hb
  change (∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x)) = _ at he
  rw [he]
  exact hb

end EinsteinFull

