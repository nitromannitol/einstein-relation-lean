import EinsteinFull.Calculus.U2GMPNullPropagation
import EinsteinFull.Calculus.U2GMPKernelReversibility
import EinsteinFull.Calculus.U2GMPNashDomain
import EinsteinFull.Calculus.U8PhysicalUltracontractive
import Mathlib.MeasureTheory.Measure.OpenPos

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- A bound on a physical C₀-test evolution which holds almost everywhere in the
starting point in fact holds at every starting point. -/
theorem u2_gmpPhysicalC0KernelSemigroup_integral_bound_everywhere {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (b : ℝ)
    (hbound : ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ b) :
    ∀ x, (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ b := by
  have hc : Continuous (fun x =>
      ∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) := by
    simp_rw [Blueprint.gmpPhysicalC0KernelSemigroup_integral]
    exact (Blueprint.gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth t f).continuous
  have hclosed : IsClosed {x : Vec d | (∫ y, f y ∂
      (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ b} :=
    isClosed_le hc continuous_const
  have hdense := MeasureTheory.Measure.dense_of_ae hbound
  have hall : {x : Vec d | (∫ y, f y ∂
      (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ b} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  intro x
  have hx : x ∈ {x : Vec d | (∫ y, f y ∂
      (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ b} := by
    rw [hall]
    exact Set.mem_univ x
  exact hx

/-- Compact-set domination extends to all measurable sets by inner regularity. -/
theorem u2_measure_le_of_compact_le {d : ℕ} (μ ν : Measure (Vec d))
    [μ.InnerRegular] (h : ∀ K : Set (Vec d), IsCompact K → μ K ≤ ν K) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [hA.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  exact (h K hK).trans (measure_mono hKA)

/-- Domination on nonnegative compact continuous tests implies measure domination. -/
theorem u2_measure_le_of_compact_continuous_tests {d : ℕ} (μ ν : Measure (Vec d))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [μ.InnerRegular]
    (h : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ x, 0 ≤ f x) → (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  apply u2_measure_le_of_compact_le μ ν
  intro A hA
  obtain ⟨c, f, hc, hcc, hcb, hf, hfb, hfl⟩ := u2_compact_indicator_approximation A hA
  have hlim (ρ : Measure (Vec d)) [IsLocallyFiniteMeasure ρ] :
      Tendsto (fun n => ∫ x, f n x ∂ρ) atTop
        (𝓝 (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂ρ)) := by
    apply tendsto_integral_of_dominated_convergence c
    · intro n
      exact (hf n).1.aestronglyMeasurable
    · exact hc.integrable_of_hasCompactSupport hcc
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hfb n x).1]
      exact (hfb n x).2
    · exact Filter.Eventually.of_forall hfl
  have hi : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ) ≤
      ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂ν :=
    le_of_tendsto_of_tendsto (hlim μ) (hlim ν)
      (Filter.Eventually.of_forall fun n => h (f n) (hf n).1 (hf n).2 (fun x => (hfb n x).1))
  apply (ENNReal.toReal_le_toReal (hA.measure_ne_top (μ := μ))
    (hA.measure_ne_top (μ := ν))).1
  rw [integral_indicator_const (μ := μ) (1 : ℝ) hA.isClosed.measurableSet,
    integral_indicator_const (μ := ν) (1 : ℝ) hA.isClosed.measurableSet] at hi
  simpa [measureReal_def] using hi

/-- An almost-everywhere compact-test bound for a Feller kernel holds at every start. -/
theorem u2_kernel_domination_of_ae_compact_tests {d : ℕ}
    (K : ProbabilityTheory.Kernel (Vec d) (Vec d)) [ProbabilityTheory.IsMarkovKernel K]
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

/-- A bounded measurable representation of compact-test integrals yields
measure domination at every starting point. -/
theorem u2_kernel_domination_of_bounded_representation {d : ℕ}
    (K : ProbabilityTheory.Kernel (Vec d) (Vec d)) [ProbabilityTheory.IsMarkovKernel K]
    (M : ℝ) (hM : 0 ≤ M) (P : Vec d → Vec d → ℝ)
    (hP : Measurable (Function.uncurry P))
    (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hcont : ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      Continuous (fun x => ∫ y, f y ∂K x))
    (hrep : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (fun x => ∫ y, f y ∂K x) =ᵐ[volume] (fun x => ∫ y, P x y * f y)) :
    ∀ x, K x ≤ ENNReal.ofReal M • (volume : Measure (Vec d)) := by
  apply u2_kernel_domination_of_ae_compact_tests K M hM hcont
  intro f hf hfc hfn
  have hfi : Integrable f (volume : Measure (Vec d)) := hf.integrable_of_hasCompactSupport hfc
  filter_upwards [hrep f hf hfc] with x hx
  rw [hx]
  have hp : Measurable (P x) := hP.comp (measurable_const.prodMk measurable_id)
  have hpi : Integrable (fun y => P x y * f y) (volume : Measure (Vec d)) := by
    apply hfi.bdd_mul hp.aestronglyMeasurable
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hPb x y).1]
    exact (hPb x y).2
  calc
    _ ≤ ∫ y, M * f y := integral_mono_ae hpi (hfi.const_mul M)
      (Filter.Eventually.of_forall fun y => mul_le_mul_of_nonneg_right (hPb x y).2 (hfn y))
    _ = M * ∫ y, f y := integral_const_mul M f

/-- An L¹-to-L∞ estimate for the actual physical evolution transfers to
every starting point of its actual unforced kernel. -/
theorem u2_unforced_kernel_domination_of_L1_to_Linfty {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ (g : Vec d → ℝ) (hg1 : Integrable g volume)
      (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)),
      ∀ᵐ x ∂(physicalReversibleMeasure ω hd 0),
        |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g) x| ≤
          M * ∫ y, |g y|) :
    ∀ x, Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x ≤
      ENNReal.ofReal M • (volume : Measure (Vec d)) := by
  let : IsMarkovKernel (Blueprint.gmpPhysicalC0KernelSemigroup
      hd ω 0 Λ hΛ hω hSmooth t) := ⟨fun x =>
        ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω 0 Λ hΛ hω hSmooth t x⟩⟩
  apply u2_kernel_domination_of_ae_compact_tests _ M hM
  · intro f
    simp_rw [Blueprint.gmpPhysicalC0KernelSemigroup_integral]
    exact (Blueprint.gmpPhysicalC0Semigroup hd ω 0 Λ hΛ hω hSmooth t f).continuous
  · intro f hf hfc hfn
    have hf1 : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
    have hf2 := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 f hf hfc
    have hac : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
      Measure.absolutelyContinuous_of_le_smul
        (u4_unforced_physical_measure_comparable hd ω Λ hω).2
    filter_upwards [hac.ae_eq (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
      hd ω 0 Λ hΛ hω hSmooth t f hf2).2, hac.ae_le (hbound f hf1 hf2)] with x he hb
    rw [he]
    calc
      _ ≤ |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hf2.toLp f) x| := le_abs_self _
      _ ≤ M * ∫ y, |f y| := hb
      _ = M * ∫ y, f y := by simp only [abs_of_nonneg (hfn _)]

/-- The actual unforced physical kernel is absolutely continuous at every
starting point and every positive time. -/
theorem u2_gmpPhysicalC0KernelSemigroup_unforced_absolutelyContinuous
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    Blueprint.gmpPhysicalC0KernelSemigroup hd ω 0 Λ hΛ hω hSmooth t x ≪
      (volume : Measure (Vec d)) := by
  obtain ⟨M, hM, hbound⟩ := u8_unforced_physical_L1_to_Linfty hd ω Λ hΛ hω t ht
  exact Measure.absolutelyContinuous_of_le_smul
    (u2_unforced_kernel_domination_of_L1_to_Linfty hd ω Λ hΛ hω hSmooth t M hM.le hbound x)






end EinsteinFull
