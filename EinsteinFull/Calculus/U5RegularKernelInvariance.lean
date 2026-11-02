import EinsteinFull.Calculus.U2GMPRegularRealization
import EinsteinFull.Calculus.U2GMPKernelReversibility

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
/- The compact approximation and rectangle extension arguments below adapt
   U1GMPKernelL2 and U2GMPKernelReversibility to the regular spatial kernel. -/
namespace EinsteinFull
open EinsteinRelation.External.GantertSection7Support

/-- The regular kernel and weighted semigroup agree on compact tests. -/
theorem u5_regular_integral_ae_L2_compact {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    let hm := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hc
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      Integrable f (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ∧
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      (∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) =
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hm.toLp f) x) := by
  constructor
  · filter_upwards with x
    let : IsProbabilityMeasure (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    exact hf.integrable_of_hasCompactSupport hc
  · exact u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t
      (Blueprint.gmpPhysicalCompactC0 f hf hc) _
      (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hc).coeFn_toLp

/-- A compact cutoff of the starting point cannot increase the mass of a
nonnegative compact observable. -/
theorem u5_regular_kernel_compact_mass_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f g : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hf0 : ∀ x, 0 ≤ f x) (hg1 : ∀ x, g x ≤ 1) :
    (∫ x, (∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) * g x ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x, f x ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let F := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f
  let G := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hg hgc).toLp g
  have hF : (F : Vec d → ℝ) =ᵐ[μ] f :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).coeFn_toLp
  have hPG : (fun x => ∫ y, g y ∂(P t x)) =ᵐ[μ]
      (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t G : Vec d → ℝ) :=
    (u5_regular_integral_ae_L2_compact hd ω lam Λ hΛ hω t g hg hgc).2
  have hi : Integrable (fun x => f x * (∫ y, g y ∂(P t x))) μ := by
    apply Integrable.congr (L2.integrable_inner (𝕜 := ℝ) F
      (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t G))
    filter_upwards [hF, hPG] with x hfx hgx
    simp only [RCLike.inner_apply', conj_trivial, hfx, hgx]
  have hfint : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  rw [u2_regular_kernel_compact_symmetry hd ω lam Λ hΛ hω t f g hf hfc hg hgc]
  apply integral_mono hi hfint
  intro x
  have hgint : Integrable g (P t x) := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    exact hg.integrable_of_hasCompactSupport hgc
  have hP : (∫ y, g y ∂(P t x)) ≤ 1 := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    simpa using integral_mono hgint (integrable_const (1 : ℝ)) hg1
  calc
    f x * (∫ y, g y ∂(P t x)) ≤ f x * 1 := mul_le_mul_of_nonneg_left hP (hf0 x)
    _ = f x := mul_one _

/-- The kernel image of a nonnegative compact observable has no greater
Lebesgue integral than the observable itself. -/
theorem u5_regular_kernel_compact_lintegral_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ∂physicalReversibleMeasure ω hd lam) ≤
      ENNReal.ofReal (∫ x, f x ∂physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let χ : ℕ → Vec d → ℝ := fun n x => b (a n • x)
  let Q : Vec d → ℝ := fun x => ∫ y, f y ∂(P t x)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc (n : ℕ) : Continuous (χ n) := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (χ n) := b.contDiff.comp (contDiff_const_smul (a n))
    exact h.continuous
  have hcs (n : ℕ) : HasCompactSupport (χ n) := b.hasCompactSupport.comp_smul (ha n).ne'
  have hlim (x : Vec d) : Tendsto (fun n => χ n x) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => a n • x) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := x))
    have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
    simpa only [χ, hb0, Function.comp_def] using (b.continuous.tendsto 0).comp ht
  have hQ0 (x : Vec d) : 0 ≤ Q x := integral_nonneg hf0
  have hQm : StronglyMeasurable Q := hf.stronglyMeasurable.integral_kernel
  have hQlp : MemLp Q 2 μ := by
    have h := (u5_regular_integral_ae_L2_compact hd ω lam Λ hΛ hω t f hf hfc).2
    exact (memLp_congr_ae h).mpr (MeasureTheory.Lp.memLp (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
      ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f)))
  have hi (n : ℕ) : Integrable (fun x => Q x * χ n x) μ := by
    exact hQlp.integrable_mul (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (χ n) (hc n) (hcs n))
  have hnonneg (n : ℕ) : 0 ≤ᵐ[μ] fun x => Q x * χ n x :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (hQ0 x) b.nonneg)
  have hmeas (n : ℕ) : Measurable (fun x => ENNReal.ofReal (Q x * χ n x)) :=
    ((hQm.measurable.mul (hc n).measurable).ennreal_ofReal)
  have hbound (n : ℕ) : (∫⁻ x, ENNReal.ofReal (Q x * χ n x) ∂μ) ≤
      ENNReal.ofReal (∫ x, f x ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal
      (u5_regular_kernel_compact_mass_bound hd ω lam Λ hΛ hω t
        f (χ n) hf hfc (hc n) (hcs n) hf0 (fun x => b.le_one))
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (Q x * χ n x)) atTop ∂μ := by
      apply lintegral_congr
      intro x
      have ht : Tendsto (fun n => ENNReal.ofReal (Q x * χ n x)) atTop
          (𝓝 (ENNReal.ofReal (Q x))) := by
        simpa only [Function.comp_def, mul_one] using
          (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul (hlim x))
      exact ht.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (Q x * χ n x) ∂μ) atTop :=
      lintegral_liminf_le hmeas
    _ ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
      have hh : liminf (fun n => ∫⁻ x, ENNReal.ofReal (Q x * χ n x) ∂μ) atTop ≤
          liminf (fun _ : ℕ => ENNReal.ofReal (∫ x, f x ∂μ)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
      simpa only [Filter.liminf_const] using hh

/-- The composed physical kernel is dominated on compact sets. -/
theorem u5_regular_kernel_compact_measure_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ((u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∘ₘ
      physicalReversibleMeasure ω hd lam) K ≤ physicalReversibleMeasure ω hd lam K := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let ν := P ∘ₘ μ
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have htest (f : Vec d → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
      (hf0 : ∀ x, 0 ≤ f x) :
      (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
    change (∫⁻ x, ENNReal.ofReal (f x) ∂(μ.bind P)) ≤ _
    rw [Measure.lintegral_bind P.aemeasurable hf.measurable.ennreal_ofReal.aemeasurable]
    calc
      _ = ∫⁻ x, ENNReal.ofReal (∫ y, f y ∂(P x)) ∂μ := by
        apply lintegral_congr
        intro x
        let : IsProbabilityMeasure (P x) :=
          ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
        exact (ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hc)
          (Filter.Eventually.of_forall hf0)).symm
      _ ≤ _ := u5_regular_kernel_compact_lintegral_bound hd ω lam Λ hΛ hω t f hf hc hf0
  change ν K ≤ μ K
  rw [hK.measure_eq_biInf_integral_hasCompactSupport μ]
  refine le_iInf fun f => le_iInf fun hf => le_iInf fun hc => le_iInf fun hfK => le_iInf fun hf0 => ?_
  calc
    ν K = ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
      rw [lintegral_indicator hK.measurableSet]
      simp
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · simp [hx, hfK hx]
      · simp [hx]
    _ ≤ _ := htest f hf hc hf0

/-- The actual conservative spatial kernel is subinvariant for the physical
reversible measure. -/
theorem u5_regular_kernel_subinvariant {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) :
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∘ₘ
      physicalReversibleMeasure ω hd lam ≤ physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let ν := (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∘ₘ μ
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hcompact (K : Set (Vec d)) (hK : IsCompact K) : ν K ≤ μ K :=
    u5_regular_kernel_compact_measure_bound hd ω lam Λ hΛ hω t K hK
  let : IsLocallyFiniteMeasure ν := ⟨fun x => by
    obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
    exact ⟨K, hx, (hcompact K hK).trans_lt hK.measure_lt_top⟩⟩
  change ν ≤ μ
  apply Measure.le_iff.mpr
  intro s hs
  apply le_of_forall_lt
  intro r hr
  obtain ⟨K, hKs, hK, hrK⟩ := hs.exists_lt_isCompact hr
  exact hrK.trans_le ((hcompact K hK).trans (measure_mono hKs))


/-- Symmetry extends from compact continuous tests to compact indicators. -/
theorem u5_regular_kernel_compact_indicator_symmetry {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (A B : Set (Vec d)) (hA : IsCompact A) (hB : IsCompact B) :
    let μ := physicalReversibleMeasure ω hd lam
    let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
    (∫ x, (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(P t x)) *
      B.indicator (fun _ => (1 : ℝ)) x ∂μ) =
    ∫ x, A.indicator (fun _ => (1 : ℝ)) x *
      (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂(P t x)) ∂μ := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  obtain ⟨c, f, hc, hcc, hcb, hf, hfb, hfl⟩ := u2_compact_indicator_approximation A hA
  obtain ⟨e, g, he, hec, heb, hg, hgb, hgl⟩ := u2_compact_indicator_approximation B hB
  have hfb1 (n : ℕ) (x : Vec d) : 0 ≤ f n x ∧ f n x ≤ 1 :=
    ⟨(hfb n x).1, (hfb n x).2.trans (hcb x).2⟩
  have hgb1 (n : ℕ) (x : Vec d) : 0 ≤ g n x ∧ g n x ≤ 1 :=
    ⟨(hgb n x).1, (hgb n x).2.trans (heb x).2⟩
  have hPf (n : ℕ) (x : Vec d) : 0 ≤ (∫ y, f n y ∂(P t x)) ∧
      (∫ y, f n y ∂(P t x)) ≤ 1 := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    constructor
    · exact integral_nonneg fun y => (hfb1 n y).1
    · simpa using integral_mono ((hf n).1.integrable_of_hasCompactSupport (hf n).2)
        (integrable_const (μ := P t x) (1 : ℝ)) (fun y => (hfb1 n y).2)
  have hPg (n : ℕ) (x : Vec d) : 0 ≤ (∫ y, g n y ∂(P t x)) ∧
      (∫ y, g n y ∂(P t x)) ≤ 1 := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    constructor
    · exact integral_nonneg fun y => (hgb1 n y).1
    · simpa using integral_mono ((hg n).1.integrable_of_hasCompactSupport (hg n).2)
        (integrable_const (μ := P t x) (1 : ℝ)) (fun y => (hgb1 n y).2)
  have hPfl (x : Vec d) : Tendsto (fun n => ∫ y, f n y ∂(P t x)) atTop
      (𝓝 (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(P t x))) := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    exact u2_probability_integral_approximation (P t x) f _ (fun n => (hf n).1) hfb1 hfl
  have hPgl (x : Vec d) : Tendsto (fun n => ∫ y, g n y ∂(P t x)) atTop
      (𝓝 (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂(P t x))) := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    exact u2_probability_integral_approximation (P t x) g _ (fun n => (hg n).1) hgb1 hgl
  have hl : Tendsto (fun n => ∫ x, (∫ y, f n y ∂(P t x)) * g n x ∂μ) atTop
      (𝓝 (∫ x, (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(P t x)) *
        B.indicator (fun _ => (1 : ℝ)) x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence e
    · intro n
      exact (((hf n).1.stronglyMeasurable.integral_kernel).mul
        (hg n).1.stronglyMeasurable).aestronglyMeasurable
    · exact he.integrable_of_hasCompactSupport hec
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hPf n x).1 (hgb n x).1)]
      calc
        (∫ y, f n y ∂(P t x)) * g n x ≤ 1 * g n x :=
          mul_le_mul_of_nonneg_right (hPf n x).2 (hgb n x).1
        _ ≤ e x := by simpa using (hgb n x).2
    · exact Filter.Eventually.of_forall (fun x => (hPfl x).mul (hgl x))
  have hr : Tendsto (fun n => ∫ x, f n x * (∫ y, g n y ∂(P t x)) ∂μ) atTop
      (𝓝 (∫ x, A.indicator (fun _ => (1 : ℝ)) x *
        (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂(P t x)) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence c
    · intro n
      exact ((hf n).1.stronglyMeasurable.mul
        ((hg n).1.stronglyMeasurable.integral_kernel)).aestronglyMeasurable
    · exact hc.integrable_of_hasCompactSupport hcc
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfb n x).1 (hPg n x).1)]
      calc
        f n x * (∫ y, g n y ∂(P t x)) ≤ f n x * 1 :=
          mul_le_mul_of_nonneg_left (hPg n x).2 (hfb n x).1
        _ ≤ c x := by simpa using (hfb n x).2
    · exact Filter.Eventually.of_forall (fun x => (hfl x).mul (hPgl x))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards with n
  exact (u2_regular_kernel_compact_symmetry hd ω lam Λ hΛ hω t
    (f n) (g n) (hf n).1 (hf n).2 (hg n).1 (hg n).2).symm

/-- The actual physical kernel is reversible on compact rectangles. -/
theorem u5_regular_kernel_compact_rectangles {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0)
    (A B : Set (Vec d)) (hA : IsCompact A) (hB : IsCompact B) :
    let μ := physicalReversibleMeasure ω hd lam
    let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
    (∫⁻ x in A, K t x B ∂μ) = ∫⁻ y in B, K t y A ∂μ := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have bridge (S T : Set (Vec d)) (hS : IsCompact S) (hT : IsCompact T) :
      (∫⁻ x in S, K t x T ∂μ) = ENNReal.ofReal
        (∫ x, S.indicator (fun _ => (1 : ℝ)) x *
          (∫ y, T.indicator (fun _ => (1 : ℝ)) y ∂(K t x)) ∂μ) := by
    let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
    have hp (x : Vec d) : (K t x T).toReal ≤ 1 := by
      let : IsProbabilityMeasure (K t x) :=
        ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
      have h := ENNReal.toReal_mono (measure_ne_top (K t x) Set.univ)
        (measure_mono (Set.subset_univ T))
      simpa using h
    have hi : Integrable (fun x => (K t x T).toReal) (μ.restrict S) := by
      apply (integrable_const (1 : ℝ)).mono'
        (Kernel.measurable_coe (K t) hT.isClosed.measurableSet).ennreal_toReal.aestronglyMeasurable
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact hp x
    have hfun : (fun x => S.indicator (fun _ => (1 : ℝ)) x *
        (∫ y, T.indicator (fun _ => (1 : ℝ)) y ∂(K t x))) =
        S.indicator (fun x => (K t x T).toReal) := by
      funext x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx, one_mul]
        simpa [measureReal_def] using
          (integral_indicator_const (μ := K t x) (1 : ℝ) hT.isClosed.measurableSet)
      · simp [hx]
    rw [hfun, integral_indicator hS.isClosed.measurableSet,
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    apply lintegral_congr
    intro x
    let : IsProbabilityMeasure (K t x) :=
      ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    exact (ENNReal.ofReal_toReal (measure_ne_top (K t x) T)).symm
  change (∫⁻ x in A, K t x B ∂μ) = ∫⁻ y in B, K t y A ∂μ
  rw [bridge A B hA hB, bridge B A hB hA]
  congr 1
  have h := u5_regular_kernel_compact_indicator_symmetry
    hd ω lam Λ hΛ hω t A B hA hB
  simpa [mul_comm] using h.symm

/-- Extend balance in one variable using local finiteness and compact regularity. -/
private theorem u5_extend_rectangles {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (S : Set (Vec d))
    (hcompact : ∀ T : Set (Vec d), IsCompact T →
      (∫⁻ x in S, (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t x T
        ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y in T, (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t y S
        ∂physicalReversibleMeasure ω hd lam) :
    ∀ T : Set (Vec d), MeasurableSet T →
      (∫⁻ x in S, (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t x T
        ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y in T, (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t y S
        ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let ν := (μ.restrict S).bind K
  let ρ := μ.withDensity (fun y => K y S)
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hν : ν ≤ μ := by
    apply Measure.le_iff.mpr
    intro T hT
    calc
      ν T = ∫⁻ x in S, K x T ∂μ := Measure.bind_apply hT K.aemeasurable
      _ ≤ ∫⁻ x, K x T ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = (K ∘ₘ μ) T := (Measure.bind_apply hT K.aemeasurable).symm
      _ ≤ μ T := u5_regular_kernel_subinvariant hd ω lam Λ hΛ hω t T
  have hρ : ρ ≤ μ := by
    apply Measure.le_iff.mpr
    intro T hT
    rw [show ρ T = ∫⁻ y in T, K y S ∂μ from withDensity_apply _ hT]
    calc
      _ ≤ ∫⁻ _ in T, (1 : ℝ≥0∞) ∂μ := by
        apply lintegral_mono
        intro y
        calc
          K y S ≤ K y Set.univ := measure_mono (Set.subset_univ S)
          _ = 1 := u2_regular_kernel_conservative hd ω lam Λ hΛ hω t y
      _ = μ T := by simp
  let : IsLocallyFiniteMeasure ν := ⟨fun x => by
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    exact ⟨C, hx, (hν C).trans_lt hC.measure_lt_top⟩⟩
  let : IsLocallyFiniteMeasure ρ := ⟨fun x => by
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    exact ⟨C, hx, (hρ C).trans_lt hC.measure_lt_top⟩⟩
  have heq : ν = ρ := by
    apply le_antisymm <;> apply Measure.le_iff.mpr <;> intro T hT <;>
      apply le_of_forall_lt <;> intro r hr
    · obtain ⟨C, hCT, hC, hrC⟩ := hT.exists_lt_isCompact hr
      have hc : ν C = ρ C := by
        rw [show ν C = ∫⁻ x in S, K x C ∂μ from Measure.bind_apply hC.measurableSet K.aemeasurable,
          show ρ C = ∫⁻ y in C, K y S ∂μ from withDensity_apply _ hC.measurableSet]
        exact hcompact C hC
      exact hrC.trans_le (hc.le.trans (measure_mono hCT))
    · obtain ⟨C, hCT, hC, hrC⟩ := hT.exists_lt_isCompact hr
      have hc : ν C = ρ C := by
        rw [show ν C = ∫⁻ x in S, K x C ∂μ from Measure.bind_apply hC.measurableSet K.aemeasurable,
          show ρ C = ∫⁻ y in C, K y S ∂μ from withDensity_apply _ hC.measurableSet]
        exact hcompact C hC
      exact hrC.trans_le (hc.symm.le.trans (measure_mono hCT))
  intro T hT
  have h := congrArg (fun m : Measure (Vec d) => m T) heq
  simpa only [ν, ρ, Measure.bind_apply hT K.aemeasurable, withDensity_apply _ hT] using h

/-- The actual physical kernel is reversible on all measurable rectangles. -/
theorem u5_regular_kernel_measurable_rectangles {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let μ := physicalReversibleMeasure ω hd lam
    let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
    (∫⁻ x in A, K t x B ∂μ) = ∫⁻ y in B, K t y A ∂μ := by
  apply u5_extend_rectangles hd ω lam Λ hΛ hω t A ?_ B hB
  intro C hC
  symm
  apply u5_extend_rectangles hd ω lam Λ hΛ hω t C ?_ A hA
  intro D hD
  exact u5_regular_kernel_compact_rectangles hd ω lam Λ hΛ hω t C D hC hD

/-- The physical reversible measure is invariant for the actual spatial kernel. -/
theorem u5_regular_kernel_invariant {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) :
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∘ₘ (physicalReversibleMeasure ω hd lam) = physicalReversibleMeasure ω hd lam := by
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let μ := physicalReversibleMeasure ω hd lam
  change K ∘ₘ μ = μ
  ext S hS
  rw [Measure.bind_apply hS K.aemeasurable]
  have h := u5_regular_kernel_measurable_rectangles hd ω lam Λ hΛ hω t Set.univ S MeasurableSet.univ hS
  change (∫⁻ x in Set.univ, K x S ∂μ) = ∫⁻ y in S, K y Set.univ ∂μ at h
  have hcons (y : Vec d) : K y Set.univ = 1 :=
    u2_regular_kernel_conservative hd ω lam Λ hΛ hω t y
  simpa only [Measure.restrict_univ, hcons, lintegral_const, one_mul, Measure.restrict_apply_univ] using h

/-- The physical reversible measure is invariant under the regular signed kernel. -/
theorem u5_regular_kernel_physical_measure_invariant {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (f : Vec d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
      ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y, f y ∂physicalReversibleMeasure ω hd lam := by
  rw [← Measure.lintegral_bind (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t).aemeasurable hf.aemeasurable]
  rw [u5_regular_kernel_invariant hd ω lam Λ hΛ hω t]

/-- The regular physical kernel is reversible for all nonnegative measurable tests. -/
theorem u5_regular_kernel_full_reversibility {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (f g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * (∫⁻ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
      ∂physicalReversibleMeasure ω hd lam) =
    (∫⁻ x, g x * (∫⁻ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
      ∂physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  have hrect (B : Set (Vec d)) (hB : MeasurableSet B) :
      (μ.restrict B).bind K = μ.withDensity (fun x => K x B) := by
    ext A hA
    rw [Measure.bind_apply hA K.aemeasurable, withDensity_apply _ hA]
    exact u5_regular_kernel_measurable_rectangles hd ω lam Λ hΛ hω t B A hB hA
  have hbase (B : Set (Vec d)) (hB : MeasurableSet B) :
      (∫⁻ x, f x * K x B ∂μ) = ∫⁻ x in B, ∫⁻ y, f y ∂K x ∂μ := by
    calc
      _ = ∫⁻ x, f x ∂μ.withDensity (fun x => K x B) := by
        rw [lintegral_withDensity_eq_lintegral_mul μ (Kernel.measurable_coe K hB) hf]
        simp only [Pi.mul_apply, mul_comm]
      _ = ∫⁻ x, f x ∂((μ.restrict B).bind K) := by rw [hrect B hB]
      _ = _ := Measure.lintegral_bind K.aemeasurable hf.aemeasurable
  change (∫⁻ x, f x * (∫⁻ y, g y ∂K x) ∂μ) =
    ∫⁻ x, g x * (∫⁻ y, f y ∂K x) ∂μ
  refine Measurable.ennreal_induction (motive := fun g =>
    (∫⁻ x, f x * (∫⁻ y, g y ∂K x) ∂μ) =
      ∫⁻ x, g x * (∫⁻ y, f y ∂K x) ∂μ) ?_ ?_ ?_ hg
  · intro c B hB
    have hp : Measurable (fun x => ∫⁻ y, f y ∂K x) := hf.lintegral_kernel
    simp only [lintegral_indicator_const hB]
    simp_rw [← Set.indicator_mul_left B (fun _ => c) (fun x => ∫⁻ y, f y ∂K x),
      lintegral_indicator hB]
    calc
      _ = ∫⁻ x, c * (f x * K x B) ∂μ := by
        apply lintegral_congr
        intro x
        ac_rfl
      _ = c * (∫⁻ x, f x * K x B ∂μ) :=
        lintegral_const_mul c (hf.mul (Kernel.measurable_coe K hB))
      _ = c * (∫⁻ x in B, ∫⁻ y, f y ∂K x ∂μ) := by rw [hbase B hB]
      _ = _ := (lintegral_const_mul c hp).symm
  · intro g h _ hg hh ig ih
    simp only [Pi.add_apply, lintegral_add_left hg h, mul_add, add_mul]
    have hL : Measurable (fun x => f x * (∫⁻ y, g y ∂K x)) :=
      hf.mul (Measurable.lintegral_kernel (κ := K) hg)
    have hR : Measurable (fun x => g x * (∫⁻ y, f y ∂K x)) :=
      hg.mul (Measurable.lintegral_kernel (κ := K) hf)
    rw [lintegral_add_left hL _, lintegral_add_left hR _, ig, ih]
  · intro g hg hm ih
    have hk (n : ℕ) : Measurable (fun x => ∫⁻ y, g n y ∂K x) :=
      (hg n).lintegral_kernel
    have hmono : Monotone (fun n x => ∫⁻ y, g n y ∂K x) :=
      fun a b hab x => lintegral_mono (hm hab)
    have hl : Monotone (fun n x => f x * ∫⁻ y, g n y ∂K x) := by
      intro a b hab x
      change f x * (∫⁻ y, g a y ∂K x) ≤ f x * (∫⁻ y, g b y ∂K x)
      gcongr
      exact hm hab y
    have hr : Monotone (fun n x => g n x * ∫⁻ y, f y ∂K x) := by
      intro a b hab x
      change g a x * (∫⁻ y, f y ∂K x) ≤ g b x * (∫⁻ y, f y ∂K x)
      gcongr
      exact hm hab x
    simp_rw [lintegral_iSup (fun n => hg n) hm, ENNReal.mul_iSup, ENNReal.iSup_mul]
    calc
      _ = ⨆ n, ∫⁻ x, f x * (∫⁻ y, g n y ∂K x) ∂μ :=
        lintegral_iSup (fun n => hf.mul (hk n)) hl
      _ = ⨆ n, ∫⁻ x, g n x * (∫⁻ y, f y ∂K x) ∂μ := iSup_congr ih
      _ = _ := (lintegral_iSup (fun n => (hg n).mul hf.lintegral_kernel) hr).symm

#print axioms u5_regular_kernel_full_reversibility
#print axioms u5_regular_kernel_physical_measure_invariant
end EinsteinFull
