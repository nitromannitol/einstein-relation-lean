import EinsteinFull.Calculus.U1GMPKernelL2
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.UrysohnsLemma

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull

open EinsteinRelation.External.GantertSection7Support

/-- A compact indicator has compactly supported continuous approximations,
with one common compactly supported upper bound. -/
theorem u2_compact_indicator_approximation {d : ℕ} (A : Set (Vec d))
    (hA : IsCompact A) :
    ∃ (c : Vec d → ℝ) (f : ℕ → Vec d → ℝ),
      Continuous c ∧ HasCompactSupport c ∧
      (∀ x, 0 ≤ c x ∧ c x ≤ 1) ∧
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n)) ∧
      (∀ n x, 0 ≤ f n x ∧ f n x ≤ c x) ∧
      (∀ x, Tendsto (fun n => f n x) atTop
        (𝓝 (A.indicator (fun _ => (1 : ℝ)) x))) := by
  obtain ⟨c, hcA, hcc, -, hcb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hA isOpen_univ (Set.subset_univ A)
  let f : ℕ → Vec d → ℝ := fun n x => c x * (hA.isClosed.apprSeq n x : ℝ)
  refine ⟨c, f, c.continuous, hcc, hcb, ?_, ?_, ?_⟩
  · intro n
    exact ⟨c.continuous.mul (continuous_subtype_val.comp (hA.isClosed.apprSeq n).continuous),
      HasCompactSupport.mul_right hcc⟩
  · intro n x
    have h1 : (hA.isClosed.apprSeq n x : ℝ) ≤ 1 := by
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hA.isClosed n x
    exact ⟨mul_nonneg (hcb x).1 (hA.isClosed.apprSeq n x).property,
      mul_le_of_le_one_right (hcb x).1 h1⟩
  · intro x
    have ht := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hA.isClosed)) x
    have ht' := (continuous_subtype_val.continuousAt.tendsto.comp ht)
    change Tendsto (fun n => (hA.isClosed.apprSeq n x : ℝ)) atTop _ at ht'
    have hm := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c x) atTop (𝓝 (c x))).mul ht'
    by_cases hx : x ∈ A
    · simpa [f, hx, hcA hx, Function.comp_def] using hm
    · simpa [f, hx, Function.comp_def] using hm

/-- Bounded continuous approximations may be integrated against any probability measure. -/
theorem u2_probability_integral_approximation {d : ℕ} (ν : Measure (Vec d))
    [IsProbabilityMeasure ν] (f : ℕ → Vec d → ℝ) (g : Vec d → ℝ)
    (hf : ∀ n, Continuous (f n)) (hbound : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (hf n).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound n x).1]
    exact (hbound n x).2
  · exact Filter.Eventually.of_forall hlim

/-- Symmetry extends from compact continuous tests to compact indicators. -/
theorem u2_gmpPhysicalC0KernelSemigroup_compact_indicator_symmetry {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (A B : Set (Vec d)) (hA : IsCompact A) (hB : IsCompact B) :
    let μ := physicalReversibleMeasure ω hd lam
    let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
    (∫ x, (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(P t x)) *
      B.indicator (fun _ => (1 : ℝ)) x ∂μ) =
    ∫ x, A.indicator (fun _ => (1 : ℝ)) x *
      (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂(P t x)) ∂μ := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
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
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    constructor
    · exact integral_nonneg fun y => (hfb1 n y).1
    · simpa using integral_mono ((hf n).1.integrable_of_hasCompactSupport (hf n).2)
        (integrable_const (μ := P t x) (1 : ℝ)) (fun y => (hfb1 n y).2)
  have hPg (n : ℕ) (x : Vec d) : 0 ≤ (∫ y, g n y ∂(P t x)) ∧
      (∫ y, g n y ∂(P t x)) ≤ 1 := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    constructor
    · exact integral_nonneg fun y => (hgb1 n y).1
    · simpa using integral_mono ((hg n).1.integrable_of_hasCompactSupport (hg n).2)
        (integrable_const (μ := P t x) (1 : ℝ)) (fun y => (hgb1 n y).2)
  have hPfl (x : Vec d) : Tendsto (fun n => ∫ y, f n y ∂(P t x)) atTop
      (𝓝 (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(P t x))) := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    exact u2_probability_integral_approximation (P t x) f _ (fun n => (hf n).1) hfb1 hfl
  have hPgl (x : Vec d) : Tendsto (fun n => ∫ y, g n y ∂(P t x)) atTop
      (𝓝 (∫ y, B.indicator (fun _ => (1 : ℝ)) y ∂(P t x))) := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
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
  exact (u1_gmpPhysicalC0KernelSemigroup_compact_symmetry hd ω lam Λ hΛ hω hSmooth t
    (f n) (g n) (hf n).1 (hf n).2 (hg n).1 (hg n).2).symm

/-- The actual physical kernel is reversible on compact rectangles. -/
theorem u2_gmpPhysicalC0KernelSemigroup_compact_rectangles {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (A B : Set (Vec d)) (hA : IsCompact A) (hB : IsCompact B) :
    let μ := physicalReversibleMeasure ω hd lam
    let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
    (∫⁻ x in A, K t x B ∂μ) = ∫⁻ y in B, K t y A ∂μ := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have bridge (S T : Set (Vec d)) (hS : IsCompact S) (hT : IsCompact T) :
      (∫⁻ x in S, K t x T ∂μ) = ENNReal.ofReal
        (∫ x, S.indicator (fun _ => (1 : ℝ)) x *
          (∫ y, T.indicator (fun _ => (1 : ℝ)) y ∂(K t x)) ∂μ) := by
    let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_ne_top
    have hp (x : Vec d) : (K t x T).toReal ≤ 1 := by
      let : IsProbabilityMeasure (K t x) :=
        ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
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
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    exact (ENNReal.ofReal_toReal (measure_ne_top (K t x) T)).symm
  change (∫⁻ x in A, K t x B ∂μ) = ∫⁻ y in B, K t y A ∂μ
  rw [bridge A B hA hB, bridge B A hB hA]
  congr 1
  have h := u2_gmpPhysicalC0KernelSemigroup_compact_indicator_symmetry
    hd ω lam Λ hΛ hω hSmooth t A B hA hB
  simpa [mul_comm] using h.symm

/-- Extend balance in one variable using local finiteness and compact regularity. -/
private theorem u2_extend_rectangles {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) (S : Set (Vec d))
    (hcompact : ∀ T : Set (Vec d), IsCompact T →
      (∫⁻ x in S, (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) t x T
        ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y in T, (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) t y S
        ∂physicalReversibleMeasure ω hd lam) :
    ∀ T : Set (Vec d), MeasurableSet T →
      (∫⁻ x in S, (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) t x T
        ∂physicalReversibleMeasure ω hd lam) =
      ∫⁻ y in T, (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) t y S
        ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
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
      _ ≤ μ T := u1_gmpPhysicalC0KernelSemigroup_subinvariant hd ω lam Λ hΛ hω hSmooth t T
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
          _ = 1 := Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t y
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
theorem u2_gmpPhysicalC0KernelSemigroup_measurable_rectangles {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let μ := physicalReversibleMeasure ω hd lam
    let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
    (∫⁻ x in A, K t x B ∂μ) = ∫⁻ y in B, K t y A ∂μ := by
  apply u2_extend_rectangles hd ω lam Λ hΛ hω hSmooth t A ?_ B hB
  intro C hC
  symm
  apply u2_extend_rectangles hd ω lam Λ hΛ hω hSmooth t C ?_ A hA
  intro D hD
  exact u2_gmpPhysicalC0KernelSemigroup_compact_rectangles hd ω lam Λ hΛ hω hSmooth t C D hC hD

/-- The physical reversible measure is invariant for the actual spatial kernel. -/
theorem u2_gmpPhysicalC0KernelSemigroup_invariant {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) :
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t) ∘ₘ (physicalReversibleMeasure ω hd lam) = physicalReversibleMeasure ω hd lam := by
  let K := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
  let μ := physicalReversibleMeasure ω hd lam
  change K ∘ₘ μ = μ
  ext S hS
  rw [Measure.bind_apply hS K.aemeasurable]
  have h := u2_gmpPhysicalC0KernelSemigroup_measurable_rectangles hd ω lam Λ hΛ hω hSmooth t Set.univ S MeasurableSet.univ hS
  change (∫⁻ x in Set.univ, K x S ∂μ) = ∫⁻ y in S, K y Set.univ ∂μ at h
  have hcons (y : Vec d) : K y Set.univ = 1 :=
    Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t y
  simpa only [Measure.restrict_univ, hcons, lintegral_const, one_mul, Measure.restrict_apply_univ] using h

end EinsteinFull
