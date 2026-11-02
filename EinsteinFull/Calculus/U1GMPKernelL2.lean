import EinsteinFull.Calculus.C8FoundationGMPAssociation
import EinsteinFull.Calculus.C16SourceExponentialMax
import EinsteinFull.Calculus.C26GMPPhysicalFormDomain
import EinsteinRelation.SpatialDirichlet.CanonicalPhysicalFormAgreementSupport
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import MarkovProcess.Kernel.Operator

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet

/-- At zero time the actual spatial kernel is Dirac, including for arbitrary
representatives of the weighted L² class. -/
theorem u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_zero {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      Integrable f (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth 0 x)) ∧
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth 0 x)) =
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω 0 (hf.toLp f) x) := by
  constructor
  · filter_upwards with x
    rw [(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).zero,
      Kernel.id_apply]
    exact integrable_dirac (by simp)
  · filter_upwards [hf.coeFn_toLp] with x hx
    rw [(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).zero,
      Kernel.id_apply, integral_dirac]
    simpa only [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.zero_apply] using hx.symm

/-- The same association holds at every time on compactly supported continuous inputs. -/
theorem u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    let hm := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hc
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      Integrable f (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ∧
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) =
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hm.toLp f) x) := by
  dsimp only
  constructor
  · filter_upwards with x
    let : IsProbabilityMeasure (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    exact hf.integrable_of_hasCompactSupport hc
  · exact Blueprint.gmpPhysicalC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω hSmooth t
      (Blueprint.gmpPhysicalCompactC0 f hf hc) _
      (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hc).coeFn_toLp

/-- Symmetry of the actual spatial kernel against compact continuous tests. -/
theorem u1_gmpPhysicalC0KernelSemigroup_compact_symmetry {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f g : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x, (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) * g x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, f x * (∫ y, g y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ∂physicalReversibleMeasure ω hd lam := by
  let F := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f
  let G := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hg hgc).toLp g
  have hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).coeFn_toLp
  have hG : (G : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hg hgc).coeFn_toLp
  have hPF := (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact hd ω lam Λ hΛ hω hSmooth t f hf hfc).2
  have hPG := (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact hd ω lam Λ hΛ hω hSmooth t g hg hgc).2
  have hs := Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω t F G
  rw [L2.inner_def, L2.inner_def] at hs
  dsimp [F, G] at *
  calc
    _ = ∫ x, inner ℝ (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t F x) (G x) ∂physicalReversibleMeasure ω hd lam := by
      apply integral_congr_ae
      filter_upwards [hPF, hG] with x h1 h2
      simp only [RCLike.inner_apply', conj_trivial, F, G, ← h1, h2]
    _ = ∫ x, inner ℝ (F x) (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t G x) ∂physicalReversibleMeasure ω hd lam := hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hPG, hF] with x h1 h2
      simp only [RCLike.inner_apply', conj_trivial, F, G, ← h1, h2]

/-- A compact cutoff of the starting point cannot increase the mass of a
nonnegative compact observable. -/
theorem u1_gmpPhysicalC0KernelSemigroup_compact_mass_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f g : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hf0 : ∀ x, 0 ≤ f x) (hg1 : ∀ x, g x ≤ 1) :
    (∫ x, (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) * g x ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x, f x ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let F := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f
  let G := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hg hgc).toLp g
  have hF : (F : Vec d → ℝ) =ᵐ[μ] f :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).coeFn_toLp
  have hPG : (fun x => ∫ y, g y ∂(P t x)) =ᵐ[μ]
      (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t G : Vec d → ℝ) :=
    (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact hd ω lam Λ hΛ hω hSmooth t g hg hgc).2
  have hi : Integrable (fun x => f x * (∫ y, g y ∂(P t x))) μ := by
    apply Integrable.congr (L2.integrable_inner (𝕜 := ℝ) F
      (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t G))
    filter_upwards [hF, hPG] with x hfx hgx
    simp only [RCLike.inner_apply', conj_trivial, hfx, hgx]
  have hfint : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  rw [u1_gmpPhysicalC0KernelSemigroup_compact_symmetry hd ω lam Λ hΛ hω hSmooth t f g hf hfc hg hgc]
  apply integral_mono hi hfint
  intro x
  have hgint : Integrable g (P t x) := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    exact hg.integrable_of_hasCompactSupport hgc
  have hP : (∫ y, g y ∂(P t x)) ≤ 1 := by
    let : IsProbabilityMeasure (P t x) :=
      ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
    simpa using integral_mono hgint (integrable_const (1 : ℝ)) hg1
  calc
    f x * (∫ y, g y ∂(P t x)) ≤ f x * 1 := mul_le_mul_of_nonneg_left hP (hf0 x)
    _ = f x := mul_one _

/-- The kernel image of a nonnegative compact observable has no greater
Lebesgue integral than the observable itself. -/
theorem u1_gmpPhysicalC0KernelSemigroup_compact_lintegral_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ∂physicalReversibleMeasure ω hd lam) ≤
      ENNReal.ofReal (∫ x, f x ∂physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
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
    have h := (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact hd ω lam Λ hΛ hω hSmooth t f hf hfc).2
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
      (u1_gmpPhysicalC0KernelSemigroup_compact_mass_bound hd ω lam Λ hΛ hω hSmooth t
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
theorem u1_gmpPhysicalC0KernelSemigroup_compact_measure_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ((Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t) ∘ₘ
      physicalReversibleMeasure ω hd lam) K ≤ physicalReversibleMeasure ω hd lam K := by
  let μ := physicalReversibleMeasure ω hd lam
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t
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
          ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
        exact (ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hc)
          (Filter.Eventually.of_forall hf0)).symm
      _ ≤ _ := u1_gmpPhysicalC0KernelSemigroup_compact_lintegral_bound hd ω lam Λ hΛ hω hSmooth t f hf hc hf0
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
theorem u1_gmpPhysicalC0KernelSemigroup_subinvariant {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) :
    (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t) ∘ₘ
      physicalReversibleMeasure ω hd lam ≤ physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let ν := (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t) ∘ₘ μ
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have hcompact (K : Set (Vec d)) (hK : IsCompact K) : ν K ≤ μ K :=
    u1_gmpPhysicalC0KernelSemigroup_compact_measure_bound hd ω lam Λ hΛ hω hSmooth t K hK
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

/-- Every physical L² representative is integrable against almost every
actual transition kernel. -/
theorem u1_gmpPhysicalC0KernelSemigroup_integrable_ae_L2 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      Integrable f (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) := by
  have hfComp := hf.mono_measure
    (u1_gmpPhysicalC0KernelSemigroup_subinvariant hd ω lam Λ hΛ hω hSmooth t)
  have hFiberEq : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      f =ᵐ[Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x]
        hfComp.aestronglyMeasurable.mk f :=
    Measure.ae_ae_of_ae_comp hfComp.aestronglyMeasurable.ae_eq_mk
  have hpowInt := hfComp.integrable_norm_rpow (by norm_num) (by simp)
  have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
  filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
  let : IsProbabilityMeasure (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) :=
    ⟨Blueprint.gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  have hxMeas : AEStronglyMeasurable f
      (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) :=
    hfComp.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  have hxMemLp : MemLp f 2
      (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) :=
    (integrable_norm_rpow_iff hxMeas (by norm_num) (by simp)).mp hxInt
  exact hxMemLp.integrable (by norm_num)

local instance : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩

/-- The canonical L² kernel operator agrees with the physical evolution. -/
theorem u1_gmpPhysicalC0KernelSemigroup_operator_L2 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0) :
    let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
    let μ := physicalReversibleMeasure ω hd lam
    let hμ : P.IsSubInvariant μ :=
      u1_gmpPhysicalC0KernelSemigroup_subinvariant hd ω lam Λ hΛ hω hSmooth
    P.operatorFinite μ hμ 2 t = Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t := by
  dsimp only
  let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := physicalReversibleMeasure ω hd lam
  let hμ : P.IsSubInvariant μ :=
    u1_gmpPhysicalC0KernelSemigroup_subinvariant hd ω lam Λ hΛ hω hSmooth
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hdense : Dense {F : Lp ℝ 2 μ |
      ∃ g : Vec d → ℝ, (F : Vec d → ℝ) =ᵐ[μ] g ∧
        HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  apply ContinuousLinearMap.ext
  have heq := Continuous.ext_on hdense
    (P.operatorFinite μ hμ 2 t).continuous
    (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t).continuous (by
      rintro F ⟨g, hFg, hgc, hgd⟩
      have hm := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hgd.continuous hgc
      have hF : F = hm.toLp g := Lp.ext (hFg.trans hm.coeFn_toLp.symm)
      apply Lp.ext
      calc
        (P.operatorFinite μ hμ 2 t F : Vec d → ℝ) =ᵐ[μ]
            MarkovProcess.kernelIntegral (P t) F :=
          P.isAssociatedFinite_operatorFinite μ hμ 2 t F
        _ =ᵐ[μ] MarkovProcess.kernelIntegral (P t) g :=
          MarkovProcess.kernelIntegral_congr_ae (hμ t) hFg
        _ =ᵐ[μ] (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hm.toLp g) : Vec d → ℝ) :=
          (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2_compact
            hd ω lam Λ hΛ hω hSmooth t g hgd.continuous hgc).2
        _ =ᵐ[μ] (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t F : Vec d → ℝ) := by rw [hF])
  exact fun x => congrFun heq x

/-- The actual kernel represents the physical L² semigroup for every L² input. -/
theorem u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam), Integrable f (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ∧
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      (∫ y, f y ∂(Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) =
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f) x) := by
  constructor
  · exact u1_gmpPhysicalC0KernelSemigroup_integrable_ae_L2 hd ω lam Λ hΛ hω hSmooth t f hf
  · let P := Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
    let μ := physicalReversibleMeasure ω hd lam
    let hμ : P.IsSubInvariant μ :=
      u1_gmpPhysicalC0KernelSemigroup_subinvariant hd ω lam Λ hΛ hω hSmooth
    have hchange := MarkovProcess.kernelIntegral_congr_ae (hμ t) hf.coeFn_toLp
    have hrepr := P.isAssociatedFinite_operatorFinite μ hμ 2 t (hf.toLp f)
    have hop := u1_gmpPhysicalC0KernelSemigroup_operator_L2 hd ω lam Λ hΛ hω hSmooth t
    calc
      MarkovProcess.kernelIntegral (P t) f =ᵐ[μ]
          MarkovProcess.kernelIntegral (P t) (hf.toLp f) := hchange.symm
      _ =ᵐ[μ] (P.operatorFinite μ hμ 2 t (hf.toLp f) : Vec d → ℝ) := hrepr.symm
      _ =ᵐ[μ] (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f) : Vec d → ℝ) := by
        rw [hop]
        exact Filter.EventuallyEq.rfl

/-- The domain of the physical closed form is characterized by the actual kernel. -/
theorem u1_gmpPhysical_kernel_closedForm_domain {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ((∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam (fun s => Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth s) t f ≤ C) ↔
      physicalH1Member ω hd lam f) := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  have hquot (t : ℝ≥0) :
      semigroupFormDifferenceQuotient ω hd lam
          (fun s => Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth s) t f =
        (t : ℝ)⁻¹ * inner ℝ
          (hf.toLp f - Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f))
          (hf.toLp f) := by
    have hk := (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
      hd ω lam Λ hΛ hω hSmooth t f hf).2
    unfold semigroupFormDifferenceQuotient
    rw [L2.inner_def]
    simp only [one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [hk, hf.coeFn_toLp,
      Lp.coeFn_sub (hf.toLp f) (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f))] with x hx hfx hs
    rw [hs]
    simp [Pi.sub_apply, hx, hfx, RCLike.inner_apply, mul_comm]
  have hh1 : physicalH1Member ω hd lam f ↔ physicalH1Member ω hd lam (hf.toLp f) := by
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans hf.coeFn_toLp.symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans hf.coeFn_toLp⟩
  rw [hh1, ← Blueprint.gmpPhysicalSemigroup_bounded_formQuotient_iff hd ω lam Λ hΛ hω (hf.toLp f)]
  simp only [hquot]

/-- The actual kernel recovers the energy of any graph representing the same H¹ value. -/
theorem u1_gmpPhysical_kernel_closedForm_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (f : Vec d → ℝ)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      (fun s => Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth s) t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 (physicalH1FormEnergy ω hd lam u)) := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let v := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q
  let F := Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
  have hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f := by
    have h := Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v
    rw [Blueprint.gmpForceH1_graphEquiv_value hd lam q] at h
    exact h.trans hq
  have hf : MemLp f 2 (physicalReversibleMeasure ω hd lam) := (Lp.memLp F).ae_eq hF
  have hFLp : hf.toLp f = F := Lp.ext (hf.coeFn_toLp.trans hF.symm)
  have hquot (t : ℝ≥0) :
      semigroupFormDifferenceQuotient ω hd lam
          (fun s => Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth s) t f =
        (t : ℝ)⁻¹ * inner ℝ
          (F - Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t F) F := by
    have hk := (u1_gmpPhysicalC0KernelSemigroup_integral_ae_L2
      hd ω lam Λ hΛ hω hSmooth t f hf).2
    unfold semigroupFormDifferenceQuotient
    rw [← hFLp, L2.inner_def]
    simp only [one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [hk, hf.coeFn_toLp,
      Lp.coeFn_sub (hf.toLp f) (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f))] with x hx hfx hs
    rw [hs]
    simp [Pi.sub_apply, hx, hfx, RCLike.inner_apply, mul_comm]
  have hgv : g.value =ᵐ[physicalReversibleMeasure ω hd lam] u.value := by
    have hr := Blueprint.gmpH1Representative_value_ae (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
    have hp := (Measure.absolutelyContinuous_of_le_smul
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hr
    exact hp.trans ((Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v).symm.trans (hF.trans hu.symm))
  have hvol := (ae_withDensity_iff_volume_of_continuous_pos
    (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
    (positiveSourcePhysicalDensity ω hd lam) _).mp hgv
  have hgrad := weakGradients_ae_eq_of_value_ae_eq hvol g.distributionalGradient u.distributionalGradient
  have hgradphys := (ae_withDensity_iff_volume_of_continuous_pos
    (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
    (positiveSourcePhysicalDensity ω hd lam) _).mpr hgrad
  have henergy : physicalH1FormEnergy ω hd lam g = physicalH1FormEnergy ω hd lam u := by
    unfold physicalH1FormEnergy
    apply integral_congr_ae
    filter_upwards [hgradphys] with x hx
    simp only [weightedFormIntegrand, hx]
  have hmember : physicalH1Member ω hd lam F :=
    (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω F).mp ⟨v, rfl⟩
  have hlimit := Blueprint.gmpPhysicalSemigroup_formLimit hd ω lam Λ hΛ hω hmember hmember
  rw [Blueprint.gmpPhysicalClosedForm_value hd ω lam Λ hΛ hω v v,
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam Λ hω v,
    henergy] at hlimit
  simpa only [hquot] using hlimit


end EinsteinFull
