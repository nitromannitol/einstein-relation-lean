import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3UniformCrossHeat
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Calculus
open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

/-- Extending a positive-time spacetime function by zero preserves its local
square integrability on a time interval extending into the past. -/
theorem c9_zero_past_memLp {d : ℕ} {T : ℝ}
    (U : Set (Vec d)) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo 0 T ×ˢ U))) :
    MemLp (fun z => if 0 < z.1 then u z else 0) 2
      (volume.restrict (Set.Ioo (-T) T ×ˢ U)) := by
  let S : Set (ℝ × Vec d) := Prod.fst ⁻¹' Set.Ioi 0
  have hS : MeasurableSet S := measurableSet_Ioi.preimage measurable_fst
  have hm : (volume.restrict (Set.Ioo (-T) T ×ˢ U)).restrict S ≤
      volume.restrict (Set.Ioo 0 T ×ˢ U) := by
    rw [Measure.restrict_restrict hS]
    apply Measure.restrict_mono_set
    intro z hz
    exact ⟨⟨hz.1, hz.2.1.2⟩, hz.2.2⟩
  change MemLp (S.indicator u) 2 _
  exact (memLp_indicator_iff_restrict hS).mpr (hu.mono_measure hm)

/-- The zero function has zero weak spatial gradient on any domain. -/
theorem c9_zero_weak_gradient {d : ℕ} (U : Set (Vec d)) :
    HasWeakGradient U (fun _ => 0) (fun _ => 0) := by
  intro i
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  intro φ hφ
  simp

/-- Zero extension preserves the almost-everywhere spatial weak gradient. -/
theorem c9_zero_past_ae_weak_gradient {d : ℕ} {T : ℝ}
    (U : Set (Vec d)) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      HasWeakGradient U (fun x => u (t, x)) (fun x => G (t, x))) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-T) T),
      HasWeakGradient U (fun x => if 0 < t then u (t, x) else 0)
        (fun x => if 0 < t then G (t, x) else 0) := by
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hgrad] with t ht hmem
  by_cases hp : 0 < t
  · simpa only [if_pos hp] using ht ⟨hp, hmem.2⟩
  · simpa only [if_neg hp] using c9_zero_weak_gradient U

/-- The zero-past gradient retains the measurability supplied by caloricity. -/
theorem c9_zero_past_gradient_measurable {d : ℕ} {T : ℝ}
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo 0 T) U u G) :
    AEStronglyMeasurable (fun z => if 0 < z.1 then G z else 0)
      (volume.restrict (Set.Ioo (-T) T ×ˢ U)) := by
  let S : Set (ℝ × Vec d) := Prod.fst ⁻¹' Set.Ioi 0
  have hS : MeasurableSet S := measurableSet_Ioi.preimage measurable_fst
  have hm : (volume.restrict (Set.Ioo (-T) T ×ˢ U)).restrict S ≤
      volume.restrict (Set.Ioo 0 T ×ˢ U) := by
    rw [Measure.restrict_restrict hS]
    apply Measure.restrict_mono_set
    intro z hz
    exact ⟨⟨hz.1, hz.2.1.2⟩, hz.2.2⟩
  change AEStronglyMeasurable (S.indicator G) _
  exact (aestronglyMeasurable_indicator_iff hS).mpr (hcal.2.1.mono_measure hm)

/-- The Euclidean gradient energy remains square integrable after zero extension. -/
theorem c9_zero_past_gradient_memLp {d : ℕ} {T : ℝ}
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo 0 T) U u G) :
    MemLp (fun z => euclideanNorm (if 0 < z.1 then G z else 0)) 2
      (volume.restrict (Set.Ioo (-T) T ×ˢ U)) := by
  have hzero : euclideanNorm (0 : Vec d) = 0 := by
    simp [euclideanNorm, euclideanSq, dot]
  have h := c9_zero_past_memLp U (fun z => euclideanNorm (G z)) hcal.2.2.1
  convert h using 1
  ext z
  split <;> simp_all

/-- A zero-past integral on the enlarged cylinder is the original integral
on the positive cylinder, without any integrability assumption. -/
theorem c9_zero_past_integral {d : ℕ} {T : ℝ} (hT : 0 < T)
    (U : Set (Vec d)) (f : ℝ × Vec d → ℝ) :
    (∫ z in Set.Ioo (-T) T ×ˢ U, if 0 < z.1 then f z else 0) =
      ∫ z in Set.Ioo 0 T ×ˢ U, f z := by
  let S : Set (ℝ × Vec d) := Prod.fst ⁻¹' Set.Ioi 0
  have hS : MeasurableSet S := measurableSet_Ioi.preimage measurable_fst
  change (∫ z in Set.Ioo (-T) T ×ˢ U, S.indicator f z) = _
  rw [setIntegral_indicator hS]
  have heq : (Set.Ioo (-T) T ×ˢ U) ∩ S = Set.Ioo 0 T ×ˢ U := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.2, hz.1.1.2⟩, hz.1.2⟩
    · intro hz
      exact ⟨⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩, hz.1.1⟩
  rw [heq]

/-- The extended weighted weak integrand has exactly the original positive-time
integral. The density stays in the time term. -/
theorem c9_zero_past_weak_integral {d : ℕ} {T : ℝ} (hT : 0 < T)
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (ψ : ℝ × Vec d → ℝ) :
    (∫ z in Set.Ioo (-T) T ×ˢ U,
      -(ρ z.2 * (if 0 < z.1 then u z else 0)) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (if 0 < z.1 then G z else 0))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) =
    ∫ z in Set.Ioo 0 T ×ˢ U,
      -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
  let f : ℝ × Vec d → ℝ := fun z =>
    -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
      dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0, unitVector j))
  calc
    _ = ∫ z in Set.Ioo (-T) T ×ˢ U, if 0 < z.1 then f z else 0 := by
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : 0 < z.1
      · simp [hz, f]
      · simp [hz, dot]
    _ = ∫ z in Set.Ioo 0 T ×ˢ U, f z := c9_zero_past_integral hT U f

/-- Multiplying a spacetime test by a smooth time cutoff vanishing up to a
positive time gives a test supported inside the positive cylinder. -/
theorem c9_time_cutoff_test {d : ℕ} {T a : ℝ} (ha : 0 < a)
    (U : Set (Vec d)) (ψ : ℝ × Vec d → ℝ) (η : ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo (-T) T ×ˢ U)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hzero : ∀ t, t ≤ a → η t = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => η z.1 * ψ z) ∧
      HasCompactSupport (fun z => η z.1 * ψ z) ∧
      tsupport (fun z => η z.1 * ψ z) ⊆ Set.Ioo 0 T ×ˢ U := by
  have hcut : tsupport (fun z : ℝ × Vec d => η z.1 * ψ z) ⊆
      {z | a ≤ z.1} := by
    apply closure_minimal ?_ (isClosed_le continuous_const continuous_fst)
    intro z hz
    by_contra hn
    have hz0 : η z.1 = 0 := hzero z.1 (le_of_not_ge hn)
    exact hz (by simp [hz0])
  refine ⟨(hη.comp contDiff_fst).mul hψ, hc.mul_left, ?_⟩
  intro z hz
  have hzs := hs (tsupport_mul_subset_right hz)
  exact ⟨⟨lt_of_lt_of_le ha (hcut hz), hzs.1.2⟩, hzs.2⟩

/-- The original weighted weak equation applies to every admissible positive-gap
cutoff of an enlarged-cylinder test. -/
theorem c9_time_cutoff_weak_equation {d : ℕ} {T a : ℝ} (ha : 0 < a)
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo 0 T) U u G)
    (ψ : ℝ × Vec d → ℝ) (η : ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo (-T) T ×ˢ U)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hzero : ∀ t, t ≤ a → η t = 0) :
    (∫ z in Set.Ioo 0 T ×ˢ U,
      -(ρ z.2 * u z) * fderiv ℝ (fun z => η z.1 * ψ z) z (1, 0) +
        dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ (fun z => η z.1 * ψ z) z (0, unitVector j))) = 0 := by
  obtain ⟨hd, hcompact, hsupport⟩ := c9_time_cutoff_test ha U ψ η hψ hc hs hη hzero
  apply hcal.2.2.2.2 _ hd hcompact
  simpa only [interior_Ioo] using hsupport

/-- The derivative of a time-cutoff test keeps the time and spatial
contributions separate. -/
theorem c9_time_cutoff_fderiv {d : ℕ} (ψ : ℝ × Vec d → ℝ) (η : ℝ → ℝ)
    (hψ : Differentiable ℝ ψ) (hη : Differentiable ℝ η)
    (z v : ℝ × Vec d) :
    fderiv ℝ (fun w => η w.1 * ψ w) z v =
      η z.1 * fderiv ℝ ψ z v + ψ z * fderiv ℝ η z.1 v.1 := by
  have htime : HasFDerivAt (fun w : ℝ × Vec d => η w.1)
      ((fderiv ℝ η z.1).comp (ContinuousLinearMap.fst ℝ ℝ (Vec d))) z :=
    (hη z.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hprod := htime.mul (hψ z).hasFDerivAt
  change fderiv ℝ ((fun w : ℝ × Vec d => η w.1) * ψ) z v = _
  rw [hprod.fderiv]
  simp

/-- Expanding the cutoff weak integrand leaves precisely the weighted time
boundary term. -/
theorem c9_time_cutoff_integrand {d : ℕ} (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (ψ : ℝ × Vec d → ℝ) (η : ℝ → ℝ)
    (hψ : Differentiable ℝ ψ) (hη : Differentiable ℝ η) (z : ℝ × Vec d) :
    -(ρ z.2 * u z) * fderiv ℝ (fun w => η w.1 * ψ w) z (1, 0) +
      dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ (fun w => η w.1 * ψ w) z (0, unitVector j)) =
    η z.1 * (-(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) -
      (ρ z.2 * u z) * ψ z * fderiv ℝ η z.1 1 := by
  have hspace (j : Fin d) :
      fderiv ℝ (fun w => η w.1 * ψ w) z (0, unitVector j) =
        η z.1 * fderiv ℝ ψ z (0, unitVector j) := by
    rw [c9_time_cutoff_fderiv ψ η hψ hη]
    simp
  have hdot : dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ (fun w => η w.1 * ψ w) z (0, unitVector j)) =
      η z.1 * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
    simp only [dot, hspace, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hdot, c9_time_cutoff_fderiv ψ η hψ hη]
  simp only [Prod.fst]
  ring

/-- A uniform derivative bound for the fixed smooth transition. -/
theorem c9_smooth_transition_deriv_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn (deriv Real.smoothTransition) (Icc (0 : ℝ) 1))
  refine ⟨max N 0 + 1, by positivity, ?_⟩
  intro s
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · have hNs : |deriv Real.smoothTransition s| ≤ N := by
      simpa only [Real.norm_eq_abs] using hN s hs
    exact hNs.trans ((le_max_left N 0).trans (le_add_of_nonneg_right zero_le_one))
  · have hz : deriv Real.smoothTransition s = 0 := by
      rcases (not_and_or.mp hs) with hs | hs
      all_goals have hs := lt_of_not_ge hs
      · have he : Real.smoothTransition =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
          filter_upwards [eventually_lt_nhds hs] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        simpa only [deriv_const] using he.deriv_eq
      · have he : Real.smoothTransition =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
          filter_upwards [eventually_gt_nhds hs] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        simpa only [deriv_const] using he.deriv_eq
    rw [hz, abs_zero]
    positivity

/-- Smooth positive-gap cutoffs have a derivative bounded by the inverse gap. -/
theorem c9_exists_time_cutoff :
    ∃ B : ℝ, 0 < B ∧ ∀ b e : ℝ, b < e → ∃ η : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ s, s ≤ b → η s = 0) ∧
      (∀ s, e ≤ s → η s = 1) ∧
      ∀ s, 0 ≤ η s ∧ η s ≤ 1 ∧ |deriv η s| ≤ B / (e - b) := by
  obtain ⟨B, hB, hbound⟩ := c9_smooth_transition_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro b e hbe
  have hgap : 0 < e - b := sub_pos.mpr hbe
  let η : ℝ → ℝ := fun s => Real.smoothTransition ((s - b) / (e - b))
  have hd s : deriv η s = deriv Real.smoothTransition ((s - b) / (e - b)) / (e - b) := by
    have h := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
      ((s - b) / (e - b))).hasDerivAt.comp s
        (((hasDerivAt_id s).sub_const b).div_const (e - b))
    change HasDerivAt η _ s at h
    rw [h.deriv]
    ring
  refine ⟨η, Real.smoothTransition.contDiff.comp (by fun_prop), ?_, ?_, ?_⟩
  · intro s hs
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hs) hgap.le)
  · intro s hs
    exact Real.smoothTransition.one_of_one_le ((one_le_div hgap).mpr (by linarith))
  · intro s
    refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, ?_⟩
    rw [hd, abs_div, abs_of_pos hgap]
    exact div_le_div_of_nonneg_right (hbound _) hgap.le

/-- A cutoff's derivative vanishes on both open constant tails. -/
theorem c9_time_cutoff_deriv_eq_zero {b e s : ℝ} (η : ℝ → ℝ)
    (hzero : ∀ t, t ≤ b → η t = 0) (hone : ∀ t, e ≤ t → η t = 1)
    (hs : s < b ∨ e < s) : deriv η s = 0 := by
  rcases hs with hs | hs
  · have he : η =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hs] with t ht
      exact hzero t ht.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : η =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      exact hone t ht.le
    simpa only [deriv_const] using he.deriv_eq

/-- The scalar Cauchy–Schwarz inequality in the second-moment form used for
the spatial boundary pairing. -/
theorem c9_integral_mul_abs_le_sqrt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, (f x)^2 ∂μ) * Real.sqrt (∫ x, (g x)^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (by simpa using hf) (by simpa using hg)
  simp only [Real.norm_eq_abs, Real.rpow_two, ← Real.sqrt_eq_rpow, sq_abs] at h
  have ht := norm_integral_le_integral_norm (μ := μ) (fun x => f x * g x)
  simp only [norm_mul, Real.norm_eq_abs] at ht
  exact ht.trans h

/-- A zero right trace gives a uniform small second moment on a sufficiently
short positive interval. -/
theorem c9_zero_trace_small {d : ℕ} (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ)
    (htrace : Tendsto (fun t : ℝ => ∫ x in U, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t ≤ δ →
      |∫ x in U, |u (t, x)|^2| < ε := by
  intro ε hε
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |∫ x in U, |u (t, x)|^2| < ε := by
    have hev : ∀ᶠ x : ℝ in 𝓝 0, |x| < ε := by
      have hb := Metric.ball_mem_nhds (0 : ℝ) hε
      filter_upwards [hb] with x hx
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact htrace.eventually hev
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  exact ⟨δ, hδ, fun t ht htd => hsmall ⟨ht, htd⟩⟩

/-- Square-integrability on a product gives square-integrable spatial slices
at almost every time. -/
theorem c9_memLp_prod_right_ae {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν]
    (f : Ω × Ξ → ℝ) (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ t ∂μ, MemLp (fun x => f (t, x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae] with t hm hi
  exact (memLp_two_iff_integrable_sq hm).2 hi

/-- The spacetime energy gives L² spatial slices at almost every positive
time, with the original restricted measures. -/
theorem c9_memLp_spatial_slice_ae {d : ℕ} {T : ℝ}
    (U : Set (Vec d)) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T ×ˢ U))) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      MemLp (fun x => u (t, x)) 2 (volume.restrict U) := by
  apply c9_memLp_prod_right_ae (volume.restrict (Ioo 0 T)) (volume.restrict U) u
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu
  exact hu

/-- A zero L² trace makes every uniformly L²-bounded spatial pairing small;
the slice hypotheses can be supplied only at those times where they hold. -/
theorem c9_zero_trace_pairing_small {d : ℕ} (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (g : ℝ → Vec d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (htrace : Tendsto (fun t : ℝ => ∫ x in U, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t ≤ δ →
      MemLp (fun x => u (t, x)) 2 (volume.restrict U) →
      MemLp (g t) 2 (volume.restrict U) →
      (∫ x in U, (g t x)^2) ≤ C →
      |∫ x in U, u (t, x) * g t x| < ε := by
  intro ε hε
  have hden : 0 < C + 1 := by linarith
  have hsmall : 0 < ε^2 / (C + 1) := div_pos (sq_pos_of_pos hε) hden
  obtain ⟨δ, hδ, hδsmall⟩ := c9_zero_trace_small U u htrace _ hsmall
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd hu hg hgC
  let A : ℝ := ∫ x in U, (u (t, x))^2
  let D : ℝ := ∫ x in U, (g t x)^2
  have hA : 0 ≤ A := integral_nonneg (fun _ => sq_nonneg _)
  have hD : 0 ≤ D := integral_nonneg (fun _ => sq_nonneg _)
  have hAsmall : A < ε^2 / (C + 1) := by
    have h := hδsmall t ht htd
    simp only [sq_abs] at h
    change |A| < ε^2 / (C + 1) at h
    simpa only [abs_of_nonneg hA] using h
  have hAC : A * C < ε^2 := by
    have h := (lt_div_iff₀ hden).mp hAsmall
    nlinarith
  have hpair := c9_integral_mul_abs_le_sqrt (volume.restrict U) hu hg
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hsquares : (Real.sqrt A * Real.sqrt D)^2 = A * D := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hD]
  have hnonneg : 0 ≤ |∫ x in U, u (t, x) * g t x| := abs_nonneg _
  have hDC : D ≤ C := hgC
  have hAD : A * D ≤ A * C := mul_le_mul_of_nonneg_left hDC hA
  dsimp only [A, D] at hsquares hAD hAC hsA hsD
  nlinarith [mul_nonneg hsA hsD]

/-- The inverse-gap cutoff derivative cancels the length of the transition
interval in the boundary pairing estimate. -/
theorem c9_cutoff_boundary_interval_bound {b e B M : ℝ} (hbe : b < e)
    (hB : 0 ≤ B) (η F : ℝ → ℝ)
    (hderiv : ∀ t, |deriv η t| ≤ B / (e - b))
    (hF : ∀ᵐ t ∂volume.restrict (Icc b e), |F t| ≤ M) :
    |∫ t in Icc b e, deriv η t * F t| ≤ B * M := by
  have hgap : 0 < e - b := sub_pos.mpr hbe
  have hbound : ∀ᵐ t ∂volume.restrict (Icc b e),
      ‖deriv η t * F t‖ ≤ (B / (e - b)) * M := by
    filter_upwards [hF] with t ht
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hderiv t) ht (abs_nonneg _) (div_nonneg hB hgap.le)
  have h := norm_integral_le_of_norm_le_const hbound
  have hcalc : (B / (e - b) * M) * (e - b) = B * M := by
    field_simp
  simpa [Real.norm_eq_abs, integral_const, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal hgap.le, hcalc] using h

/-- The zero trace suppresses the cutoff boundary pairing uniformly over
positive transition intervals approaching time zero. -/
theorem c9_cutoff_boundary_vanishes {d : ℕ} {T : ℝ}
    (U : Set (Vec d)) (u : ℝ × Vec d → ℝ) (g : ℝ → Vec d → ℝ)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T ×ˢ U)))
    (htrace : Tendsto (fun t : ℝ => ∫ x in U, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0))
    (hg : ∀ t, MemLp (g t) 2 (volume.restrict U))
    (hgC : ∀ t, (∫ x in U, (g t x)^2) ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b e : ℝ, 0 < b → b < e → e ≤ δ → e < T →
      ∀ η : ℝ → ℝ, (∀ t, |deriv η t| ≤ B / (e - b)) →
      |∫ t in Icc b e, deriv η t * (∫ x in U, u (t, x) * g t x)| ≤ ε := by
  intro ε hε
  have hden : 0 < B + 1 := by linarith
  obtain ⟨δ, hδ, hsmall⟩ :=
    c9_zero_trace_pairing_small U u g C hC htrace (ε / (B + 1)) (div_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro b e hb hbe heδ heT η hη
  have hslice := (ae_restrict_iff' measurableSet_Ioo).1 (c9_memLp_spatial_slice_ae U u hu)
  have hF : ∀ᵐ t ∂volume.restrict (Icc b e),
      |∫ x in U, u (t, x) * g t x| ≤ ε / (B + 1) := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hslice] with t ht hmem
    have htpos : 0 < t := lt_of_lt_of_le hb hmem.1
    have htT : t < T := lt_of_le_of_lt hmem.2 heT
    have htδ : t ≤ δ := le_trans hmem.2 heδ
    exact (hsmall t htpos htδ (ht ⟨htpos, htT⟩) (hg t) (hgC t)).le
  have hbound := c9_cutoff_boundary_interval_bound hbe hB
    η (fun t => ∫ x in U, u (t, x) * g t x) hη hF
  have hratio : B * (ε / (B + 1)) ≤ ε := by
    calc
      B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hε.le hden.le)
      _ = ε := by field_simp
  exact hbound.trans hratio

/-- The Euclidean source ball has finite coordinate Lebesgue measure. -/
theorem c9_sourceBall_measure_ne_top {d : ℕ} (y : Vec d) (r : ℝ) :
    volume (sourceBall y r) ≠ ⊤ := by
  have hnorm (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change x i ^ 2 ≤ ∑ j : Fin d, x j * x j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
  apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := (volume : Measure (Vec d))) (x := y) (r := r)).ne
  apply measure_mono
  intro x hx
  change dist x y < r
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hnorm (x - y)) hx

/-- Every spatial slice of a compactly supported test multiplied by the
elliptic density has a uniform square-integral bound. -/
theorem c9_weighted_test_slice_bound {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, MemLp (fun x => ρ x * ψ (t, x)) 2
      (volume.restrict (sourceBall y r)) ∧
      (∫ x in sourceBall y r, (ρ x * ψ (t, x))^2) ≤ C := by
  let μ := volume.restrict (sourceBall y r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (c9_sourceBall_measure_ne_top y r)
  obtain ⟨D, hD⟩ := hψ.continuous.bounded_above_of_compact_support hc
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD (0, 0))
  have hκinv : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hρ (x : Vec d) : |ρ x| ≤ κ⁻¹ := by
    rw [abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  let K := κ⁻¹ * D
  have hK : 0 ≤ K := mul_nonneg hκinv hD0
  have hpoint (t : ℝ) (x : Vec d) : |ρ x * ψ (t, x)| ≤ K := by
    rw [abs_mul]
    exact mul_le_mul (hρ x) (by simpa [Real.norm_eq_abs] using hD (t, x))
      (abs_nonneg _) hκinv
  refine ⟨K^2 * μ.real Set.univ, mul_nonneg (sq_nonneg _) measureReal_nonneg, ?_⟩
  intro t
  have hm : Measurable (fun x => ρ x * ψ (t, x)) :=
    hell.1.mul (hψ.continuous.measurable.comp (measurable_const.prodMk measurable_id))
  have hlp : MemLp (fun x => ρ x * ψ (t, x)) 2 μ := by
    apply MemLp.of_bound hm.aestronglyMeasurable K
    exact ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hpoint t x)
  refine ⟨hlp, ?_⟩
  have hi := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => (ρ x * ψ (t, x))^2) (C := K^2)
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hp := (sq_le_sq₀ (abs_nonneg (ρ x * ψ (t, x))) hK).2 (hpoint t x)
      simpa only [sq_abs] using hp))
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hi)

/-- The density-weighted test pairing vanishes uniformly as the cutoff
transition interval approaches the zero-trace time. -/
theorem c9_weighted_cutoff_boundary_vanishes {d : ℕ} {κ T r : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T ×ˢ sourceBall y r)))
    (htrace : Tendsto (fun t : ℝ => ∫ x in sourceBall y r, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0)) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b e : ℝ, 0 < b → b < e → e ≤ δ → e < T →
      ∀ η : ℝ → ℝ, (∀ t, |deriv η t| ≤ B / (e - b)) →
      |∫ t in Icc b e, deriv η t *
        (∫ x in sourceBall y r, u (t, x) * (ρ x * ψ (t, x)))| ≤ ε := by
  obtain ⟨C, hC, hg⟩ := c9_weighted_test_slice_bound hκ ρ α hell y ψ hψ hc
  exact c9_cutoff_boundary_vanishes (sourceBall y r) u (fun t x => ρ x * ψ (t, x))
    C B hC hB hu htrace (fun t => (hg t).1) (fun t => (hg t).2)

/-- The weighted weak integrand is integrable on any spatial domain whenever
the solution and its actual Euclidean gradient have the stated L² regularity. -/
theorem c9_weighted_weak_integrand_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (I : Set ℝ) (U : Set (Vec d)) (u : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hG : AEStronglyMeasurable G (volume.restrict (I ×ˢ U)))
    (hL : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)))
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun z => -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
      dot ((α z.2).mulVec (G z))
        (fun i => fderiv ℝ ψ z (0, unitVector i)))
      (volume.restrict (I ×ˢ U)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U)
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hell.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      change |ρ z.2| ≤ κ⁻¹
      rw [abs_of_nonneg (hκ.le.trans (hell.2.2 z.2).1)]
      exact (hell.2.2 z.2).2.1
  have ht := spacetime_test_directional_derivative_memLp ψ hψ hc (1, 0) (I ×ˢ U)
  have htime : Integrable (fun z => -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0)) μ := by
    apply ((hu.fun_mul (r := 2) hρ).integrable_mul ht).neg.congr
    exact ae_of_all _ fun z => by dsimp; ring
  have hflux : Integrable (fun z => ∑ i : Fin d, ∑ j : Fin d,
      α z.2 i j * G z j * fderiv ℝ ψ z (0, Pi.single i 1)) μ := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    have hm : Measurable (fun z : ℝ × Vec d => α z.2 i j) := by
      let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
      let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
      exact ((((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        hell.2.1).comp measurable_snd)
    have ha : MemLp (fun z : ℝ × Vec d => α z.2 i j) ⊤ μ := by
      apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        simpa only [dirichletValueGradientMatrix] using
          dirichletValueGradientMatrix_bound hκ hell z.2 (some i) (some j)
    have hg := spacetime_gradient_coordinate_memLp μ G hG hL j
    have hd := spacetime_test_directional_derivative_memLp ψ hψ hc
      (0, Pi.single i 1) (I ×ˢ U)
    apply ((hg.fun_mul (r := 2) ha).integrable_mul hd).congr
    exact ae_of_all _ fun z => by dsimp; ring
  have hflux' : Integrable (fun z => dot ((α z.2).mulVec (G z))
      (fun i => fderiv ℝ ψ z (0, unitVector i))) μ := by
    simpa only [dot, Matrix.mulVec, dotProduct, Finset.sum_mul, unitVector] using hflux
  exact htime.add hflux'

/-- The time-cutoff boundary term is integrable on the original cylinder. -/
theorem c9_weighted_boundary_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (I : Set ℝ) (U : Set (Vec d)) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (B : ℝ) (hB : ∀ t, |deriv η t| ≤ B) :
    Integrable (fun z => (ρ z.2 * u z) * ψ z * deriv η z.1)
      (volume.restrict (I ×ˢ U)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U)
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hell.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      change |ρ z.2| ≤ κ⁻¹
      rw [abs_of_nonneg (hκ.le.trans (hell.2.2 z.2).1)]
      exact (hell.2.2 z.2).2.1
  have hp : MemLp ψ 2 μ :=
    (hψ.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have he : MemLp (fun z : ℝ × Vec d => deriv η z.1) ⊤ μ := by
    apply memLp_top_of_bound
      (((contDiff_infty_iff_deriv.mp hη).2.continuous.measurable.comp measurable_fst).aestronglyMeasurable) B
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hB z.1
  have hi := (hu.fun_mul (r := 2) hρ).integrable_mul (hp.fun_mul (r := 2) he)
  apply hi.congr
  exact ae_of_all _ fun z => by dsimp; ring

/-- Fubini identifies the spacetime boundary term with the time integral
on the actual cutoff transition interval. -/
theorem c9_weighted_boundary_fubini {d : ℕ} {κ T b e : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (hb : 0 < b) (heT : e < T)
    (U : Set (Vec d)) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T ×ˢ U)))
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hzero : ∀ t, t ≤ b → η t = 0) (hone : ∀ t, e ≤ t → η t = 1)
    (B : ℝ) (hB : ∀ t, |deriv η t| ≤ B) :
    (∫ z in Ioo 0 T ×ˢ U, (ρ z.2 * u z) * ψ z * deriv η z.1) =
      ∫ t in Icc b e, deriv η t * (∫ x in U, u (t, x) * (ρ x * ψ (t, x))) := by
  let f : ℝ × Vec d → ℝ := fun z => (ρ z.2 * u z) * ψ z * deriv η z.1
  have hi : Integrable f ((volume.restrict (Ioo 0 T)).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact c9_weighted_boundary_integrable hκ hell (Ioo 0 T) U u hu ψ hψ hc η hη B hB
  have hF : (∫ z in Ioo 0 T ×ˢ U, f z) =
      ∫ t in Ioo 0 T, deriv η t * (∫ x in U, u (t, x) * (ρ x * ψ (t, x))) := by
    change (∫ z, f z ∂(((volume : Measure ℝ).prod (volume : Measure (Vec d))).restrict
      (Ioo 0 T ×ˢ U))) = _
    rw [← Measure.prod_restrict, integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [f]
    ring
  rw [hF]
  symm
  apply (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo ?_ ?_).symm
  · intro t ht
    exact ⟨lt_of_lt_of_le hb ht.1, lt_of_le_of_lt ht.2 heT⟩
  · intro t ht
    have ht' : t < b ∨ e < t := by
      rcases lt_or_ge t b with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge (fun hh => ht.2 ⟨h, hh⟩))
    rw [c9_time_cutoff_deriv_eq_zero η hzero hone ht', zero_mul]

/-- The spacetime cutoff boundary term vanishes uniformly as its transition
interval shrinks to the zero-trace time. -/
theorem c9_weighted_spacetime_boundary_vanishes {d : ℕ} {κ T r : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hu : MemLp u 2 (volume.restrict (Ioo 0 T ×ˢ sourceBall y r)))
    (htrace : Tendsto (fun t : ℝ => ∫ x in sourceBall y r, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0)) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b e : ℝ, 0 < b → b < e → e ≤ δ → e < T →
      ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η →
      (∀ t, t ≤ b → η t = 0) → (∀ t, e ≤ t → η t = 1) →
      (∀ t, |deriv η t| ≤ B / (e - b)) →
      |∫ z in Ioo 0 T ×ˢ sourceBall y r,
        (ρ z.2 * u z) * ψ z * deriv η z.1| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := c9_weighted_cutoff_boundary_vanishes hκ ρ α hell y u ψ
    hψ hc hu htrace B hB ε hε
  refine ⟨δ, hδ, ?_⟩
  intro b e hb hbe heδ heT η hη hzero hone hderiv
  rw [c9_weighted_boundary_fubini hκ hell hb heT (sourceBall y r)
    u hu ψ hψ hc η hη hzero hone (B / (e - b)) hderiv]
  exact hsmall b e hb hbe heδ heT η hderiv

/-- Expanding the positive-time weak equation identifies its cutoff term with
its density-weighted boundary term. -/
theorem c9_time_cutoff_weak_integral_identity {d : ℕ} {κ T b : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (hb : 0 < b)
    (U : Set (Vec d)) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Ioo 0 T) U u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo (-T) T ×ˢ U)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hzero : ∀ t, t ≤ b → η t = 0)
    (hbounded : ∀ t, 0 ≤ η t ∧ η t ≤ 1)
    (B : ℝ) (hderiv : ∀ t, |deriv η t| ≤ B) :
    (∫ z in Ioo 0 T ×ˢ U, η z.1 *
      (-(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j)))) =
      ∫ z in Ioo 0 T ×ˢ U, (ρ z.2 * u z) * ψ z * deriv η z.1 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict (Ioo 0 T ×ˢ U)
  let f : ℝ × Vec d → ℝ := fun z =>
    -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))
  have hf : Integrable f μ := c9_weighted_weak_integrand_integrable hκ hell
    (Ioo 0 T) U u G hcal.1 hcal.2.1 hcal.2.2.1 ψ hψ hc
  have hcut : Integrable (fun z => η z.1 * f z) μ := by
    apply hf.bdd_mul ((hη.continuous.measurable.comp measurable_fst).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change |η z.1| ≤ 1
      rw [abs_of_nonneg (hbounded z.1).1]
      exact (hbounded z.1).2
  have hbnd := c9_weighted_boundary_integrable hκ hell (Ioo 0 T) U u hcal.1
    ψ hψ hc η hη B hderiv
  have hweak := c9_time_cutoff_weak_equation hb U ρ α u G hcal ψ η hψ hc hs hη hzero
  have heq : (∫ z, (η z.1 * f z) - (ρ z.2 * u z) * ψ z * deriv η z.1 ∂μ) = 0 := by
    convert hweak using 1
    apply integral_congr_ae
    filter_upwards [] with z
    rw [c9_time_cutoff_integrand ρ α u G ψ η (hψ.differentiable (by simp)) (hη.differentiable (by simp))]
    simp only [f, fderiv_apply_one_eq_deriv]
  rw [integral_sub hcut hbnd, sub_eq_zero] at heq
  exact heq

/-- Bounded time cutoffs converging to one on positive times preserve the
integral of every integrable spacetime function. -/
theorem c9_time_cutoff_integral_tendsto {d : ℕ} {T : ℝ} (U : Set (Vec d))
    (hU : MeasurableSet U)
    (f : ℝ × Vec d → ℝ) (hf : Integrable f (volume.restrict (Ioo 0 T ×ˢ U)))
    (η : ℕ → ℝ → ℝ) (hmeas : ∀ n, Measurable (η n))
    (hbound : ∀ n t, 0 ≤ η n t ∧ η n t ≤ 1)
    (hlim : ∀ t, 0 < t → Tendsto (fun n => η n t) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ z in Ioo 0 T ×ˢ U, η n z.1 * f z) atTop
      (𝓝 (∫ z in Ioo 0 T ×ˢ U, f z)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict (Ioo 0 T ×ˢ U)
  apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
  · intro n
    exact ((hmeas n).comp measurable_fst).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [] with z
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hbound n z.1).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbound n z.1).2
  · apply (ae_restrict_iff' (measurableSet_Ioo.prod hU)).2
    filter_upwards [] with z hz
    simpa only [one_mul] using (hlim z.1 hz.1.1).mul tendsto_const_nhds

/-- A fixed sequence of smooth cutoffs has transitions shrinking to zero,
with the derivative controlled uniformly in the inverse transition width. -/
theorem c9_exists_time_cutoff_sequence :
    ∃ (B : ℝ) (e : ℕ → ℝ) (η : ℕ → ℝ → ℝ), 0 < B ∧
      Tendsto e atTop (𝓝 0) ∧
      (∀ n, 0 < e n ∧ ContDiff ℝ (⊤ : ℕ∞) (η n) ∧
        (∀ t, t ≤ e n / 2 → η n t = 0) ∧
        (∀ t, e n ≤ t → η n t = 1) ∧
        ∀ t, 0 ≤ η n t ∧ η n t ≤ 1 ∧
          |deriv (η n) t| ≤ B / (e n - e n / 2)) := by
  obtain ⟨B, hB, hcut⟩ := c9_exists_time_cutoff
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hegap (n : ℕ) : e n / 2 < e n := by have := hepos n; linarith
  choose η hη hzero hone hbound using fun n => hcut (e n / 2) (e n) (hegap n)
  refine ⟨B, e, η, hB, ?_, ?_⟩
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact ⟨hepos n, hη n, hzero n, hone n, hbound n⟩

/-- Zero trace eliminates the positive-time weak integral even for a test
that reaches the initial time. -/
theorem c9_weighted_zero_trace_weak_integral {d : ℕ} {κ T r : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Ioo 0 T) (sourceBall y r) u G)
    (htrace : Tendsto (fun t : ℝ => ∫ x in sourceBall y r, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0))
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo (-T) T ×ˢ sourceBall y r) :
    (∫ z in Ioo 0 T ×ˢ sourceBall y r,
      -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  let U := sourceBall y r
  let f : ℝ × Vec d → ℝ := fun z =>
    -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))
  have hU : MeasurableSet U := by
    have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
      continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
    have hnorm : Continuous (fun v : Vec d => euclideanNorm v) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp hsum
    exact (isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hf : Integrable f (volume.restrict (Ioo 0 T ×ˢ U)) :=
    c9_weighted_weak_integrand_integrable hκ hell (Ioo 0 T) U u G
      hcal.1 hcal.2.1 hcal.2.2.1 ψ hψ hc
  obtain ⟨B, e, η, hB, he, hη⟩ := c9_exists_time_cutoff_sequence
  have hlimη (t : ℝ) (ht : 0 < t) : Tendsto (fun n => η n t) atTop (𝓝 1) := by
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he.eventually (eventually_lt_nhds ht)] with n hn
    exact (hη n).2.2.2.1 t hn.le
  have hmain := c9_time_cutoff_integral_tendsto U hU f hf η
    (fun n => (hη n).2.1.continuous.measurable)
    (fun n t => ⟨((hη n).2.2.2.2 t).1, ((hη n).2.2.2.2 t).2.1⟩) hlimη
  have hzero : Tendsto (fun n => ∫ z in Ioo 0 T ×ˢ U, η n z.1 * f z) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := c9_weighted_spacetime_boundary_vanishes hκ ρ α hell y u ψ
      hψ hc hcal.1 htrace B hB.le (ε / 2) (by positivity)
    have hev : ∀ᶠ n in atTop, e n < min δ T := he.eventually (eventually_lt_nhds (lt_min hδ hT))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, ?_⟩
    intro n hn
    have hen := hN n hn
    have hp := (hη n).1
    have hbe : e n / 2 < e n := by linarith
    have hid := c9_time_cutoff_weak_integral_identity hκ hell (by linarith : 0 < e n / 2)
      U u G hcal ψ hψ hc hs (η n) (hη n).2.1 (hη n).2.2.1
      (fun t => ⟨((hη n).2.2.2.2 t).1, ((hη n).2.2.2.2 t).2.1⟩)
      (B / (e n - e n / 2)) (fun t => ((hη n).2.2.2.2 t).2.2)
    have hbound := hsmall (e n / 2) (e n) (by linarith) hbe
      (le_of_lt (lt_of_lt_of_le hen (min_le_left _ _)))
      (lt_of_lt_of_le hen (min_le_right _ _)) (η n) (hη n).2.1
      (hη n).2.2.1 (hη n).2.2.2.1 (fun t => ((hη n).2.2.2.2 t).2.2)
    rw [Real.dist_eq, sub_zero, hid]
    linarith
  exact tendsto_nhds_unique hmain hzero

/-- A weighted caloric function with zero initial L² trace extends calorically
by zero to the past, with its actual weak gradient extended by zero. -/
theorem c9_weighted_caloric_zero_past_gluing {d : ℕ} {κ T r : ℝ}
    (hκ : 0 < κ) (hT : 0 < T) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Ioo 0 T) (sourceBall y r) u G)
    (htrace : Tendsto (fun t : ℝ => ∫ x in sourceBall y r, |u (t, x)|^2)
      (𝓝[>] 0) (𝓝 0)) :
    IsWeightedCaloric ρ α (Ioo (-T) T) (sourceBall y r)
      (fun z => if 0 < z.1 then u z else 0)
      (fun z => if 0 < z.1 then G z else 0) := by
  refine ⟨c9_zero_past_memLp _ _ hcal.1,
    c9_zero_past_gradient_measurable _ ρ α u G hcal,
    c9_zero_past_gradient_memLp _ ρ α u G hcal,
    c9_zero_past_ae_weak_gradient _ u G hcal.2.2.2.1, ?_⟩
  intro ψ hψ hc hs
  rw [c9_zero_past_weak_integral hT (sourceBall y r) ρ α u G ψ]
  apply c9_weighted_zero_trace_weak_integral hκ hT hell y u G hcal htrace ψ hψ hc
  simpa only [interior_Ioo] using hs

end EinsteinFull.Calculus
