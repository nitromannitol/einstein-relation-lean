import EinsteinRelation.Correctors.PairedPDEInitialL2
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Strong local scalar continuity at positive times

Source: `paper/main.tex:808–816,832–850`. Joint continuity of the actual
scalar semigroup representative gives strong local L² continuity on every
relatively compact spatial set. No deterministic global bound on the flow
and no choice of representatives of its gradient are used.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Every positive-time scalar slice is locally square integrable.
Source: `paper/main.tex:808–816,832–850`. -/
theorem semigroupSolution_scalar_memLp_on_precompact {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {U : Set (Vec d)} (hU : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] {t : ℝ} (ht : 0 < t) :
    MemLp (fun x => u (t,x)) 2 (volume.restrict U) := by
  have hc : Continuous (fun x => u (t,x)) :=
    hsol.1.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  obtain ⟨B, hB⟩ := hU.exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable B
  filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem measurableSet_closure)] with x hx
  exact hB x hx

/-- The actual scalar flow has a strongly continuous local L² realization
at every positive time. The classes are constructed from the given flow.
Source: `paper/main.tex:808–816,832–850`. -/
theorem semigroupSolution_exists_continuous_local_L2 {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {U : Set (Vec d)} (hU : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] :
    ∃ f : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousOn f (Set.Ioi 0) ∧
      ∀ t : ℝ, 0 < t → (f t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u (t,x) := by
  let hm := fun t ht => semigroupSolution_scalar_memLp_on_precompact hsol hU (t := t) ht
  let f : ℝ → Lp ℝ 2 (volume.restrict U) := fun t =>
    if ht : 0 < t then (hm t ht).toLp (fun x => u (t,x)) else 0
  have hrep (t : ℝ) (ht : 0 < t) :
      (f t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u (t,x) := by
    simp only [f, dif_pos ht]
    exact (hm t ht).coeFn_toLp
  refine ⟨f, ?_, hrep⟩
  intro t ht
  change 0 < t at ht
  apply ContinuousAt.continuousWithinAt
  change Tendsto f (𝓝 t) (𝓝 (f t))
  rw [show f t = (hm t ht).toLp (fun x => u (t,x)) by simp only [f, dif_pos ht]]
  apply paired_tendsto_L2_of_quadratic_representatives f (hm t ht)
  · filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hrep s hs
  · have hc : ContinuousOn u (Set.Icc (t/2) (t+1) ×ˢ closure U) :=
      hsol.1.mono (by
        rintro ⟨s,x⟩ ⟨hs,_⟩
        change t/2 ≤ s ∧ s ≤ t+1 at hs
        exact ⟨lt_of_lt_of_le (half_pos ht) hs.1, Set.mem_univ _⟩)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod hU).exists_bound_of_continuousOn hc
    have htime : ∀ᶠ s in 𝓝 t, s ∈ Set.Icc (t/2) (t+1) :=
      Icc_mem_nhds (by linarith) (by linarith)
    have htI : t ∈ Set.Icc (t/2) (t+1) := ⟨by linarith, by linarith⟩
    have hmeas : ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable (fun x => (u (s,x) - u (t,x))^2) (volume.restrict U) := by
      filter_upwards [htime] with s hs
      exact ((hm s (by linarith [hs.1])).1.sub (hm t ht).1).pow 2
    have hbound : ∀ᶠ s in 𝓝 t, ∀ᵐ x ∂volume.restrict U,
        ‖(u (s,x) - u (t,x))^2‖ ≤ (2*B)^2 := by
      filter_upwards [htime] with s hs
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_closure
        (ae_restrict_mem measurableSet_closure)] with x hx
      have hsB := hB (s,x) ⟨hs,hx⟩
      have htB := hB (t,x) ⟨htI,hx⟩
      have hB0 : 0 ≤ B := (norm_nonneg (u (t,x))).trans htB
      have hsub : |u (s,x) - u (t,x)| ≤ 2*B := by
        exact (abs_sub _ _).trans (by simpa only [Real.norm_eq_abs, two_mul] using add_le_add hsB htB)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*B)).mpr hsub
    have hlim : ∀ᵐ x ∂volume.restrict U,
        Tendsto (fun s => (u (s,x) - u (t,x))^2) (𝓝 t) (𝓝 (0 : ℝ)) := by
      apply ae_of_all
      intro x
      have hc' : ContinuousOn (fun s => u (s,x)) (Set.Ioi 0) :=
        hsol.1.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun s hs => ⟨hs, Set.mem_univ _⟩)
      simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
        (((hc' t ht).continuousAt (isOpen_Ioi.mem_nhds ht)).sub_const (u (t,x))).pow 2
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence (fun _ : Vec d => (2*B)^2)
        hmeas hbound (integrable_const _) hlim

/-- A zero-time trace of a paired flow joins its genuine positive-time
L² classes to give a continuous evolution on the entire nonnegative axis.
Source: `paper/main.tex:821–838,850`. -/
theorem paired_semigroupSolutions_continuous_local_L2_of_trace
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)]
    (v : ℝ → Lp ℝ 2 (volume.restrict U))
    (hv₀ : ContinuousWithinAt v (Set.Ici 0) 0)
    (hrep : ∀ t : ℝ, 0 < t →
      (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t,x) - u₂ (t,x)) :
    ContinuousOn v (Set.Ici 0) := by
  obtain ⟨f₁, hf₁, hrep₁⟩ := semigroupSolution_exists_continuous_local_L2 h₁ hU
  obtain ⟨f₂, hf₂, hrep₂⟩ := semigroupSolution_exists_continuous_local_L2 h₂ hU
  have hpos : ContinuousOn v (Set.Ioi 0) := by
    apply (hf₁.sub hf₂).congr
    intro t ht
    apply Lp.ext
    filter_upwards [hrep t ht, hrep₁ t ht, hrep₂ t ht,
      Lp.coeFn_sub (f₁ t) (f₂ t)] with x hv hx₁ hx₂ hxsub
    simp only [Pi.sub_apply] at hxsub
    rw [hxsub, hx₁, hx₂, hv]
  intro t ht
  by_cases ht₀ : t = 0
  · simpa only [ht₀] using hv₀
  · have htpos : t ∈ Set.Ioi 0 := lt_of_le_of_ne ht (Ne.symm ht₀)
    exact ((hpos t htpos).continuousAt (isOpen_Ioi.mem_nhds htpos)).continuousWithinAt

end EinsteinRelation.Correctors
