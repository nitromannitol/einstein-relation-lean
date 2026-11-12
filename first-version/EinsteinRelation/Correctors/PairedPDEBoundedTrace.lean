import EinsteinRelation.Correctors.PairedPDEInitialL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Bounded almost-everywhere initial limits give the strong paired trace

Source: `paper/main.tex:821–838,850`. AKM (E.11), printed p. 501, gives an
almost-everywhere initial limit for the Green-function evolution of a
bounded scalar datum. Dominated convergence then gives the strong local
L² trace. The kernel representation and its initial limit remain explicit
here; they are not consequences asserted for every distributional solution.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- Bounded scalar convergence yields local quadratic convergence.
Source: paper/main.tex:821–838,850; AKM (E.11), p. 501. -/
theorem paired_tendsto_integral_sq_of_bounded_ae {X T : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {l : Filter T} [l.IsCountablyGenerated]
    {u : T → X → ℝ} {h : X → ℝ} {B : ℝ}
    (hu : ∀ᶠ t in l, AEStronglyMeasurable (u t) μ)
    (hh : AEStronglyMeasurable h μ) (hB : 0 ≤ B)
    (hub : ∀ᶠ t in l, ∀ᵐ x ∂μ, |u t x| ≤ B)
    (hhb : ∀ᵐ x ∂μ, |h x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t => u t x) l (𝓝 (h x))) :
    Tendsto (fun t => ∫ x, (u t x - h x)^2 ∂μ) l (𝓝 0) := by
  have hbound : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖(u t x - h x)^2‖ ≤ (2 * B)^2 := by
    filter_upwards [hub] with t ht
    filter_upwards [ht, hhb] with x hux hhx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hd : |u t x - h x| ≤ 2 * B :=
      (abs_sub (u t x) (h x)).trans (by linarith only [hux, hhx])
    have hs := (sq_le_sq₀ (abs_nonneg (u t x - h x)) (by positivity : 0 ≤ 2 * B)).mpr hd
    simpa only [sq_abs] using hs
  have hzero : ∀ᵐ x ∂μ, Tendsto (fun t => (u t x - h x)^2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      (hx.sub (tendsto_const_nhds (x := h x))).pow 2
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (fun _ : X => (2 * B)^2)
      (hu.mono fun t ht => (ht.sub hh).pow 2) hbound (integrable_const _) hzero)

/-- Almost-everywhere initial convergence and a uniform bound suffice for
strong convergence of the actual L² representatives. No Cauchy premise
is used. Source: `paper/main.tex:821–838,850`. -/
theorem paired_tendsto_L2_of_bounded_ae {X T : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {l : Filter T} [l.IsCountablyGenerated]
    (f : T → Lp ℝ 2 μ) {u : T → X → ℝ} {a : X → ℝ}
    (ha : MemLp a 2 μ) (hrep : ∀ᶠ t in l, (f t : X → ℝ) =ᵐ[μ] u t)
    {B : ℝ} (hB : 0 ≤ B)
    (hub : ∀ᶠ t in l, ∀ᵐ x ∂μ, |u t x| ≤ B)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t => u t x) l (𝓝 (a x))) :
    Tendsto f l (𝓝 (ha.toLp a)) := by
  apply paired_tendsto_L2_of_quadratic_representatives f ha hrep
  apply paired_tendsto_integral_sq_of_bounded_ae ?_ ha.1 hB hub hab hlim
  filter_upwards [hrep] with t ht
  exact (Lp.aestronglyMeasurable (f t)).congr ht

open External.AKM Environment.AKMTestIntegralSupport

/-- The bounded almost-everywhere initial-limit route constructs the strong
zero initial extension of the actual paired flow. The candidate scalar
limit is arbitrary; the distributional initial condition proves it is zero.
Source: `paper/main.tex:821–838,850`. -/
theorem paired_semigroupSolution_exists_zero_L2_extension_of_bounded_ae
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (hg : Set.EqOn g₁ g₂ U)
    (f : ℝ → Lp ℝ 2 (volume.restrict U))
    (hrep : ∀ t : ℝ, 0 < t →
      (f t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x))
    {a : Vec d → ℝ} (ha : MemLp a 2 (volume.restrict U))
    {B : ℝ} (hB : 0 ≤ B)
    (hub : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ x ∂volume.restrict U, |u₁ (t, x) - u₂ (t, x)| ≤ B)
    (hab : ∀ᵐ x ∂volume.restrict U, |a x| ≤ B)
    (hlim : ∀ᵐ x ∂volume.restrict U,
      Tendsto (fun t => u₁ (t, x) - u₂ (t, x))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a x))) :
    ∃ v : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousWithinAt v (Set.Ici 0) 0 ∧ v 0 = 0 ∧
      (∀ t : ℝ, 0 < t →
        (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x)) ∧
      Tendsto (fun t => ∫ x in U, (u₁ (t, x) - u₂ (t, x))^2 ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hfrep : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      (f t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hrep t ht
  have hstrong := paired_tendsto_L2_of_bounded_ae f ha hfrep hB hub hab hlim
  exact paired_semigroupSolution_exists_zero_L2_extension_of_cauchy
    h₁ h₂ hU hg f hrep hstrong.cauchy_map

/-- Scalar bounded initial limits construct a strong extension of the paired
flow, including its positive-time L² classes. The zero value is deduced from
agreement of the vector initial data. Source: `paper/main.tex:821–838,850`. -/
theorem paired_semigroupSolution_exists_zero_L2_extension_of_scalar_limits
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (hg : Set.EqOn g₁ g₂ U)
    {a₁ a₂ : Vec d → ℝ}
    (ha₁ : AEStronglyMeasurable a₁ (volume.restrict U))
    (ha₂ : AEStronglyMeasurable a₂ (volume.restrict U))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hu₁b : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂volume.restrict U, |u₁ (t, x)| ≤ B₁)
    (hu₂b : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂volume.restrict U, |u₂ (t, x)| ≤ B₂)
    (ha₁b : ∀ᵐ x ∂volume.restrict U, |a₁ x| ≤ B₁)
    (ha₂b : ∀ᵐ x ∂volume.restrict U, |a₂ x| ≤ B₂)
    (hlim₁ : ∀ᵐ x ∂volume.restrict U, Tendsto (fun t => u₁ (t, x))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a₁ x)))
    (hlim₂ : ∀ᵐ x ∂volume.restrict U, Tendsto (fun t => u₂ (t, x))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a₂ x))) :
    ∃ v : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousWithinAt v (Set.Ici 0) 0 ∧ v 0 = 0 ∧
      (∀ t : ℝ, 0 < t →
        (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x)) ∧
      Tendsto (fun t => ∫ x in U, (u₁ (t, x) - u₂ (t, x))^2 ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hub (t : ℝ) (ht : 0 < t) : ∀ᵐ x ∂volume.restrict U,
      |u₁ (t, x) - u₂ (t, x)| ≤ B₁ + B₂ := by
    filter_upwards [hu₁b t ht, hu₂b t ht] with x hx₁ hx₂
    exact (abs_sub _ _).trans (add_le_add hx₁ hx₂)
  have hab : ∀ᵐ x ∂volume.restrict U, |a₁ x - a₂ x| ≤ B₁ + B₂ := by
    filter_upwards [ha₁b, ha₂b] with x hx₁ hx₂
    exact (abs_sub _ _).trans (add_le_add hx₁ hx₂)
  have hm (t : ℝ) (ht : 0 < t) :
      MemLp (fun x => u₁ (t, x) - u₂ (t, x)) 2 (volume.restrict U) := by
    have hc₁ : Continuous (fun x => u₁ (t, x)) :=
      h₁.1.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨ht, Set.mem_univ _⟩)
    have hc₂ : Continuous (fun x => u₂ (t, x)) :=
      h₂.1.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨ht, Set.mem_univ _⟩)
    exact MemLp.of_bound (hc₁.sub hc₂).aestronglyMeasurable (B₁ + B₂)
      (by simpa only [Real.norm_eq_abs] using hub t ht)
  let f : ℝ → Lp ℝ 2 (volume.restrict U) := fun t =>
    if ht : 0 < t then (hm t ht).toLp (fun x => u₁ (t, x) - u₂ (t, x)) else 0
  have hrep (t : ℝ) (ht : 0 < t) :
      (f t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x) := by
    simp only [f, dif_pos ht]
    exact (hm t ht).coeFn_toLp
  have ha : MemLp (fun x => a₁ x - a₂ x) 2 (volume.restrict U) :=
    MemLp.of_bound (ha₁.sub ha₂) (B₁ + B₂)
      (by simpa only [Real.norm_eq_abs] using hab)
  apply paired_semigroupSolution_exists_zero_L2_extension_of_bounded_ae
    h₁ h₂ hU hg f hrep ha (add_nonneg hB₁ hB₂) ?_ hab ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hub t ht
  · filter_upwards [hlim₁, hlim₂] with x hx₁ hx₂
    exact hx₁.sub hx₂

end EinsteinRelation.Correctors
