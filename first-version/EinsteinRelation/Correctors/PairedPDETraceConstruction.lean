import EinsteinRelation.Correctors.PairedPDETrace
import Mathlib.Topology.UniformSpace.Cauchy

/-! # Completion criterion for a strong paired initial trace

Source: `paper/main.tex:822–843`. Completeness constructs a strong initial
extension once the actual positive-time L² classes are Cauchy at zero.
The distributional initial condition then identifies its initial value.
The Cauchy estimate is an internal analytic obligation, not an external input.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Pasting the limit of a Cauchy positive-time L² path constructs an
extension through zero. No initial value is prescribed by the hypotheses.
Source: `paper/main.tex:822–843`. -/
theorem paired_exists_L2_extension_of_cauchy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : ℝ → Lp ℝ 2 μ)
    (hf : Cauchy (Filter.map f (nhdsWithin 0 (Set.Ioi 0)))) :
    ∃ v : ℝ → Lp ℝ 2 μ,
      ContinuousWithinAt v (Set.Ici 0) 0 ∧
      ∀ t : ℝ, 0 < t → v t = f t := by
  obtain ⟨a, ha⟩ := cauchy_map_iff_exists_tendsto.mp hf
  let v : ℝ → Lp ℝ 2 μ := fun t => if 0 < t then f t else a
  have hv0 : v 0 = a := by simp only [v, lt_self_iff_false, ↓reduceIte]
  refine ⟨v, ?_, fun t ht => if_pos ht⟩
  rw [ContinuousWithinAt, hv0]
  have hvpos : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (𝓝 a) := by
    apply ha.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (if_pos ht).symm
  have hvzero : Tendsto v (nhdsWithin 0 ({0} : Set ℝ)) (𝓝 a) := by
    rw [nhdsWithin_singleton, ← hv0]
    exact tendsto_pure_nhds v 0
  have hset : Set.Ici (0 : ℝ) = Set.Ioi 0 ∪ {0} := by
    ext t
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
    simp only [le_iff_lt_or_eq, eq_comm]
  rw [hset, nhdsWithin_union]
  exact tendsto_sup.mpr ⟨hvpos, hvzero⟩

/-- The actual paired flow has a zero strong initial trace whenever its
positive-time L² classes satisfy the local Cauchy estimate. The initial
value is deduced from the source distributional condition.
Source: `paper/main.tex:822–843`. -/
theorem paired_semigroupSolution_exists_zero_L2_extension_of_cauchy
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (hg : Set.EqOn g₁ g₂ U)
    (f : ℝ → Lp ℝ 2 (volume.restrict U))
    (hrep : ∀ t : ℝ, 0 < t →
      (f t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x))
    (hf : Cauchy (Filter.map f (nhdsWithin 0 (Set.Ioi 0)))) :
    ∃ v : ℝ → Lp ℝ 2 (volume.restrict U),
      ContinuousWithinAt v (Set.Ici 0) 0 ∧ v 0 = 0 ∧
      (∀ t : ℝ, 0 < t →
        (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x)) ∧
      Tendsto (fun t => ∫ x in U, (u₁ (t, x) - u₂ (t, x))^2 ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨v, hv, heq⟩ := paired_exists_L2_extension_of_cauchy f hf
  have hvrep : ∀ t : ℝ, 0 < t →
      (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x) := by
    intro t ht
    rw [heq t ht]
    exact hrep t ht
  obtain ⟨hv0, _, henergy⟩ :=
    paired_semigroupSolution_zero_L2_trace_of_continuous_extension h₁ h₂ hU hg v hv hvrep
  exact ⟨v, hv, hv0, hvrep, henergy⟩

end EinsteinRelation.Correctors
