import EinsteinFull.Regeneration.BackwardHittingFromWalk
import EinsteinFull.Regeneration.CycleCount

/-!
# Path domination between slab exits

The slab confinement and the embedded-walk comparison extend from exit
positions to all times when the exit clock diverges.
-/

open MeasureTheory Filter EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A diverging slab clock, confinement between exits, and comparison at exit times
give all-time domination by the walk with one spatial step of slack. -/
theorem all_time_domination_of_slab_exits {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (γ : Ω → Path d) (i : Fin d)
    (X : ℕ → Ω → ℝ) (τ : ℕ → Ω → ℝ≥0) (lam L : ℝ)
    (hzero : ∀ᵐ ω ∂μ, τ 0 ω = 0)
    (htop : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (τ n ω : ℝ)) atTop atTop)
    (hslab : ∀ᵐ ω ∂μ, ∀ n t, τ n ω ≤ t → t ≤ τ (n + 1) ω →
      -(L / lam) ≤ γ ω t i - γ ω (τ n ω) i)
    (hcompare : ∀ n, ∀ᵐ ω ∂μ,
      (L / lam) * (∑ j ∈ range n, X j ω) ≤ γ ω (τ n ω) i - γ ω 0 i) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ∃ n : ℕ,
      (L / lam) * ((∑ j ∈ range n, X j ω) - 1) ≤ γ ω t i - γ ω 0 i := by
  have hcomp : ∀ᵐ ω ∂μ, ∀ n, (L / lam) * (∑ j ∈ range n, X j ω) ≤
      γ ω (τ n ω) i - γ ω 0 i := ae_all_iff.mpr hcompare
  filter_upwards [hzero, htop, hslab, hcomp] with ω hω0 hωtop hωslab hωcomp t
  let clock : ℕ → ℝ := fun n => τ n ω
  have hclock0 : clock 0 = 0 := by simp only [clock, hω0, NNReal.coe_zero]
  let n := cycleCount clock hωtop t
  have hn := cycleCount_bracket clock hωtop hclock0 t t.coe_nonneg
  have hlo : τ n ω ≤ t := NNReal.coe_le_coe.mp hn.1
  have hhi : t ≤ τ (n + 1) ω := NNReal.coe_le_coe.mp hn.2.le
  refine ⟨n, ?_⟩
  have hs := hωslab n t hlo hhi
  have hc := hωcomp n
  nlinarith

end EinsteinFull.Regeneration
