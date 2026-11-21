import EinsteinFull.External.DFGW.MartingaleMaximalTail

/-! # Maximal norms of stationary martingale increments

The largest norm of the first `n` stationary unit increments is `o(√n)` in probability.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Maximal squared norms of stationary unit increments are sublinear in probability. -/
theorem tendsto_measureReal_max_martingale_increment_norm_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ k < n, δ * n ≤
      ‖N ((k : ℝ≥0) + 1) η - N k η‖ ^ 2}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  have hf : StronglyMeasurable (fun η => ‖N 1 η‖) :=
    ((hN.stronglyAdapted 1).mono (Draft.dfgwPast.le 1)).norm
  have hf2 : MemLp (fun η => ‖N 1 η‖) 2 P := (hN2 1).norm
  have hθ (k : ℕ) : MeasurePreserving (Draft.dfgwShift (S := S) (k : ℝ)) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have hg (k : ℕ) : (fun η => ‖N ((k : ℝ≥0) + 1) η - N k η‖) =ᵐ[P]
      fun η => ‖N 1 (Draft.dfgwShift (k : ℝ) η)‖ := by
    filter_upwards [hstat (k : ℝ≥0) 1] with η hη
    exact congrArg norm hη
  exact tendsto_measureReal_max_same_distribution_sq
    (fun k => Draft.dfgwShift (k : ℝ)) hθ _ hf hf2 _ hg hδ

end EinsteinFull.External.DFGW
