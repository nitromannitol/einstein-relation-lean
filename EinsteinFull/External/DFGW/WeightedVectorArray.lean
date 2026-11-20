import EinsteinFull.External.DFGW.WeightedVectorMartingale

/-! # Vector-weighted martingale arrays

Diffusively scaled, deterministically vector-weighted increments form triangular martingale
arrays, including the linear combinations needed for finite-dimensional convergence.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The row-normalized martingale increment against a deterministic vector weight. -/
noncomputable def scaledVectorWeightedIncrement (N : ℝ≥0 → C(ℝ, S) → Vec d)
    (w : ℕ → ℕ → Vec d) (n k : ℕ) (η : C(ℝ, S)) : ℝ :=
  (Real.sqrt (n + 1))⁻¹ * dot (w n k) (N ((k : ℝ≥0) + 1) η - N k η)

/-- Every row of the scaled vector-weighted array has martingale partial sums. -/
theorem martingale_scaledVectorWeightedIncrement (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (w : ℕ → ℕ → Vec d) (n : ℕ) :
    Martingale (fun m η => ∑ k ∈ Finset.range m, scaledVectorWeightedIncrement N w n k η)
      (gridPast 1) P := by
  have h := (martingale_sum_vectorWeighted_increments hP N hN (w n)).smul
    (Real.sqrt (n + 1))⁻¹
  have heq : (fun m η => ∑ k ∈ Finset.range m, scaledVectorWeightedIncrement N w n k η) =
      (Real.sqrt (n + 1))⁻¹ • (fun m η => ∑ k ∈ Finset.range m,
        dot (w n k) (N ((k : ℝ≥0) + 1) η - N k η)) := by
    funext m η
    simp only [scaledVectorWeightedIncrement, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [heq]
  exact h

end EinsteinFull.External.DFGW
