import EinsteinFull.External.DFGW.WeightedArraySecondMoment
import LatticeProb.Prob.McLeish.MartingaleCLT

/-! # Central limit theorem for weighted martingale arrays

Bounded deterministic vector weights yield a Gaussian limit whenever the empirical quadratic
variation has a deterministic limit.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Bounded weighted increments satisfy a central limit theorem once their quadratic sums
converge in probability to a deterministic variance. -/
theorem tendstoInDistribution_scaledVectorWeightedIncrement_sum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (w : ℕ → ℕ → Vec d) (C : ℝ) (hw : ∀ n k, ‖w n k‖ ≤ C)
    (σsq : ℝ≥0)
    (hsq : TendstoInMeasure P (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledVectorWeightedIncrement N w n k η ^ 2) atTop (fun _ => (σsq : ℝ))) :
    letI : IsProbabilityMeasure P := hP.probability
    TendstoInDistribution (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledVectorWeightedIncrement N w n k η) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq) := by
  let : IsProbabilityMeasure P := hP.probability
  have hmart (n : ℕ) : Martingale
      (fun k η => ∑ j ∈ Finset.range k, scaledVectorWeightedIncrement N w n j η) (gridPast 1) P :=
    martingale_scaledVectorWeightedIncrement hP N hN w n
  have hint (n : ℕ) : Integrable (fun η => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => scaledVectorWeightedIncrement N w n k η ^ 2)) P :=
    (integrable_max_scaledVectorWeightedIncrement_sq_and_integral_le hP N hN hN2 hstat w C hw n).1
  have hbdd : ∃ B : ℝ, ∀ n, (∫ η, (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => scaledVectorWeightedIncrement N w n k η ^ 2) ∂P) ≤ B := by
    refine ⟨(((d : ℝ) * (|C| + 1) + 1) ^ 2) * ∫ η, ‖N 1 η‖ ^ 2 ∂P, fun n => ?_⟩
    exact (integrable_max_scaledVectorWeightedIncrement_sq_and_integral_le
      hP N hN hN2 hstat w C hw n).2
  have hmax := tendstoInMeasure_max_scaledVectorWeightedIncrement hP N hN hN2 hstat w C hw
  exact LatticeProb.McLeish.tendstoInDistribution_martingale_clt P (fun _ => gridPast 1)
    (scaledVectorWeightedIncrement N w) (fun n => n + 1) (fun n => Nat.zero_lt_succ n)
    σsq hmart hint hbdd hmax hsq

end EinsteinFull.External.DFGW
