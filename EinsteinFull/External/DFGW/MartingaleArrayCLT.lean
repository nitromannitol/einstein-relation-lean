import EinsteinFull.External.DFGW.MartingaleArrayVariance
import LatticeProb.Prob.McLeish.MartingaleCLT

/-! # Scalar central limit theorem for stationary martingale arrays

McLeish's theorem applies to the diffusively scaled projected unit increments of the
stationary-increment martingale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Projected unit martingale increments satisfy a scalar central limit theorem. -/
theorem tendstoInDistribution_scaledProjectedIncrement_sum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) :
    letI : IsProbabilityMeasure P := hP.probability
    let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P,
      integral_nonneg fun _ => sq_nonneg _⟩
    TendstoInDistribution (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledProjectedIncrement N e n k η) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq) := by
  let : IsProbabilityMeasure P := hP.probability
  let σsq : ℝ≥0 := ⟨∫ η, dot e (N 1 η) ^ 2 ∂P,
    integral_nonneg fun _ => sq_nonneg _⟩
  have hmart (n : ℕ) : Martingale
      (fun k η => ∑ j ∈ Finset.range k, scaledProjectedIncrement N e n j η) (gridPast 1) P :=
    martingale_scaledProjectedIncrement hP N hN e n
  have hint (n : ℕ) : Integrable (fun η => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => scaledProjectedIncrement N e n k η ^ 2)) P := by
    simpa only [scaledProjectedIncrement] using
      (integrable_max_scaled_martingale_sq_and_integral_le hP N hN hN2 hstat e n).1
  have hbdd : ∃ C : ℝ, ∀ n, (∫ η, (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => scaledProjectedIncrement N e n k η ^ 2) ∂P) ≤ C := by
    refine ⟨∫ η, dot e (N 1 η) ^ 2 ∂P, fun n => ?_⟩
    simpa only [scaledProjectedIncrement] using
      (integrable_max_scaled_martingale_sq_and_integral_le hP N hN hN2 hstat e n).2
  have hmax : TendstoInMeasure P (fun n η => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => |scaledProjectedIncrement N e n k η|))
      atTop (fun _ => 0) := by
    simpa only [scaledProjectedIncrement] using
      tendstoInMeasure_max_scaled_martingale_increment hP N hN hN2 hstat e
  have hsq := tendstoInMeasure_scaledProjectedIncrement_sqSum hP hcoord hμ hPfin N (hN2 1) hstat e
  exact LatticeProb.McLeish.tendstoInDistribution_martingale_clt P (fun _ => gridPast 1)
    (scaledProjectedIncrement N e) (fun n => n + 1) (fun n => Nat.zero_lt_succ n)
    σsq hmart hint hbdd hmax hsq

end EinsteinFull.External.DFGW
