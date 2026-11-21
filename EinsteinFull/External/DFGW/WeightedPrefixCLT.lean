import EinsteinFull.External.DFGW.WeightedArrayCrossVariation
import EinsteinFull.External.DFGW.WeightedArrayCLT

/-! # Central limit theorem for prefix-weighted arrays

Finite linear combinations of time-prefix martingale increments converge to a centered
Gaussian with the covariance determined by pairwise minimum times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Prefix vector weights are uniformly bounded by the sum of the direction norms. -/
theorem norm_prefixVectorWeight_le {J : Type*} (s : Finset J) (m : ℕ → J → ℕ)
    (e : J → Vec d) (n k : ℕ) : ‖prefixVectorWeight s m e n k‖ ≤ ∑ j ∈ s, ‖e j‖ := by
  classical
  calc
    ‖prefixVectorWeight s m e n k‖ ≤ ∑ j ∈ s, ‖if k < m n j then e j else 0‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs <;> simp

/-- The pairwise minimum-time covariance is nonnegative. -/
theorem prefix_covariance_nonneg
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} (s : Finset J) (e : J → Vec d) (r : J → ℝ)
    (hr : ∀ j ∈ s, 0 ≤ r j ∧ r j ≤ 1) :
    0 ≤ ∑ j ∈ s, ∑ l ∈ s, min (r j) (r l) *
      ∫ η, dot (e j) (N 1 η) * dot (e l) (N 1 η) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  have h := tendstoInMeasure_sum_sq_scaledVectorWeightedIncrement_prefix
    hP hcoord hμ hPfin N hN2 hstat s e r hr
  obtain ⟨ns, _, hns⟩ := h.exists_seq_tendsto_ae
  obtain ⟨η, hη⟩ := hns.exists
  have hnonneg (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range (ns n + 1),
      scaledVectorWeightedIncrement N
        (prefixVectorWeight s (fun n j => ⌊r j * (n + 1 : ℝ)⌋₊) e) (ns n) k η ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  exact ge_of_tendsto hη (Eventually.of_forall hnonneg)

/-- Prefix-weighted martingale increments have a centered Gaussian limit. -/
theorem tendstoInDistribution_scaledVectorWeightedIncrement_prefix
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} (s : Finset J) (e : J → Vec d) (r : J → ℝ)
    (hr : ∀ j ∈ s, 0 ≤ r j ∧ r j ≤ 1) :
    letI : IsProbabilityMeasure P := hP.probability
    TendstoInDistribution (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledVectorWeightedIncrement N
        (prefixVectorWeight s (fun n j => ⌊r j * (n + 1 : ℝ)⌋₊) e) n k η) atTop
      (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (∑ j ∈ s, ∑ l ∈ s, min (r j) (r l) *
        ∫ η, dot (e j) (N 1 η) * dot (e l) (N 1 η) ∂P))) := by
  let : IsProbabilityMeasure P := hP.probability
  have hvar := prefix_covariance_nonneg hP hcoord hμ hPfin N (hN2 1) hstat s e r hr
  have hsq := tendstoInMeasure_sum_sq_scaledVectorWeightedIncrement_prefix
    hP hcoord hμ hPfin N (hN2 1) hstat s e r hr
  apply tendstoInDistribution_scaledVectorWeightedIncrement_sum hP N hN hN2 hstat
    _ (∑ j ∈ s, ‖e j‖) (norm_prefixVectorWeight_le s _ e) _
  simpa only [Real.coe_toNNReal _ hvar] using hsq

end EinsteinFull.External.DFGW
