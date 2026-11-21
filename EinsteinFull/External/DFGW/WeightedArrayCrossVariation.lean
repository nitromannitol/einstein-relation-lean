import EinsteinFull.External.DFGW.FinitePrefixAlgebra
import EinsteinFull.External.DFGW.FiniteCrossVariation

/-! # Cross-variation of prefix-weighted martingale arrays

The quadratic sum of a martingale array whose vector weights are sums of truncated
directions expands into pairwise prefix cross-variations.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ}

/-- A vector weight obtained by retaining each direction along its prefix. -/
noncomputable def prefixVectorWeight {J : Type*} (s : Finset J) (m : ℕ → J → ℕ)
    (e : J → Vec d) (n k : ℕ) : Vec d :=
  ∑ j ∈ s, if k < m n j then e j else 0

omit [MeasurableSpace S] [BorelSpace S] in
/-- The squared array with prefix weights is a sum of pairwise prefix cross-variations. -/
theorem sum_sq_scaledVectorWeightedIncrement_prefix {J : Type*} (s : Finset J)
    (m : ℕ → J → ℕ) (e : J → Vec d) (N : ℝ≥0 → C(ℝ, S) → Vec d)
    (n : ℕ) (η : C(ℝ, S)) (hm : ∀ j ∈ s, m n j ≤ n + 1) :
    ∑ k ∈ Finset.range (n + 1),
      scaledVectorWeightedIncrement N (prefixVectorWeight s m e) n k η ^ 2 =
    ∑ j ∈ s, ∑ l ∈ s, ∑ k ∈ Finset.range (min (m n j) (m n l)),
      scaledProjectedIncrement N (e j) n k η * scaledProjectedIncrement N (e l) n k η := by
  classical
  have h (k : ℕ) : scaledVectorWeightedIncrement N (prefixVectorWeight s m e) n k η =
      ∑ j ∈ s, if k < m n j then scaledProjectedIncrement N (e j) n k η else 0 := by
    simp only [scaledVectorWeightedIncrement, scaledProjectedIncrement, prefixVectorWeight,
      dot, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  simp_rw [h]
  exact sum_sq_prefix_sum_eq_sum_min s (n + 1) (m n)
    (fun j k => scaledProjectedIncrement N (e j) n k η) hm

/-- The quadratic sums of scaled time-prefix weights converge to the pairwise covariance. -/
theorem tendstoInMeasure_sum_sq_scaledVectorWeightedIncrement_prefix
    {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} (s : Finset J) (e : J → Vec d) (r : J → ℝ)
    (hr : ∀ j ∈ s, 0 ≤ r j ∧ r j ≤ 1) :
    TendstoInMeasure P (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledVectorWeightedIncrement N
        (prefixVectorWeight s (fun n j => ⌊r j * (n + 1 : ℝ)⌋₊) e) n k η ^ 2) atTop
      (fun _ => ∑ j ∈ s, ∑ l ∈ s, min (r j) (r l) *
        ∫ η, dot (e j) (N 1 η) * dot (e l) (N 1 η) ∂P) := by
  classical
  have hm (n : ℕ) (j : J) (hj : j ∈ s) : ⌊r j * (n + 1 : ℝ)⌋₊ ≤ n + 1 := by
    apply Nat.floor_le_of_le
    have h := mul_le_mul_of_nonneg_right (hr j hj).2 (show (0 : ℝ) ≤ n + 1 by positivity)
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using h
  have hmin (n : ℕ) (j l : J) :
      min ⌊r j * (n + 1 : ℝ)⌋₊ ⌊r l * (n + 1 : ℝ)⌋₊ =
        ⌊min (r j) (r l) * (n + 1 : ℝ)⌋₊ := by
    rcases le_total (r j) (r l) with h | h
    · rw [min_eq_left h, min_eq_left (Nat.floor_mono (mul_le_mul_of_nonneg_right h (by positivity)))]
    · rw [min_eq_right h, min_eq_right (Nat.floor_mono (mul_le_mul_of_nonneg_right h (by positivity)))]
  have hc := tendstoInMeasure_sum_floorCrossSum hP hcoord hμ hPfin N hN2 hstat
    (s.product s) (fun p => e p.1) (fun p => e p.2) (fun p => min (r p.1) (r p.2))
    (by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      exact le_min (hr p.1 hp1).1 (hr p.2 hp2).1)
  refine TendstoInMeasure.congr ?_ ?_ hc
  · intro n
    filter_upwards with η
    calc
      _ = ∑ j ∈ s, ∑ l ∈ s, ∑ k ∈ Finset.range ⌊min (r j) (r l) * (n + 1 : ℝ)⌋₊,
          scaledProjectedIncrement N (e j) n k η * scaledProjectedIncrement N (e l) n k η :=
        Finset.sum_product s s _
      _ = _ := by
        symm
        rw [sum_sq_scaledVectorWeightedIncrement_prefix s _ e N n η (hm n)]
        simp only [hmin]
  · filter_upwards with η
    exact Finset.sum_product s s _

end EinsteinFull.External.DFGW
