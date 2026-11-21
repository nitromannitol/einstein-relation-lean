import EinsteinFull.External.DFGW.WeightedMartingale
import EinsteinFull.External.DFGW.MartingaleArray

/-! # Vector-weighted martingale increments

Partial sums of vector martingale increments against deterministic vector weights are
martingales on the unit-time grid.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Finite sums of real martingales are martingales. -/
theorem martingale_finset_sum {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    {Q : Measure Ω} {ℱ : Filtration ι (inferInstance : MeasurableSpace Ω)}
    {J : Type*} (s : Finset J) (M : J → ι → Ω → ℝ) (hM : ∀ j ∈ s, Martingale (M j) ℱ Q) :
    Martingale (fun t ω => ∑ j ∈ s, M j t ω) ℱ Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have heq : (fun t ω => ∑ j ∈ (∅ : Finset J), M j t ω) = (0 : ι → Ω → ℝ) := by
      funext t ω
      simp
    rw [heq]
    exact martingale_zero ℝ ℱ Q
  | @insert j s hjs ih =>
    have hj : Martingale (M j) ℱ Q := hM j (Finset.mem_insert_self j s)
    have hs : ∀ k ∈ s, Martingale (M k) ℱ Q := fun k hk => hM k (Finset.mem_insert_of_mem hk)
    have hadd := hj.add (ih hs)
    have heq : (fun t ω => ∑ k ∈ insert j s, M k t ω) =
        M j + (fun t ω => ∑ k ∈ s, M k t ω) := by
      funext t ω
      simp only [Finset.sum_insert hjs, Pi.add_apply]
    rw [heq]
    exact hadd

/-- Vector-weighted sums of unit martingale increments are martingales. -/
theorem martingale_sum_vectorWeighted_increments (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (w : ℕ → Vec d) :
    Martingale (fun n η => ∑ k ∈ Finset.range n,
      dot (w k) (N ((k : ℝ≥0) + 1) η - N k η)) (gridPast 1) P := by
  let : IsProbabilityMeasure P := hP.probability
  let M (i : Fin d) : ℕ → C(ℝ, S) → ℝ := fun k η => N k η i
  have hM (i : Fin d) : Martingale (M i) (gridPast 1) P := by
    have hproj := martingale_continuousLinearMap hN
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)
    have hproj' : Martingale (fun t η => N t η i) Draft.dfgwPast P := by
      simpa only [ContinuousLinearMap.proj_apply] using hproj
    constructor
    · intro k
      change StronglyMeasurable[Draft.dfgwPast (k • (1 : ℝ≥0))] (fun η => N k η i)
      have hk : k • (1 : ℝ≥0) = (k : ℝ≥0) := by simp
      rw [hk]
      exact hproj'.stronglyMeasurable k
    · intro k l hkl
      simpa only [gridPast, nsmul_eq_mul, mul_one] using
        hproj'.condExp_ae_eq (show (k : ℝ≥0) ≤ l by exact_mod_cast hkl)
  let G (i : Fin d) : ℕ → C(ℝ, S) → ℝ := fun n η =>
    ∑ k ∈ Finset.range n, w k i * (M i (k + 1) η - M i k η)
  have hG (i : Fin d) : Martingale (G i) (gridPast 1) P :=
    martingale_sum_weighted_increments (M i) (hM i) (fun k => w k i)
  have hsum := martingale_finset_sum Finset.univ G (fun i _ => hG i)
  have heq : (fun n η => ∑ i : Fin d, G i n η) =
      (fun n η => ∑ k ∈ Finset.range n, dot (w k) (N ((k : ℝ≥0) + 1) η - N k η)) := by
    funext n η
    simp only [G, M, dot, Pi.sub_apply, Nat.cast_add, Nat.cast_one]
    exact Finset.sum_comm
  rw [heq] at hsum
  exact hsum

end EinsteinFull.External.DFGW
