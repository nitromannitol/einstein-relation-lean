import EinsteinFull.External.DFGW.MartingaleFloorCrossVariation
import LatticeProb.Bonanno.ReflectedGMS.Limit.MultiTimeCharFunFromIncrements

/-! # Finite sums of martingale cross-variations

Cross-variations over finitely many scaled time intervals converge jointly under finite
linear combinations.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Cross-variation at any nonnegative scaled time converges to the corresponding covariance. -/
theorem tendstoInMeasure_scaledProjectedIncrement_floorCrossSum_nonneg
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e f : Vec d) (r : ℝ) (hr : 0 ≤ r) :
    TendstoInMeasure P (fun (n : ℕ) η => ∑ k ∈ Finset.range ⌊r * (n + 1 : ℝ)⌋₊,
      scaledProjectedIncrement N e n k η * scaledProjectedIncrement N f n k η) atTop
      (fun _ => r * ∫ η, dot e (N 1 η) * dot f (N 1 η) ∂P) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [zero_mul, Nat.floor_zero, Finset.range_zero, Finset.sum_empty]
    change TendstoInMeasure P (fun (_ : ℕ) (_ : C(ℝ, S)) => (0 : ℝ)) atTop
      (0 : C(ℝ, S) → ℝ)
    exact (ReflectedGMS.MultiTimeCharFun.tendstoInMeasure_zero_of_ae_norm_le
        (P := P) (f := fun (_ : ℕ) (_ : C(ℝ, S)) => (0 : ℝ))
        (c := fun _ => 0) tendsto_const_nhds (fun _ => Eventually.of_forall fun _ => by simp))
  · exact tendstoInMeasure_scaledProjectedIncrement_floorCrossSum hP hcoord hμ hPfin
      N hN2 hstat e f r hr

/-- Finite sums of cross-variations converge to the corresponding sum of covariances. -/
theorem tendstoInMeasure_sum_floorCrossSum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} (s : Finset J) (e f : J → Vec d) (r : J → ℝ)
    (hr : ∀ j ∈ s, 0 ≤ r j) :
    TendstoInMeasure P (fun (n : ℕ) η => ∑ j ∈ s,
      ∑ k ∈ Finset.range ⌊r j * (n + 1 : ℝ)⌋₊,
        scaledProjectedIncrement N (e j) n k η * scaledProjectedIncrement N (f j) n k η) atTop
      (fun _ => ∑ j ∈ s, r j * ∫ η, dot (e j) (N 1 η) * dot (f j) (N 1 η) ∂P) := by
  classical
  let X (j : J) (n : ℕ) (η : C(ℝ, S)) : ℝ :=
    ∑ k ∈ Finset.range ⌊r j * (n + 1 : ℝ)⌋₊,
      scaledProjectedIncrement N (e j) n k η * scaledProjectedIncrement N (f j) n k η
  let a (j : J) : ℝ := r j * ∫ η, dot (e j) (N 1 η) * dot (f j) (N 1 η) ∂P
  have h (j : J) (hj : j ∈ s) : TendstoInMeasure P
      (fun n η => X j n η - a j) atTop 0 := by
    have hcross := tendstoInMeasure_scaledProjectedIncrement_floorCrossSum_nonneg
      hP hcoord hμ hPfin N hN2 hstat (e j) (f j) (r j) (hr j hj)
    rw [tendstoInMeasure_iff_norm] at hcross ⊢
    simpa only [X, a, Pi.zero_apply, sub_zero] using hcross
  have hsum := ReflectedGMS.MultiTimeCharFun.tendstoInMeasure_zero_finset_sum
    (P := P) s h
  rw [tendstoInMeasure_iff_norm] at hsum ⊢
  simpa only [X, a, Pi.zero_apply, sub_zero, ← Finset.sum_sub_distrib] using hsum

end EinsteinFull.External.DFGW
