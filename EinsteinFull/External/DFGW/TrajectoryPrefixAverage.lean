import EinsteinFull.External.DFGW.ConvergenceInMeasureScale

/-! # Prefix averages of stationary trajectories

Partial sums over a deterministic number of grid points converge after normalization by a
second scale whenever the ratio of the two scales converges.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A normalized prefix sum tends in probability to its limiting fraction times the mean. -/
theorem tendstoInMeasure_shift_prefixAverage (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t)
    (f : C(ℝ, S) → ℝ) (hf : Integrable f P) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (r : ℝ)
    (hr : Tendsto (fun n : ℕ => (m n : ℝ) / (n + 1)) atTop (𝓝 r)) :
    TendstoInMeasure P (fun (n : ℕ) η => (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (m n),
      f (Draft.dfgwShift ((k • t : ℝ≥0) : ℝ) η)) atTop
      (fun _ => r * ∫ η, f η ∂P) := by
  let : IsProbabilityMeasure P := hP.probability
  have havg := (tendstoInMeasure_shift_empiricalAverage hP hcoord hμ hPfin ht f hf).comp hm
  have hscaled := tendstoInMeasure_mul_const_sequence
    (fun n η => (m n : ℝ)⁻¹ * ∑ k ∈ Finset.range (m n),
      f (Draft.dfgwShift ((k • t : ℝ≥0) : ℝ) η))
    (∫ η, f η ∂P) (fun n => (m n : ℝ) / (n + 1)) r havg hr
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hscaled
  filter_upwards [hm.eventually (eventually_gt_atTop 0)] with n hn
  apply ae_of_all P
  intro η
  have hn' : (m n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [div_eq_mul_inv]
  field_simp

end EinsteinFull.External.DFGW
