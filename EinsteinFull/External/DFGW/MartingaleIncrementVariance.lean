import EinsteinFull.External.DFGW.VectorStationaryMartingaleVariance

/-! # Variance of projected martingale increments

The second moment of a projected stationary martingale increment is its elapsed time times the
unit-time second moment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Projected stationary martingale increments have variance proportional to elapsed time. -/
theorem integral_dot_martingale_increment_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ η, dot e (N t η - N s η) ^ 2 ∂P) =
      ((t - s : ℝ≥0) : ℝ) * ∫ η, dot e (N 1 η) ^ 2 ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have hNm : StronglyMeasurable (fun η => dot e (N (t - s) η) ^ 2) := by
    have hm := L.continuous.comp_stronglyMeasurable
      ((hN.stronglyAdapted (t - s)).mono (Draft.dfgwPast.le _))
    have hm' : StronglyMeasurable (fun η => dot e (N (t - s) η)) := by
      simpa only [hL] using hm
    exact (continuous_pow 2).comp_stronglyMeasurable hm'
  calc
    _ = ∫ η, dot e (N (t - s) (Draft.dfgwShift s η)) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hstat s (t - s)] with η hη
      rw [add_tsub_cancel_of_le hst] at hη
      rw [hη]
    _ = ∫ η, dot e (N (t - s) η) ^ 2 ∂P.map (Draft.dfgwShift s) := by
      symm
      apply integral_map (measurable_shift _).aemeasurable
      rw [hP.stationary]
      exact hNm.aestronglyMeasurable
    _ = ∫ η, dot e (N (t - s) η) ^ 2 ∂P := by rw [hP.stationary]
    _ = _ := integral_dot_stationary_martingale_sq hP N hN hN2 hstat e (t - s)

end EinsteinFull.External.DFGW
