import EinsteinFull.External.DFGW.VectorStationaryMartingaleVariance
import EinsteinFull.External.DFGW.StationaryMaximalTail

/-! # Maximal unit increments of the stationary martingale

Projected unit increments of the martingale approximation satisfy the maximal-jump estimate
needed for martingale central limit arguments.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Projected unit increments of a stationary-increment square-integrable martingale have
maximal square `o(n)` in probability. -/
theorem tendsto_measureReal_max_martingale_increment_sq
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ k < n, δ * n ≤
      (dot e (N ((k : ℝ≥0) + 1) η - N k η)) ^ 2}) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have hf : StronglyMeasurable (fun η => dot e (N 1 η)) := by
    simpa only [hL] using L.continuous.comp_stronglyMeasurable
      ((hN.stronglyAdapted 1).mono (Draft.dfgwPast.le 1))
  have hf2 : MemLp (fun η => dot e (N 1 η)) 2 P := by
    simpa only [hL] using (hN2 1).continuousLinearMap_comp L
  have hθ (k : ℕ) : MeasurePreserving (Draft.dfgwShift (S := S) (k : ℝ)) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have hg (k : ℕ) : (fun η => dot e (N ((k : ℝ≥0) + 1) η - N k η)) =ᵐ[P]
      fun η => dot e (N 1 (Draft.dfgwShift (k : ℝ) η)) := by
    filter_upwards [hstat (k : ℝ≥0) 1] with η hη
    exact congrArg (dot e) hη
  exact tendsto_measureReal_max_same_distribution_sq
    (fun k => Draft.dfgwShift (k : ℝ)) hθ _ hf hf2 _ hg hδ

end EinsteinFull.External.DFGW
