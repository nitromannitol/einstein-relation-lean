import EinsteinFull.External.DFGW.DynkinDyadicObservableSup
import EinsteinFull.External.DFGW.StationaryMaximalTail

/-! # Tails of stationary dyadic block maxima

The largest observable value on the dyadic points of the first `n` unit blocks is
`o(√n)` in probability.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Maximal dyadic values over the first `n` unit blocks have sublinear squared magnitude
in probability. -/
theorem tendsto_measureReal_max_dyadic_observable_blocks
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {η | ∃ k < n, ∃ r j, j ≤ 2 ^ r ∧
      δ * n ≤ |(f : Lp ℝ 2 μ) (η ((k : ℝ) + dyadicGridTime 1 r j))| ^ 2}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hP.probability
  let B := dyadicObservableSup hP f 1
  let θ (k : ℕ) : C(ℝ, S) → C(ℝ, S) := Draft.dfgwShift (k : ℝ)
  have hθ (k : ℕ) : MeasurePreserving (θ k) P P := ⟨measurable_shift _, hP.stationary _⟩
  have hB : StronglyMeasurable B := (measurable_dyadicObservableSup hP f 1).stronglyMeasurable
  have hB2 : MemLp B 2 P := memLp_dyadicObservableSup hP hcoord f 1
  have htail := tendsto_measureReal_max_same_distribution_sq θ hθ B hB hB2
    (fun k η => B (θ k η)) (fun _ => EventuallyEq.rfl) hδ
  have hdom : ∀ᵐ η ∂P, ∀ k r j : ℕ, j ≤ 2 ^ r →
      |(f : Lp ℝ 2 μ) (η ((k : ℝ) + dyadicGridTime 1 r j))| ≤ B (θ k η) := by
    apply ae_all_iff.mpr
    intro k
    have h := (hθ k).quasiMeasurePreserving.ae (ae_abs_le_dyadicObservableSup hP hcoord f 1)
    filter_upwards [h] with η hη r j hj
    have h' := hη r j hj
    simpa only [θ, Draft.dfgwShift, ContinuousMap.coe_comp, ContinuousMap.coe_mk,
      Function.comp_apply, add_comm] using h'
  apply squeeze_zero (g := fun n : ℕ => P.real {η | ∃ k < n, δ * n ≤ B (θ k η) ^ 2})
  · intro n
    exact measureReal_nonneg
  · intro n
    have hsubset : {η | ∃ k < n, ∃ r j, j ≤ 2 ^ r ∧
        δ * n ≤ |(f : Lp ℝ 2 μ) (η ((k : ℝ) + dyadicGridTime 1 r j))| ^ 2} ≤ᵐ[P]
        {η | ∃ k < n, δ * n ≤ B (θ k η) ^ 2} := by
      filter_upwards [hdom] with η hη hhit
      obtain ⟨k, hk, r, j, hj, hval⟩ := hhit
      refine ⟨k, hk, le_trans hval ?_⟩
      exact pow_le_pow_left₀ (abs_nonneg _) (hη k r j hj) 2
    exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsubset)
  · exact htail

end EinsteinFull.External.DFGW
