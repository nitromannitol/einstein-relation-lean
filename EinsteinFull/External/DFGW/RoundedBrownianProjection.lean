import EinsteinFull.External.DFGW.WeightedPrefixTelescope
import EinsteinFull.External.DFGW.BrownianFiniteProjection
import EinsteinFull.External.DFGW.MartingaleBilinearCovariance

/-! # Brownian limits of rounded martingale projections

Finite linear combinations of rounded martingale values converge to the corresponding
Brownian projections.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Linear combinations of grid-time martingale values converge to the Brownian combination. -/
theorem tendstoInDistribution_sum_rounded_martingale_brownian
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (W : Measure (Path d)) (hW : IsBrownianLaw D W)
    (m : ℕ) (t : Fin m → ℝ≥0) (e : Fin m → Vec d) (ht : ∀ j, t j ≤ 1) :
    letI : IsProbabilityMeasure P := hP.probability
    letI : IsProbabilityMeasure W := hW.1
    TendstoInDistribution (fun (n : ℕ) η => ∑ j, (Real.sqrt (n + 1))⁻¹ *
      dot (e j) (N ⌊(t j : ℝ) * (n + 1 : ℝ)⌋₊ η)) atTop
      (fun γ : Path d => ∑ j, dot (e j) (γ (t j))) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure W := hW.1
  have hr (j : Fin m) (_ : j ∈ Finset.univ) : 0 ≤ (t j : ℝ) ∧ (t j : ℝ) ≤ 1 := by
    exact ⟨(t j).coe_nonneg, by exact_mod_cast ht j⟩
  have hc (e f : Vec d) : (∫ η, dot e (N 1 η) * dot f (N 1 η) ∂P) =
      dot e (D.mulVec f) := integral_dot_stationary_martingale_mul hP N hN hN2 hstat D hD hcov e f
  have hv := prefix_covariance_nonneg hP hcoord hμ hPfin N (hN2 1) hstat
    Finset.univ e (fun j => (t j : ℝ)) hr
  simp only [hc, ← NNReal.coe_min] at hv
  have hmap := isBrownianLaw_map_sum_dot hW m t e hv
  have hseq := tendstoInDistribution_sum_rounded_martingale hP hcoord hμ hPfin
    N hN hN2 hstat Finset.univ e (fun j => (t j : ℝ)) hr
  simp only [hc, ← NNReal.coe_min] at hseq
  have hZ : Continuous (fun γ : Path d => ∑ j, dot (e j) (γ (t j))) := by
    apply continuous_finsetSum
    intro j hj
    unfold dot
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp (continuous_eval_const (t j)))
  refine ⟨hseq.forall_aemeasurable, hZ.measurable.aemeasurable, ?_⟩
  simpa only [hmap, Measure.map_id, ← NNReal.coe_min] using hseq.tendsto

end EinsteinFull.External.DFGW
