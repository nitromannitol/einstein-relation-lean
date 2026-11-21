import EinsteinFull.External.DFGW.MartingalePrefixCrossVariation
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Cross-variation at scaled times

The empirical cross-variation up to a fixed positive scaled time converges to that time
multiplied by the unit covariance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Cross-variation up to a fixed positive scaled time converges to the corresponding
covariance. -/
theorem tendstoInMeasure_scaledProjectedIncrement_floorCrossSum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e f : Vec d) (r : ℝ) (hr : 0 < r) :
    TendstoInMeasure P (fun (n : ℕ) η => ∑ k ∈ Finset.range ⌊r * (n + 1 : ℝ)⌋₊,
      scaledProjectedIncrement N e n k η * scaledProjectedIncrement N f n k η) atTop
      (fun _ => r * ∫ η, dot e (N 1 η) * dot f (N 1 η) ∂P) := by
  let m : ℕ → ℕ := fun n => ⌊r * (n + 1 : ℝ)⌋₊
  have hm : Tendsto m atTop atTop := by
    simpa only [m, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_nat_floor_mul_atTop r hr).comp (tendsto_add_atTop_nat 1)
  have hdenom : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ => (m n : ℝ) / (n + 1)) atTop (𝓝 r) := by
    exact (tendsto_nat_floor_mul_div_atTop hr.le).comp hdenom
  exact tendstoInMeasure_scaledProjectedIncrement_prefixCrossSum hP hcoord hμ hPfin
    N hN2 hstat e f m hm r hratio

end EinsteinFull.External.DFGW
