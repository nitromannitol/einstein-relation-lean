import EinsteinFull.External.DFGW.MartingaleArray
import EinsteinFull.External.DFGW.TrajectoryEmpiricalAverage

/-! # Cross-variation of scaled martingale arrays

The empirical cross-variation of two projections of stationary increments converges to their
unit-time covariance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Empirical cross-variation of two projected increment arrays converges to their unit-time
covariance in probability. -/
theorem tendstoInMeasure_scaledProjectedIncrement_crossSum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e f : Vec d) :
    TendstoInMeasure P (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledProjectedIncrement N e n k η * scaledProjectedIncrement N f n k η) atTop
        (fun _ => ∫ η, dot e (N 1 η) * dot f (N 1 η) ∂P) := by
  let : IsProbabilityMeasure P := hP.probability
  let L (v : Vec d) : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (v i) • ContinuousLinearMap.proj i
  have hL (v w : Vec d) : L v w = dot v w := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have he : MemLp (fun η => dot e (N 1 η)) 2 P := by
    simpa only [hL] using hN2.continuousLinearMap_comp (L e)
  have hf : MemLp (fun η => dot f (N 1 η)) 2 P := by
    simpa only [hL] using hN2.continuousLinearMap_comp (L f)
  have hint : Integrable (fun η => dot e (N 1 η) * dot f (N 1 η)) P := he.integrable_mul hf
  have h := (tendstoInMeasure_shift_empiricalAverage hP hcoord hμ hPfin
    (t := 1) (by norm_num) (fun η => dot e (N 1 η) * dot f (N 1 η)) hint).comp
      (tendsto_add_atTop_nat 1)
  have hstatall : ∀ᵐ η ∂P, ∀ k : ℕ,
      N ((k : ℝ≥0) + 1) η - N k η = N 1 (Draft.dfgwShift (k : ℝ) η) :=
    ae_all_iff.mpr (fun k => by
      filter_upwards [hstat (k : ℝ≥0) 1] with η hη
      simpa only [NNReal.coe_natCast] using hη)
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
  intro n
  filter_upwards [hstatall] with η hη
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, nsmul_eq_mul, mul_one,
    NNReal.coe_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hsqrt : (Real.sqrt (n + 1)) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by positivity)
  simp only [scaledProjectedIncrement, hη k]
  have hnorm : (Real.sqrt (n + 1))⁻¹ * (Real.sqrt (n + 1))⁻¹ = (n + 1 : ℝ)⁻¹ := by
    rw [← pow_two, inv_pow, hsqrt]
  rw [← hnorm]
  ring

end EinsteinFull.External.DFGW
