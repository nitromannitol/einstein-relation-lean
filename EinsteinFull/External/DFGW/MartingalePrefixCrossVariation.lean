import EinsteinFull.External.DFGW.MartingaleArrayCrossVariation
import EinsteinFull.External.DFGW.TrajectoryPrefixAverage

/-! # Prefix cross-variation of martingale increments

Normalized cross-products of projected unit martingale increments converge over deterministic
prefixes to the prefix fraction times the unit covariance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Normalized cross-variation over a growing prefix converges to its time fraction times
unit-time covariance. -/
theorem tendstoInMeasure_scaledProjectedIncrement_prefixCrossSum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e f : Vec d)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (r : ℝ)
    (hr : Tendsto (fun n : ℕ => (m n : ℝ) / (n + 1)) atTop (𝓝 r)) :
    TendstoInMeasure P (fun n η => ∑ k ∈ Finset.range (m n),
      scaledProjectedIncrement N e n k η * scaledProjectedIncrement N f n k η) atTop
      (fun _ => r * ∫ η, dot e (N 1 η) * dot f (N 1 η) ∂P) := by
  let : IsProbabilityMeasure P := hP.probability
  let L (v : Vec d) : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (v i) • ContinuousLinearMap.proj i
  have hL (v w : Vec d) : L v w = dot v w := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have he : MemLp (fun η => dot e (N 1 η)) 2 P := by
    simpa only [hL] using hN2.continuousLinearMap_comp (L e)
  have hf : MemLp (fun η => dot f (N 1 η)) 2 P := by
    simpa only [hL] using hN2.continuousLinearMap_comp (L f)
  have hint : Integrable (fun η => dot e (N 1 η) * dot f (N 1 η)) P := he.integrable_mul hf
  have h := tendstoInMeasure_shift_prefixAverage hP hcoord hμ hPfin
    (t := 1) (by norm_num) (fun η => dot e (N 1 η) * dot f (N 1 η)) hint m hm r hr
  have hstatall : ∀ᵐ η ∂P, ∀ k : ℕ,
      N ((k : ℝ≥0) + 1) η - N k η = N 1 (Draft.dfgwShift (k : ℝ) η) :=
    ae_all_iff.mpr (fun k => by
      filter_upwards [hstat (k : ℝ≥0) 1] with η hη
      simpa only [NNReal.coe_natCast] using hη)
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
  intro n
  filter_upwards [hstatall] with η hη
  simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul, mul_one, NNReal.coe_natCast]
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
