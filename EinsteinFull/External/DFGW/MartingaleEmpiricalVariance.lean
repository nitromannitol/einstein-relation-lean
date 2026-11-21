import EinsteinFull.External.DFGW.TrajectoryEmpiricalAverage
import EinsteinFull.External.DFGW.MartingaleMaximalSecondMoment

/-! # Empirical quadratic variation of stationary martingale increments

The normalized sum of squared projected unit increments converges in probability to the
projected unit second moment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The empirical second moment of stationary unit martingale increments converges in probability
without any fourth-moment assumption. -/
theorem tendstoInMeasure_empirical_martingale_variance
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) :
    TendstoInMeasure P (fun (n : ℕ) η => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      dot e (N ((k : ℝ≥0) + 1) η - N k η) ^ 2) atTop
        (fun _ => ∫ η, dot e (N 1 η) ^ 2 ∂P) := by
  let : IsProbabilityMeasure P := hP.probability
  let L : Vec d →L[ℝ] ℝ := ∑ i : Fin d, (e i) • ContinuousLinearMap.proj i
  have hL (v : Vec d) : L v = dot e v := by
    simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, dot]
  have hF : Integrable (fun η => dot e (N 1 η) ^ 2) P := by
    have h := (hN2.continuousLinearMap_comp L).integrable_sq
    simpa only [hL] using h
  have h := tendstoInMeasure_shift_empiricalAverage hP hcoord hμ hPfin
    (t := 1) (by norm_num) (fun η => dot e (N 1 η) ^ 2) hF
  have hstatall : ∀ᵐ η ∂P, ∀ k : ℕ,
      N ((k : ℝ≥0) + 1) η - N k η = N 1 (Draft.dfgwShift (k : ℝ) η) :=
    ae_all_iff.mpr (fun k => by
      filter_upwards [hstat (k : ℝ≥0) 1] with η hη
      simpa only [NNReal.coe_natCast] using hη)
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
  intro n
  filter_upwards [hstatall] with η hη
  simp only [nsmul_eq_mul, mul_one, NNReal.coe_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hη k]

end EinsteinFull.External.DFGW
