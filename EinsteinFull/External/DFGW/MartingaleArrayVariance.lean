import EinsteinFull.External.DFGW.MartingaleArray
import EinsteinFull.External.DFGW.MartingaleEmpiricalVariance

/-! # Quadratic sums of scaled martingale arrays

The squared row sums of the diffusively normalized martingale array converge in probability to
the projected unit-time variance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Squared sums of the normalized projected increments converge in probability to the
unit-time projected second moment. -/
theorem tendstoInMeasure_scaledProjectedIncrement_sqSum
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN2 : MemLp (N 1) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η)) (e : Vec d) :
    TendstoInMeasure P (fun n η => ∑ k ∈ Finset.range (n + 1),
      scaledProjectedIncrement N e n k η ^ 2) atTop
        (fun _ => ∫ η, dot e (N 1 η) ^ 2 ∂P) := by
  have h := (tendstoInMeasure_empirical_martingale_variance hP hcoord hμ hPfin N hN2 hstat e).comp
    (tendsto_add_atTop_nat 1)
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h
  intro n
  apply ae_of_all P
  intro η
  have hn : 0 ≤ (n + 1 : ℝ) := by positivity
  have heq (k : ℕ) : scaledProjectedIncrement N e n k η ^ 2 =
      (n + 1 : ℝ)⁻¹ * dot e (N ((k : ℝ≥0) + 1) η - N k η) ^ 2 := by
    simp only [scaledProjectedIncrement, mul_pow, inv_pow, Real.sq_sqrt hn]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => (heq k).symm)

end EinsteinFull.External.DFGW
