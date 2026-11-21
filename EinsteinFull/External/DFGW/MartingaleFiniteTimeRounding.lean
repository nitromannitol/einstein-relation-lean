import EinsteinFull.External.DFGW.MartingaleTimeRoundingAt
import EinsteinFull.External.DFGW.FiniteDimensionalMeasure

/-! # Rounding finitely many martingale times

Rounding any finite collection of diffusively scaled martingale observation times is negligible
in probability jointly over all coordinates and times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Rounding finitely many diffusively scaled martingale times changes the joint vector by
an amount vanishing in probability. -/
theorem tendstoInMeasure_martingale_finite_rounding
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    {J : Type*} [Fintype J] (times : J → ℝ≥0) :
    TendstoInMeasure P (fun (ε : ℝ) η j => ε •
      (N ((ε⁻¹ ^ 2).toNNReal * times j) η -
        N (floorTime ((ε⁻¹ ^ 2).toNNReal * times j)) η))
      (𝓝[>] 0) (fun _ => 0) := by
  let : IsProbabilityMeasure P := hP.probability
  apply tendstoInMeasure_pi_zero
  intro j
  apply tendstoInMeasure_pi_zero
  intro i
  have h := tendstoInMeasure_martingale_rounding_at hP N hN hN2 hstat (unitVector i) (times j)
  simpa only [dot, unitVector, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h

end EinsteinFull.External.DFGW
