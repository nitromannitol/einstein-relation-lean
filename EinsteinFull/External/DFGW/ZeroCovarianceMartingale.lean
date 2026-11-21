import EinsteinFull.External.DFGW.MartingaleMatrixCovariance

/-! # Stationary martingales with zero covariance

A square-integrable stationary-increment martingale whose unit-time covariance is zero vanishes
almost everywhere at every fixed time.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Zero unit-time covariance forces a stationary-increment martingale to vanish at fixed times. -/
theorem stationary_martingale_ae_zero_of_zero_covariance
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (hcov : ∀ e : Vec d, dot e ((0 : Mat d).mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (t : ℝ≥0) : N t =ᵐ[P] 0 := by
  have hmat := secondMomentMatrix_stationary_martingale hP N hN hN2 hstat 0
    (by simp) hcov t
  have hcoord (i : Fin d) : ∀ᵐ η ∂P, N t η i = 0 := by
    have hi : MemLp (fun η => N t η i) 2 P := (hN2 t).eval i
    have hentry := congrFun (congrFun hmat i) i
    have hsq : (∫ η, (N t η i) ^ 2 ∂P) = 0 := by
      simpa only [secondMomentMatrix, Matrix.smul_apply, Matrix.zero_apply, smul_zero,
        ← pow_two] using hentry
    have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all P fun η => sq_nonneg (N t η i))
      hi.integrable_sq).1 hsq
    filter_upwards [hz] with η hη
    exact (sq_eq_zero_iff).1 hη
  filter_upwards [ae_all_iff.mpr hcoord] with η hη
  ext i
  exact hη i

end EinsteinFull.External.DFGW
