import EinsteinFull.External.DFGW.VectorStationaryMartingaleVariance
import EinsteinFull.External.DFGW.QuadraticMatrix

/-! # Matrix covariance of a stationary-increment martingale

The unit-time covariance matrix determines the covariance matrix of a stationary-increment
vector martingale at every time.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The second-moment matrix of a stationary-increment martingale equals time times its
unit-time covariance matrix. -/
theorem secondMomentMatrix_stationary_martingale (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (t : ℝ≥0) : secondMomentMatrix P (N t) = (t : ℝ) • D := by
  apply symmetric_matrix_eq_of_quadratic
  · exact secondMomentMatrix_transpose P _
  · rw [Matrix.transpose_smul, hD]
  · intro e
    rw [secondMomentMatrix_quadratic P _ (hN2 t),
      integral_dot_stationary_martingale_sq hP N hN hN2 hstat e t, ← hcov e,
      Matrix.smul_mulVec]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

end EinsteinFull.External.DFGW
