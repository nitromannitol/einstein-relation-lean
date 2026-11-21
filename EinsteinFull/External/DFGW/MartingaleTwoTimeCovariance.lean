import EinsteinFull.External.DFGW.MartingaleCrossCovariance

/-! # Brownian covariance at two times

A stationary-increment square-integrable martingale has the two-time covariance associated with
its unit-time covariance matrix.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The two-time coordinate covariance of a stationary-increment martingale is `min(s,t) D`. -/
theorem integral_stationary_martingale_two_time_covariance
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (s t : ℝ≥0) (i j : Fin d) :
    (∫ η, N s η i * N t η j ∂P) = (min s t : ℝ≥0) * D i j := by
  let : IsProbabilityMeasure P := hP.probability
  have hM (k : Fin d) : Martingale (fun u η => N u η k) Draft.dfgwPast P := by
    simpa only [ContinuousLinearMap.proj_apply] using
      martingale_continuousLinearMap hN (ContinuousLinearMap.proj k)
  have h2 (u : ℝ≥0) (k : Fin d) : MemLp (fun η => N u η k) 2 P := (hN2 u).eval k
  have hsame (u : ℝ≥0) (k l : Fin d) :
      (∫ η, N u η k * N u η l ∂P) = (u : ℝ) * D k l := by
    have hmat := secondMomentMatrix_stationary_martingale hP N hN hN2 hstat D hD hcov u
    have hentry := congrFun (congrFun hmat k) l
    simpa only [secondMomentMatrix, Matrix.smul_apply, smul_eq_mul] using hentry
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact (integral_martingale_mul_later _ _ (hM i) (hM j) hst (h2 s i) (h2 s j)
      (h2 t j)).trans (hsame s i j)
  · rw [min_eq_right hts]
    have hsym : D j i = D i j := congrFun (congrFun hD i) j
    calc
      (∫ η, N s η i * N t η j ∂P) = ∫ η, N t η j * N s η i ∂P := by
        congr 1
        funext η
        ring
      _ = ∫ η, N t η j * N t η i ∂P :=
        integral_martingale_mul_later _ _ (hM j) (hM i) hts (h2 t j) (h2 t i) (h2 s i)
      _ = (t : ℝ) * D i j := by rw [hsame, hsym]

end EinsteinFull.External.DFGW
