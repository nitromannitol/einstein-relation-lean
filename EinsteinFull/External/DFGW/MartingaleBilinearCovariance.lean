import EinsteinFull.External.DFGW.MartingaleMatrixCovariance

/-! # Bilinear covariance of a vector martingale

The matrix of unit-time second moments represents all cross-products of scalar projections.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The bilinear form of a second-moment matrix is the projected cross-moment. -/
theorem secondMomentMatrix_bilinear (P : Measure Ω) (Z : Ω → Vec d) (hZ : MemLp Z 2 P)
    (e f : Vec d) : dot e ((secondMomentMatrix P Z).mulVec f) =
      ∫ ω, dot e (Z ω) * dot f (Z ω) ∂P := by
  have hint (i j : Fin d) : Integrable (fun ω => (e i * f j) * (Z ω i * Z ω j)) P :=
    (integrable_secondMoment_entry P Z hZ i j).const_mul _
  calc
    dot e ((secondMomentMatrix P Z).mulVec f) =
        ∑ i, ∑ j, (e i * f j) * ∫ ω, Z ω i * Z ω j ∂P := by
      simp only [dot, Matrix.mulVec, dotProduct, secondMomentMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, ∫ ω, (e i * f j) * (Z ω i * Z ω j) ∂P := by
      simp only [integral_const_mul]
    _ = ∫ ω, ∑ i, ∑ j, (e i * f j) * (Z ω i * Z ω j) ∂P := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact hint i j
      · intro i hi
        apply integrable_finsetSum
        intro j hj
        exact hint i j
    _ = ∫ ω, dot e (Z ω) * dot f (Z ω) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      simp only [dot]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The unit-time cross-moment equals the bilinear form of the martingale covariance. -/
theorem integral_dot_stationary_martingale_mul
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (e f : Vec d) : (∫ η, dot e (N 1 η) * dot f (N 1 η) ∂P) = dot e (D.mulVec f) := by
  have hmat := secondMomentMatrix_stationary_martingale hP N hN hN2 hstat D hD hcov 1
  simp only [NNReal.coe_one, one_smul] at hmat
  rw [← hmat, secondMomentMatrix_bilinear P (N 1) (hN2 1)]

end EinsteinFull.External.DFGW
