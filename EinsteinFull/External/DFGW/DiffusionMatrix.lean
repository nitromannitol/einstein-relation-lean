import EinsteinFull.External.DFGW.VelocityCorrelation
import EinsteinFull.External.DFGW.MartingaleCovariance

/-! # The diffusion matrix formula

The martingale second moments and integrated velocity correlations define symmetric matrices
with the entries appearing in the diffusion formula.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The second-moment and diffusion matrices satisfy the covariance formula, with all integrals
absolutely convergent. -/
theorem exists_symmetric_diffusion_matrix
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (hL2 : ∀ t, MemLp (compensated X φ t) 2 P)
    (hM : Martingale (compensated X φ) Draft.dfgwPast P) :
    ∃ C D : Mat d,
      C.transpose = C ∧ D.transpose = D ∧
      (∀ e : Vec d, dot e (C.mulVec e) = ∫ η, dot e (compensated X φ 1 η) ^ 2 ∂P) ∧
      ∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
          (Set.Ioi 0) ∧
        D i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ := by
  let C := secondMomentMatrix P (compensated X φ 1)
  let D : Mat d := fun i j => C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
    ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ
  refine ⟨C, D, secondMomentMatrix_transpose P _, ?_, ?_, ?_⟩
  · ext i j
    change C j i - 2 * (∫ t in Set.Ioi (0 : ℝ),
      ∫ x, φ x j * ∫ y, φ y i ∂T t.toNNReal x ∂μ) =
      C i j - 2 * (∫ t in Set.Ioi (0 : ℝ),
        ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
    have hC : C j i = C i j := by
      exact congrFun (congrFun (secondMomentMatrix_transpose P (compensated X φ 1)) i) j
    rw [hC]
    congr 2
    apply integral_congr_ae
    filter_upwards with t
    exact integral_mul_kernel_comm hP t.toNNReal _ _ (hφ.eval j) (hφ.eval i)
  · exact secondMomentMatrix_quadratic P _ (hL2 1)
  · intro i j
    exact ⟨integrableOn_velocity_kernel_correlation hP hX φ hφ hlim hL2 hM i j, rfl⟩

end EinsteinFull.External.DFGW
