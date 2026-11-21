import EinsteinFull.External.DFGW.DiffusionMatrix
import EinsteinFull.External.DFGW.IncrementVarianceLimit
import EinsteinFull.External.DFGW.ProjectedCorrelationMatrix
import EinsteinFull.External.DFGW.MatrixQuadratic

/-! # Diffusion matrix and long-time variance

The diffusion matrix is nonnegative definite and is the limit of normalized increment
second moments.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The diffusion matrix has the covariance formula, is nonnegative definite, and gives the
long-time projected variance. -/
theorem exists_diffusion_matrix_variance_limit
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
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ)
          (Set.Ioi 0) ∧
        D i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ) ∧
      (∀ e : Vec d, Tendsto (fun t : ℝ => t⁻¹ * ∫ η : C(ℝ, S),
        dot e (X 0 t η) ^ 2 ∂P) atTop (𝓝 (dot e (D.mulVec e)))) ∧
      ∀ e : Vec d, 0 ≤ dot e (D.mulVec e) := by
  obtain ⟨C, D, hC, hD, hCquad, hentries⟩ :=
    exists_symmetric_diffusion_matrix hP hX φ hφ hlim hL2 hM
  let K : Mat d := fun i j => ∫ t in Set.Ioi (0 : ℝ),
    ∫ x, φ x i * ∫ y, φ y j ∂T t.toNNReal x ∂μ
  have hDformula : D = fun i j => C i j - 2 * K i j := by
    funext i j
    exact (hentries i j).2
  have hlimit (e : Vec d) : Tendsto (fun t : ℝ => t⁻¹ * ∫ η : C(ℝ, S),
      dot e (X 0 t η) ^ 2 ∂P) atTop (𝓝 (dot e (D.mulVec e))) := by
    have hg : MemLp (fun x => dot e (φ x)) 2 μ := by
      unfold dot
      apply memLp_finsetSum
      intro i hi
      exact (hφ.eval i).const_mul (e i)
    have hcor := integral_projected_velocity_autocorrelation_eq_sum hP hX φ hφ hlim hL2 hM e hg
    have heD : dot e (D.mulVec e) =
        dot e ((secondMomentMatrix P (compensated X φ 1)).mulVec e) -
          2 * ∫ t in Set.Ioi (0 : ℝ), inner ℝ (hg.toLp (fun x => dot e (φ x)))
            (transitionOperator hP t.toNNReal (hg.toLp (fun x => dot e (φ x)))) := by
      rw [hDformula, dot_matrix_sub_two_mul, hcor, hCquad,
        secondMomentMatrix_quadratic P _ (hL2 1) e]
    rw [heD]
    exact tendsto_normalized_dot_increment_sq hP hX φ hφ hlim hL2 hM e hg
  refine ⟨C, D, hC, hD, hCquad, hentries, hlimit, ?_⟩
  intro e
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := (0 : ℝ))) (hlimit e)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact mul_nonneg (inv_nonneg.mpr ht.le) (integral_nonneg fun _ => sq_nonneg _)

end EinsteinFull.External.DFGW
