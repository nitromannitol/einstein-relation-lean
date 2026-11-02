import EinsteinRelation.Diffusion.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

/-! # Uniqueness of the actual invariance-principle covariance

Source: `paper/main.tex:82–86`. Bounded continuous cosine tests of the position
at time one recover every covariance quadratic form. Symmetry and polarization
then identify the matrix. This asserts no invariance-principle existence.
-/

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinRelation

private theorem continuous_path_pairing {d : ℕ} (ξ : Vec d) :
    Continuous (fun γ : Path d => dot ξ (γ 1)) := by
  unfold dot
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp (continuous_eval_const (1 : ℝ≥0)))

/-- The bounded cosine test of the position at time one. -/
noncomputable def cosinePathTest {d : ℕ} (ξ : Vec d) :
    BoundedContinuousFunction (Path d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun γ => Real.cos (dot ξ (γ 1)))
    (Real.continuous_cos.comp (continuous_path_pairing ξ)) 1
    (fun γ => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (dot ξ (γ 1)))

/-- The source's Brownian convention fixes its one-time characteristic function. -/
theorem IsBrownianLaw.characteristic_one {d : ℕ} {covariance : Mat d} {W : Measure (Path d)}
    (hW : IsBrownianLaw covariance W) (ξ : Vec d) :
    (∫ γ, Complex.exp (Complex.I * (dot ξ (γ 1) : ℂ)) ∂W) =
      Complex.exp (((-(1 / 2 : ℝ)) * dot ξ (covariance.mulVec ξ)) : ℂ) := by
  simpa only [Fintype.sum_unique, min_self, NNReal.coe_one, one_mul] using
    hW.2.2.2.2 1 (fun _ => 1) (fun _ => ξ)

/-- An actual bounded continuous path test recovers each covariance quadratic form. -/
theorem IsBrownianLaw.integral_cosinePathTest {d : ℕ} {covariance : Mat d}
    {W : Measure (Path d)} (hW : IsBrownianLaw covariance W) (ξ : Vec d) :
    (∫ γ, cosinePathTest ξ γ ∂W) = Real.exp (-(1 / 2 : ℝ) * dot ξ (covariance.mulVec ξ)) := by
  letI : IsProbabilityMeasure W := hW.1
  have hcont : Continuous (fun γ : Path d =>
      Complex.exp (Complex.I * (dot ξ (γ 1) : ℂ))) :=
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_path_pairing ξ)))
  have hint : Integrable (fun γ : Path d =>
      Complex.exp (Complex.I * (dot ξ (γ 1) : ℂ))) W :=
    (integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun γ => by rw [Complex.norm_exp_I_mul_ofReal])
  have hre := integral_re hint
  rw [hW.characteristic_one ξ] at hre
  change (∫ γ, Real.cos (dot ξ (γ 1)) ∂W) = _
  simpa only [RCLike.re_eq_complex_re, mul_comm Complex.I, Complex.exp_ofReal_mul_I_re,
    ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_re] using hre

private theorem matrix_eq_of_quadratic_eq {d : ℕ} {A B : Mat d}
    (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ ξ : Vec d, dot ξ (A.mulVec ξ) = dot ξ (B.mulVec ξ)) : A = B := by
  have he (M : Mat d) (i j : Fin d) :
      dot (unitVector i) (M.mulVec (unitVector j)) = M i j := by
    simp [dot, unitVector, Pi.single_apply]
  have hadd (M : Mat d) (i j : Fin d) :
      dot (unitVector i + unitVector j) (M.mulVec (unitVector i + unitVector j)) =
        M i i + M i j + M j i + M j j := by
    change ((unitVector i + unitVector j) ⬝ᵥ
      M.mulVec (unitVector i + unitVector j)) = _
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    change dot (unitVector i) (M.mulVec (unitVector i)) +
      dot (unitVector i) (M.mulVec (unitVector j)) +
      (dot (unitVector j) (M.mulVec (unitVector i)) +
        dot (unitVector j) (M.mulVec (unitVector j))) = _
    rw [he, he, he, he]
    ring
  have hd (i : Fin d) : A i i = B i i := by
    simpa only [he] using h (unitVector i)
  ext i j
  have hs := h (unitVector i + unitVector j)
  rw [hadd, hadd] at hs
  have hAs : A j i = A i j := congrArg (fun M : Mat d => M i j) hA
  have hBs : B j i = B i j := congrArg (fun M : Mat d => M i j) hB
  linarith only [hs, hd i, hd j, hAs, hBs]

/-- The annealed invariance principle determines a unique symmetric covariance. -/
theorem HasDiffusivity.unique {d : ℕ} {Q : Measure (FieldPair d)}
    {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)} {covariance T : Mat d}
    (hcovariance : HasDiffusivity Q P covariance) (hT : HasDiffusivity Q P T) : covariance = T := by
  obtain ⟨W, hW, hlimW⟩ := hcovariance
  obtain ⟨Z, hZ, hlimZ⟩ := hT
  apply matrix_eq_of_quadratic_eq hW.2.1 hZ.2.1
  intro ξ
  have heq := tendsto_nhds_unique (hlimW (cosinePathTest ξ)) (hlimZ (cosinePathTest ξ))
  rw [hW.integral_cosinePathTest ξ, hZ.integral_cosinePathTest ξ, Real.exp_eq_exp] at heq
  linarith only [heq]

end EinsteinRelation

