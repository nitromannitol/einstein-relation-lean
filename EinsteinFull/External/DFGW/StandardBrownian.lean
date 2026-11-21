import EinsteinFull.External.DFGW.IndependentBrownianPaths
import EinsteinFull.External.DFGW.BrownianCovariance

/-! # Brownian laws of arbitrary covariance

Independent real Brownian coordinates provide the identity-covariance path law; a matrix square
root then gives every positive semidefinite covariance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation MarkovProcess
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

/-- Independent standard real Brownian paths form an identity-covariance Brownian law. -/
theorem isBrownianLaw_independentBrownianPaths (d : ℕ) :
    IsBrownianLaw (1 : Mat d) (independentBrownianPaths d) := by
  refine ⟨inferInstance, by simp, ?_, ?_, ?_⟩
  · intro x
    simp only [Matrix.one_mulVec, dot]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  · unfold independentBrownianPaths
    rw [ae_map_iff (continuous_coordinatePaths d).measurable.aemeasurable
      (measurableSet_eq_fun (continuous_eval_const (0 : ℝ≥0)).measurable measurable_const)]
    have hzero (i : Fin d) : ∀ᵐ γ ∂(Measure.pi (fun _ : Fin d => brownianMotion 0)),
        γ i 0 = 0 :=
      (measurePreserving_eval (fun _ : Fin d => brownianMotion 0) i).quasiMeasurePreserving.ae
        isPreBrownianReal_heatProcess.eval_zero_ae_eq_zero
    filter_upwards [ae_all_iff.mpr hzero] with γ hγ
    ext i
    exact hγ i
  · intro n t ξ
    unfold independentBrownianPaths
    have hint : AEStronglyMeasurable (fun γ : Path d =>
        Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k))) : ℂ)))
        ((Measure.pi (fun _ : Fin d => brownianMotion 0)).map coordinatePaths) := by
      refine Continuous.aestronglyMeasurable ?_
      refine Complex.continuous_exp.comp (continuous_const.mul ?_)
      refine continuous_finsetSum _ fun k _ => Complex.continuous_ofReal.comp ?_
      unfold dot
      exact continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).comp (continuous_eval_const (t k)))
    rw [integral_map (continuous_coordinatePaths d).measurable.aemeasurable hint]
    have hprod (γ : Fin d → ContinuousPath ℝ) :
        Complex.exp (Complex.I * ((∑ k, dot (ξ k) ((coordinatePaths γ) (t k))) : ℂ)) =
        ∏ i, Complex.exp (Complex.I * ((∑ k, ξ k i * γ i (t k)) : ℂ)) := by
      rw [← Complex.exp_sum]
      congr 1
      simp only [dot, coordinatePaths, ContinuousMap.pi_eval, Complex.ofReal_sum,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [Complex.ofReal_mul]
    simp_rw [hprod]
    change (∫ γ : Fin d → ContinuousPath ℝ, ∏ i,
      (fun p : ContinuousPath ℝ => Complex.exp
        (Complex.I * ((∑ k, ξ k i * p (t k)) : ℂ))) (γ i)
      ∂(Measure.pi (fun _ : Fin d => brownianMotion 0))) = _
    rw [integral_fintype_prod_eq_prod (fun i (p : ContinuousPath ℝ) =>
      Complex.exp (Complex.I * ((∑ k, ξ k i * p (t k)) : ℂ)))]
    simp_rw [isPreBrownianReal_integral_exp_sum isPreBrownianReal_heatProcess]
    rw [← Complex.exp_sum]
    congr 1
    simp only [Matrix.one_mulVec, dot, Complex.ofReal_mul, Complex.ofReal_sum,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Every symmetric positive semidefinite matrix is the covariance of a Brownian path law. -/
theorem exists_brownianLaw (d : ℕ) (D : Mat d) (hsymm : D.transpose = D)
    (hpsd : ∀ x : Vec d, 0 ≤ dot x (D.mulVec x)) :
    ∃ W : Measure (Path d), IsBrownianLaw D W :=
  exists_brownianLaw_of_identity (isBrownianLaw_independentBrownianPaths d) D hsymm hpsd

end EinsteinFull.External.DFGW
