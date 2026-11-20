import EinsteinFull.External.Draft.DFGWInvarianceV2

/-! # Linear images of Brownian path laws

A deterministic linear transformation of a Brownian path has the corresponding transformed
covariance matrix.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped BigOperators NNReal

namespace EinsteinFull.External.DFGW

variable {d : ℕ}

/-- Apply a matrix to each point of a continuous path. -/
def matrixPath (A : Mat d) (γ : Path d) : Path d :=
  ⟨fun t => A.mulVec (γ t), continuous_const.matrix_mulVec γ.continuous⟩

/-- Applying a matrix to all path values is continuous. -/
theorem continuous_matrixPath (A : Mat d) : Continuous (matrixPath A) := by
  exact ContinuousMap.continuous_postcomp
    ⟨A.mulVec, continuous_const.matrix_mulVec continuous_id⟩

private theorem dot_matrix (A : Mat d) (x y : Vec d) :
    dot x (A.mulVec y) = dot (A.transpose.mulVec x) y := by
  change dotProduct x (A.mulVec y) = dotProduct (A.transpose.mulVec x) y
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- A linear image of a Brownian law is Brownian with covariance `A D Aᵀ`. -/
theorem isBrownianLaw_map_matrixPath {D : Mat d} {W : Measure (Path d)}
    (hW : IsBrownianLaw D W) (A : Mat d) :
    IsBrownianLaw (A * D * A.transpose) (W.map (matrixPath A)) := by
  obtain ⟨hprob, hsymm, hpsd, hstart, hchar⟩ := hW
  let : IsProbabilityMeasure W := hprob
  have hm := (continuous_matrixPath A).measurable
  have hdot (x y : Vec d) : dot x ((A * D * A.transpose).mulVec y) =
      dot (A.transpose.mulVec x) (D.mulVec (A.transpose.mulVec y)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dot_matrix]
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsymm, Matrix.mul_assoc]
  · intro x
    rw [hdot]
    exact hpsd _
  · rw [ae_map_iff hm.aemeasurable
      (measurableSet_eq_fun (continuous_eval_const (0 : ℝ≥0)).measurable measurable_const)]
    filter_upwards [hstart] with γ hγ
    change A.mulVec (γ 0) = 0
    rw [hγ, Matrix.mulVec_zero]
  · intro n t ξ
    have hint : AEStronglyMeasurable (fun γ : Path d =>
        Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k))) : ℂ)))
        (W.map (matrixPath A)) := by
      refine Continuous.aestronglyMeasurable ?_
      refine Complex.continuous_exp.comp (continuous_const.mul ?_)
      refine continuous_finsetSum _ fun k _ => Complex.continuous_ofReal.comp ?_
      unfold dot
      exact continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).comp (continuous_eval_const (t k)))
    rw [integral_map hm.aemeasurable hint]
    change (∫ γ : Path d, Complex.exp (Complex.I *
      ((∑ k, dot (ξ k) (A.mulVec (γ (t k)))) : ℂ)) ∂W) = _
    conv_lhs => simp only [dot_matrix]
    rw [hchar n t (fun k => A.transpose.mulVec (ξ k))]
    simp_rw [hdot]

end EinsteinFull.External.DFGW
