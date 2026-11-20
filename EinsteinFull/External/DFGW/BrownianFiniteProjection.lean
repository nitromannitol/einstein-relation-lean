import EinsteinFull.External.DFGW.StandardBrownian
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian projections of Brownian paths

Every finite linear combination of Brownian path values has the centered Gaussian law with
its pairwise minimum-time covariance.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal ENNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {d : ℕ} {D : Mat d} {W : Measure (Path d)}

/-- The law of a finite linear combination of Brownian coordinates is Gaussian. -/
theorem isBrownianLaw_map_sum_dot (hW : IsBrownianLaw D W)
    (n : ℕ) (t : Fin n → ℝ≥0) (e : Fin n → Vec d)
    (hv : 0 ≤ ∑ j, ∑ l, (min (t j) (t l) : ℝ) * dot (e j) (D.mulVec (e l))) :
    W.map (fun γ => ∑ j, dot (e j) (γ (t j))) = gaussianReal 0
      (Real.toNNReal (∑ j, ∑ l, (min (t j) (t l) : ℝ) * dot (e j) (D.mulVec (e l)))) := by
  let : IsProbabilityMeasure W := hW.1
  let Z : Path d → ℝ := fun γ => ∑ j, dot (e j) (γ (t j))
  have hZ : Continuous Z := by
    apply continuous_finsetSum
    intro j hj
    unfold dot
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp (continuous_eval_const (t j)))
  let : IsProbabilityMeasure (W.map Z) := (Measure.isProbabilityMeasure_map_iff hZ.measurable.aemeasurable).2 inferInstance
  change W.map Z = _
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_apply_real, integral_map hZ.measurable.aemeasurable (by fun_prop), charFun_gaussianReal]
  have h := hW.2.2.2.2 n t (fun j => u • e j)
  have hphase (γ : Path d) :
      Complex.exp ((u : ℂ) * ((Z γ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((∑ j, dot (u • e j) (γ (t j)) : ℝ) : ℂ)) := by
    have hdot (j : Fin n) : dot (u • e j) (γ (t j)) = u * dot (e j) (γ (t j)) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hsum : (∑ j, dot (u • e j) (γ (t j))) = u * Z γ := by
      simp only [hdot, Z, Finset.mul_sum]
    rw [hsum]
    push_cast
    ring
  simp_rw [hphase, Complex.ofReal_sum]
  rw [h]
  have hdot (v w : Vec d) : dot (u • v) (D.mulVec (u • w)) =
      u ^ 2 * dot v (D.mulVec w) := by
    rw [Matrix.mulVec_smul]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hvar : (∑ j, ∑ l, (min (t j) (t l) : ℝ) * dot (u • e j) (D.mulVec (u • e l))) =
      u ^ 2 * (∑ j, ∑ l, (min (t j) (t l) : ℝ) * dot (e j) (D.mulVec (e l))) := by
    simp only [hdot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hvar]
  have hcoe : ((Real.toNNReal (∑ j, ∑ l, (min (t j) (t l) : ℝ) *
      dot (e j) (D.mulVec (e l))) : ℝ≥0) : ℂ) =
      ((∑ j, ∑ l, (min (t j) (t l) : ℝ) * dot (e j) (D.mulVec (e l))) : ℝ) := by
    exact_mod_cast Real.coe_toNNReal _ hv
  rw [hcoe]
  congr 1
  push_cast
  ring

end EinsteinFull.External.DFGW
