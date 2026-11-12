import EinsteinRelation.Correctors.AKMFlowScaling
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Scalar initial data may have either sign when kernel solutions are
averaged. Source: `paper/main.tex:787–792,850`. -/
theorem parabolicSolution_signed_const_mul {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsParabolicSolution A I U u G) (c : ℝ) :
    IsParabolicSolution A I U (fun z => c * u z) (fun z => c • G z) := by
  refine ⟨h.1.const_mul c, h.2.1.const_smul c, ?_, ?_, ?_⟩
  · -- MemLp (euclideanNorm (c • G z)) 2
    have hnorm : (fun z => euclideanNorm (c • G z)) =
        (fun z => |c| * euclideanNorm (G z)) := by
      ext z; rw [TimeChange.euclideanNorm_smul]
    rw [hnorm]
    exact h.2.2.1.const_mul |c|
  · -- HasWeakGradient condition
    filter_upwards [h.2.2.2.1] with t ht
    exact hasWeakGradient_const_mul ht c
  · -- Weak formulation
    intro ψ hψ hψc hψU
    have hsplit (z : ℝ × Vec d) :
        -(c * u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (c • G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j)) =
        c * (-(u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
      calc
        -(c * u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (c • G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))
            = -(c * u z) * fderiv ℝ ψ z (1, 0) +
              dot (c • ((A z.2).mulVec (G z)))
                (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
          simp [Matrix.mulVec_smul]
        _ = -(c * u z) * fderiv ℝ ψ z (1, 0) +
              (c * dot ((A z.2).mulVec (G z))
                (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
          simp [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
        _ = c * (-(u z) * fderiv ℝ ψ z (1, 0)) +
              c * dot ((A z.2).mulVec (G z))
                (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
          ring
        _ = c * (-(u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
          ring
    simp_rw [hsplit]
    rw [integral_const_mul, h.2.2.2.2 ψ hψ hψc hψU, mul_zero]

end EinsteinRelation.Correctors
