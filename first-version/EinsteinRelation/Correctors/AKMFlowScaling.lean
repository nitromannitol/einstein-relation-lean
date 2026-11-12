import EinsteinRelation.Correctors.AKMCorrectorScaling

/-! # Rescaling the supplied parabolic flow

Source: `paper/main.tex:789–816`. Normalizing a coefficient column for the
bounded initial-field hypothesis of AKM does not change the equation:
rescaling the actual scalar flow and its actual gradient rescales the
initial flux. No uniqueness of whole-space weak solutions is used.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Positive scalar multiplication preserves the actual parabolic energy
class and its distributional equation. Source: `paper/main.tex:789–810`. -/
theorem parabolicSolution_const_mul {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsParabolicSolution A I U u G) {c : ℝ} (hc : 0 ≤ c) :
    IsParabolicSolution A I U (fun z => c * u z) (fun z => c • G z) := by
  refine ⟨h.1.const_mul c, h.2.1.const_smul c, ?_, ?_, ?_⟩
  · simpa only [euclideanNorm_smul c hc] using h.2.2.1.const_mul c
  · filter_upwards [h.2.2.2.1] with t ht
    exact hasWeakGradient_const_mul ht c
  · intro ψ hψ hψc hψU
    have hsplit (z : ℝ × Vec d) :
        -(c * u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (c • G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j)) =
        c * (-(u z) * fderiv ℝ ψ z (1, 0) +
          dot ((A z.2).mulVec (G z))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
      simp only [Matrix.mulVec_smul, dot, Pi.smul_apply, smul_eq_mul,
        mul_add, Finset.mul_sum, mul_assoc]
      ring
    simp_rw [hsplit]
    rw [integral_const_mul, h.2.2.2.2 ψ hψ hψc hψU, mul_zero]

/-- Rescaling the same supplied flow preserves continuity, all positive
cylinder equations, and the actual distributional initial trace.
Source: `paper/main.tex:789–816`. -/
theorem semigroupSolution_const_mul {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsSemigroupSolution A g u G) {c : ℝ} (hc : 0 ≤ c) :
    IsSemigroupSolution A (fun x => c • g x)
      (fun z => c * u z) (fun z => c • G z) := by
  refine ⟨continuousOn_const.mul h.1, ?_, ?_⟩
  · intro a b R ha hab hR
    exact parabolicSolution_const_mul (h.2.1 a b R ha hab hR) hc
  · intro ψ hψ
    have hlim := (h.2.2 ψ hψ).const_mul c
    have hdot (x : Vec d) : dot (c • g x) (gradient ψ x) =
        c * dot (g x) (gradient ψ x) := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    simpa only [hdot, mul_assoc, integral_const_mul, mul_neg] using hlim

end EinsteinRelation.Correctors
