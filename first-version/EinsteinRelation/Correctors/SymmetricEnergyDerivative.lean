import Mathlib.Analysis.Calculus.Deriv.Mul

namespace EinsteinRelation.Correctors

/-- Differentiate the actual symmetric energy form along an L² curve.
Source: `paper/main.tex:798–806`; time-slice energy estimate. -/
theorem hasDerivAt_symmetric_bilinear_energy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    {f : ℝ → E} {f' : E} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => B (f s) (f s)) (2 * B (f t) f') t := by
  have h := B.hasDerivAt_of_bilinear hf hf
  have hderiv : B (f t) f' + B f' (f t) = 2 * B (f t) f' := by
    rw [hsymm (f t) f', two_mul]
  rw [hderiv] at h
  exact h

end EinsteinRelation.Correctors
