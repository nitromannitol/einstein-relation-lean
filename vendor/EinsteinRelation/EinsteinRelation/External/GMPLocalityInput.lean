import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Environment.Basic
import EinsteinRelation.External.GantertSection7Support

/-! # Cited locality input for the GMP Section 7 realizations

A Prop-valued statement draft for the cited input of `paper/main.tex` 375-381 (Step 2 of the
proof of Lemma 3.1). It concerns the fixed-environment realizations
`GantertFixedEnvironmentRealization` of the GMP Section 7 heat-kernel construction, and it is the
only declaration of this module. The module contains no theorem and no data.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace EinsteinRelation.External

/-- Locality of the fixed-environment realizations, stopped at the exit time from an open set.

Let `ω` and `ω'` be regular environments that have equal coefficients and potentials at every
point of an open set `U`. Let `r` and `r'` be fixed-environment realizations of `ω` and `ω'` at the
same force `lam ∈ [0, 1]`. Then for every starting point `x ∈ U`, the path laws of `r` and `r'`
from `x` agree after stopping at the first exit from `U`. The stopping map is characterized
pointwise: `stop γ t = γ (min t τ_U(γ))`, where `τ_U(γ) = inf {s | γ s ∉ U}`, and the infimum over
the empty set is `∞`. Measurability of `stop` is part of the conclusion, since `Measure.map` of a
non-measurable map is zero and would make the equality vacuous.

Source: Gantert, Mathieu and Piatnitski (2012), Comm. Pure Appl. Math. 65, proof of Proposition 7.2
(pp. 34-35). There, on the ball `G_n` with exit time `ζ_n`, the parts of the two Dirichlet forms
coincide when the coefficients agree on `G_n`, so the processes agree up to `ζ_n`. The paper states
this for balls; the statement here is for an arbitrary open `U`, which covers the balls
`U^x = B_{6R}(x + 5Re₁)` of `paper/main.tex` 268 used in Step 2. The killed kernel `p_{ω,U}`
that enters the same argument is in Shen (2003), Theorem 2.1, formulas (2.8)-(2.9), and Shen
(2004), addendum, p. 386. -/
def GMPKernelLocality : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (U : Set (Vec d)),
    IsOpen U →
    ∀ (ω ω' : FieldPair d) (hω : IsRegular Λ₀ ω) (hω' : IsRegular Λ₀ ω') (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1),
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
      ∀ (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd Λ₀ hΛ₀ ω hω lam h0 h1)
        (r' : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd Λ₀ hΛ₀ ω' hω' lam h0 h1)
        (x : Vec d), x ∈ U →
        ∀ stop : Path d → ℝ≥0 → Vec d,
          (∀ (γ : Path d) (t : ℝ≥0), stop γ t =
            γ ((min (t : ℝ≥0∞) (⨅ (s : ℝ≥0) (_ : γ s ∉ U), (s : ℝ≥0∞))).toNNReal)) →
          Measurable stop ∧ Measure.map stop (r.pathLaw x) = Measure.map stop (r'.pathLaw x)

end EinsteinRelation.External
