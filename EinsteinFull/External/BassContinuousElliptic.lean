import EinsteinFull.Calculus.C8BassFiltrationCompletion

/-!
# Bass continuous elliptic martingale-problem well-posedness

Exact source input: Bass, Diffusions and Elliptic Operators (1997), VI.4.3,
with VI.1 coefficient assumptions and V.1 completed canonical conventions.
Its application to the physical operator, to measurable families of environments
and to the weighted H¹ form is proved in this repository.
-/

open EinsteinRelation MeasureTheory

namespace EinsteinFull.External

/-- Bass VI.4.3: continuous symmetric uniformly elliptic diffusion coefficients
and bounded measurable drift give a unique completed canonical martingale-
problem law from every starting point, with the literal source quantifiers. -/
axiom bass_continuous_elliptic_well_posed (d : ℕ) (hd : 1 ≤ d) (Λ₁ Λ₂ : ℝ) (hΛ₁ : 0 < Λ₁) (hΛ₂ : 0 < Λ₂) (a : Vec d → Mat d) (b : Vec d → Vec d) (ha : Measurable a) (hb : Measurable b) (hsym : ∀ x, (a x).transpose = a x) (hell : ∀ x ξ, Λ₁ * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ) ∧ dot ξ ((a x).mulVec ξ) ≤ Λ₁⁻¹ * euclideanSq ξ) (hbound : ∀ x i, |b x i| ≤ Λ₂) (hcont : Continuous a) : ∀ x : Vec d, ∃! P : Measure (Bass.Path d), Bass.Completion.SolvesMartingaleProblem a b x P

end EinsteinFull.External
