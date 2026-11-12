import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:808–816`. The literal origin flux represents the
actual affine L² coefficient action, for an arbitrary L² gradient field. -/
theorem ae_origin_correctorFluxOfGradient {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (correctorFluxOfGradient Q i G ω).ofLp =
        (ω.1 0).mulVec (correctorUnitVector i + G ω).ofLp := by
  have h := reducedOriginCoefficientAction_coeFn Q (correctorAffineField Q i + G)
  filter_upwards [h, Lp.coeFn_add (correctorAffineField Q i) G,
    Lp.coeFn_const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)] with ω hω hsum hconst
  rw [show correctorFluxOfGradient Q i G =
    reducedOriginCoefficientAction Q (correctorAffineField Q i + G) from rfl]
  rw [hω]
  dsimp [correctorAffineField] at hsum hconst ⊢
  rw [hsum, hconst]
  rfl

end EinsteinRelation.Correctors
