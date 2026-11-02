import EinsteinRelation.Sharpness.HarmonicField

/-! # The actual physical coefficient pair and its reduced generator

`paper/main.tex`, `eq.sharp-coefficients` (1225–1231) and `eq.sharp-generator`
(1247–1250). Continuity proofs only certify membership in the existing carrier;
no probabilistic law, velocity, or clock conclusion is stored in the pair.
-/

namespace EinsteinRelation.Sharpness

/-- The literal pair `(μ⁻¹ a, -(1/2) log μ)` as a physical environment. -/
noncomputable def physicalEnvironment {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (ha : Continuous (physicalCoefficientField i δ ψ))
    (hV : Continuous (potentialField i δ ψ)) : FieldPair d :=
  (⟨physicalCoefficientField i δ ψ, ha⟩, ⟨potentialField i δ ψ, hV⟩)

/-- The physical environment's clock is the constructed divergence density. -/
theorem physicalEnvironment_clockDensity {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (ha : Continuous (physicalCoefficientField i δ ψ))
    (hV : Continuous (potentialField i δ ψ)) (x : Vec d)
    (hμ : 0 < densityField i δ ψ x) :
    clockDensity (physicalEnvironment i δ ψ ha hV) x = densityField i δ ψ x :=
  exp_neg_two_potentialField i δ ψ x hμ

/-- Reduction of the physical environment recovers the constructed coefficient. -/
theorem physicalEnvironment_reducedCoefficient {d : ℕ} (i : Fin d) (δ : ℝ)
    (ψ : Vec d → ℝ) (ha : Continuous (physicalCoefficientField i δ ψ))
    (hV : Continuous (potentialField i δ ψ)) (x : Vec d)
    (hμ : 0 < densityField i δ ψ x) :
    reducedCoefficient (physicalEnvironment i δ ψ ha hV) x = coefficientField i ψ x :=
  reduce_physicalCoefficientField i δ ψ x hμ

/-- The shared reduced generator on the literal physical pair satisfies the clock
identity, with its factor `1/2` and its actual force coefficient. -/
theorem physicalEnvironment_generator {d : ℕ} (i : Fin d) (δ lam : ℝ) (ψ : Vec d → ℝ)
    (ha : Continuous (physicalCoefficientField i δ ψ))
    (hV : Continuous (potentialField i δ ψ))
    (hμ : ∀ y, 0 < densityField i δ ψ y) (hδ : δ ≠ 0)
    (hj : ∀ y, jacobianFactor i (gradient ψ y) ≠ 0) (x : Vec d) :
    reducedGenerator i (physicalEnvironment i δ ψ ha hV) lam ψ x =
      (1 - densityField i δ ψ x) / δ + lam * (1 - coefficientField i ψ x i i) := by
  have hcoeff : reducedCoefficient (physicalEnvironment i δ ψ ha hV) =
      coefficientField i ψ :=
    funext (fun y => physicalEnvironment_reducedCoefficient i δ ψ ha hV y (hμ y))
  simp only [reducedGenerator, hcoeff]
  exact clock_generator_identity i δ lam ψ hδ hj x

end EinsteinRelation.Sharpness
