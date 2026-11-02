import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Almost-everywhere reduced-generator identity

Rademacher's theorem gives one spatial event on which every entry of the actual reduced
coefficient is differentiable. The product rule then identifies the two generators on that
event simultaneously for all force directions, signed forces and twice differentiable tests.
-/

open scoped NNReal BigOperators

namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory

/-- For a regular environment, the divergence-form reduced generator agrees almost everywhere
with the textbook second-order operator, on one event independent of the force and test. -/
theorem c16_reduced_generator_ae_textbook {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ (i : Fin d) (lam : ℝ)
      (f : Vec d → ℝ), ContDiff ℝ 2 f →
      reducedGenerator i ω lam f x =
        External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam) f x := by
  have hA : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ k j : Fin d,
      DifferentiableAt ℝ (fun z => reducedCoefficient ω z k j) x := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun j => ?_
    exact (reducedCoefficient_lipschitz hΛ hω k j).ae_differentiableAt_of_real
  filter_upwards [hA] with x hx
  intro i lam f hf
  unfold reducedGenerator
  exact generator_eq_svGenerator_of_differentiableAt (reducedCoefficient ω) i lam hf hx

end EinsteinFull
