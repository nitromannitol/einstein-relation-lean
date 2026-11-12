import EinsteinRelation.Correctors.ConditionalMomentInputs

/-! Source: `paper/main.tex:834-883`. The sharp paired-energy obligations
needed by the continuous successor of Lemma 5.2. No conditional-expectation
conclusion or assumption on corrector representatives occurs here. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance pairEnergyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Sharp paired point-gradient and planar ball-energy moments, with
constants chosen before the environment law. These are internal analytic
obligations, not external inputs. Source: `paper/main.tex:834-883`. -/
def ConditionalPairEnergyBounds : Prop :=
  (∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ), 2 ≤ m →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : EnvironmentLaw d L r₀)
      (R : ℝ), 1 ≤ R → ∀ (y : Point d) (i : Fin d),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
        (FieldPair d × FieldPair d) => euclideanNorm
        (conditionalCorrectorGradient Q i y z.2.1 - conditionalCorrectorGradient Q i y z.2.2))
        (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B * R ^ (-(d : ℝ)/2))) ∧
  (∀ (L r₀ m : ℝ), 2 ≤ m → ∃ B : ℝ, 0 ≤ B ∧
    ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R → ∀ (y : Point 2) (i : Fin 2),
      MemLp (conditionalCopyGradientRms Q R y i) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ∧
      eLpNorm (conditionalCopyGradientRms Q R y i) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B/R))

end EinsteinRelation.Correctors
