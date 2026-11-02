import EinsteinFull.Calculus.C27RealForceRealizationAssembly

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- The signed exponential weight of the supplied zero-force law has unit mass. -/
theorem u3_reduced_force_exponential_weight_integral {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P) (lam : ℝ) (T : ℝ≥0) :
    let Z : Path d → ℝ := fun γ => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Integrable Z P ∧ (∫ γ, Z γ ∂P) = 1 :=
  c27_reduced_force_exponential_weight_integral hd hΛ hω i lam hP T

end EinsteinFull
