import EinsteinRelation.Correctors.CoefficientColumnDivergence
import EinsteinRelation.Correctors.LipschitzWeakPartial
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

/-! # The actual bounded initial divergence

Source: `paper/main.tex:787–792,850–852`. The original environment's
regularity gives a deterministic bound, depending only on dimension and
the original regularity parameter, for the weak divergence of each column
of the literal reduced coefficient field. -/

open MeasureTheory Set
open scoped NNReal

namespace EinsteinRelation.Correctors

/-- All entries of the reduced coefficient have an explicit deterministic
Lipschitz constant. Source: `paper/main.tex:194–207,850–852`. -/
theorem ae_reducedCoefficient_entry_lipschitz {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    let L : ℝ≥0 := ⟨Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2) * ((d : ℝ) + 1),
      by have hΛ := Q.ellipticity_parameter; positivity⟩
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ j k : Fin d,
      LipschitzWith L (fun x => ω.1 x j k) := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2) * ((d : ℝ) + 1),
    by have hΛ := Q.ellipticity_parameter; positivity⟩
  have hc : IsClosed {ω : FieldPair d | ∀ j k : Fin d,
      LipschitzWith L (fun x => ω.1 x j k)} := by
    simp only [lipschitzWith_iff_dist_le_mul, Set.setOf_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_iInter fun x => isClosed_iInter fun y => ?_
    have he (z : Vec d) : Continuous (fun ω : FieldPair d => ω.1 z j k) :=
      ((continuous_eval_const z).comp continuous_fst).matrix_elem j k
    exact isClosed_le ((he x).dist (he y)) continuous_const
  change ∀ᵐ ω ∂Measure.map reduce Q.measure, _
  rw [ae_map_iff Probability.measurable_reduce.aemeasurable hc.measurableSet]
  filter_upwards [Q.regular] with ω hω
  have hΛ := Q.ellipticity_parameter
  intro j k
  exact lipschitzWith_of_euclidean_bound _ (by positivity)
    ((reducedCoefficient_operatorLipschitz hΛ hω).entry_bound j k)

/-- The actual reduced column has its literal weak divergence, bounded
everywhere by a constant fixed before the sample and column.
Source: `paper/main.tex:787–792,850–852`. -/
theorem ae_reducedCoefficient_column_bounded_weak_divergence
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ i : Fin d,
      HasWeakDivergence univ (fun x j => ω.1 x j i)
        (divergence (fun x j => ω.1 x j i)) ∧
      ∀ x : Vec d, |divergence (fun y j => ω.1 y j i) x| ≤
        (d : ℝ) * (Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2) * ((d : ℝ) + 1)) := by
  filter_upwards [ae_reducedCoefficient_entry_lipschitz Q] with ω hω
  intro i
  constructor
  · exact hasWeakDivergence_of_coordinate_derivatives isOpen_univ
      (fun j => lipschitzWith_hasWeakPartialDerivative (hω j i) j)
  · exact abs_divergence_le_of_lipschitz_components (fun j => hω j i)

end EinsteinRelation.Correctors
