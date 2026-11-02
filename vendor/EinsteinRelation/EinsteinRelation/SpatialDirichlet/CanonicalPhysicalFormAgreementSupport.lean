import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.SpatialDirichlet.PhysicalResolventSupport

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-- The canonical force reference measure is the full weighted-H¹ graph measure. -/
theorem physicalForceMeasure_eq_densityWeightedMeasure {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) :
    External.GantertSection7Support.physicalForceMeasure hd lam =
      densityWeightedMeasure (External.GantertSection7Support.physicalForceWeight hd lam) := rfl

/-- The canonical physical reversible measure is the weighted measure used by the
physical form transport. -/
theorem physicalReversibleMeasure_eq_densityWeightedMeasure {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) :
    External.GantertSection7Support.physicalReversibleMeasure ω hd lam =
      densityWeightedMeasure
        (External.GantertSection7Support.physicalReversibleDensity ω hd lam) := rfl

/-- The force weight used by the canonical form is the density of the full source graph. -/
theorem physicalForceWeight_eq_sourceReducedDensity {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) :
    External.GantertSection7Support.physicalForceWeight hd lam = sourceReducedDensity hd lam := rfl

/-- The physical graph retains the weak gradient of the original full force-weight H¹
representative used by the canonical energy. -/
private theorem sourcePhysicalGraph_weakGradient {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam K : ℝ)
    (hMeasure : densityWeightedMeasure (sourcePhysicalDensity ω hd lam) ≤
      ENNReal.ofReal K • densityWeightedMeasure (sourceReducedDensity hd lam))
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    (sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) K hMeasure u).weakGradient =
    (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).weakGradient := by
  rfl

/-- A full force-weight H¹ element has the same diagonal physical Dirichlet form as the
canonical Gantert physical form, evaluated on its original force-weight graph representative.
The physical graph transport reuses that representative's Euclidean weak gradient. -/
theorem sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hω : IsRegular L ω)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u u =
    External.GantertSection7Support.physicalH1FormEnergy ω hd lam
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u) := by
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  have hDensity : sourcePhysicalDensity ω hd lam =
      External.GantertSection7Support.physicalReversibleDensity ω hd lam := by
    funext x
    rfl
  show _ = ∫ x, weightedFormIntegrand ω.1
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u)
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u) x
      ∂External.GantertSection7Support.physicalReversibleMeasure ω hd lam
  rw [physicalReversibleMeasure_eq_densityWeightedMeasure, ← hDensity]
  unfold sourcePhysicalDirichletForm weightedSpatialForm
  apply integral_congr_ae
  filter_upwards [] with x
  have hGraph := sourcePhysicalGraph_weakGradient ω hd lam (Real.exp (2 * L))
    (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u
  simp only [weightedFormIntegrand]
  rw [hGraph]

/-- The force-weight graph reconstructed from the quotient H¹ class has exactly the value
and gradient L² classes carried by that quotient. -/
theorem physicalH1Representative_pair_eq_quotient_pair {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ)
    (q : DensityWeightedH1 (sourceReducedDensity hd lam)) :
    densityWeightedGraphPair (sourceReducedDensity hd lam)
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q)) =
      densityWeightedH1GraphPair (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q := by
  rw [densityWeightedH1SpaceRepresentative_pair]
  first
    | rfl
    | simp [densityWeightedH1SpacePair, densityWeightedH1GraphEquiv,
        densityWeightedH1GraphEmbedding, densityWeightedH1GraphPair, Equiv.ofBijective_apply]

/-- The physical form agreement applies directly to a quotient weighted H¹ class through its
canonical full-graph equivalence. -/
theorem quotientSourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hω : IsRegular L ω) (q : DensityWeightedH1 (sourceReducedDensity hd lam)) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1
      (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q)
      (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q) =
    External.GantertSection7Support.physicalH1FormEnergy ω hd lam
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q)) := by
  exact sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy
    ω hd lam L hω (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q)

/-- The actual `Q`-almost-everywhere consumer of the physical/canonical form agreement.
The environment law supplies regularity almost surely; no isotropy condition is added. -/
theorem actualQ_sourcePhysicalDirichletForm_agreement {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
      ∀ lam : ℝ,
        ∀ q : DensityWeightedH1 (sourceReducedDensity hd lam),
          sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ₀))
            (sourcePhysicalMeasure_le_reduced ω hd lam Λ₀ hω) ω.1
            (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
              (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q)
            (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
              (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q) =
          External.GantertSection7Support.physicalH1FormEnergy ω hd lam
            (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
              (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
              (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
                (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q)) := by
  filter_upwards [Q.regular] with ω hω
  refine ⟨hω, ?_⟩
  intro lam q
  exact quotientSourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy
    ω hd lam Λ₀ hω q

end

end EinsteinRelation.SpatialDirichlet

