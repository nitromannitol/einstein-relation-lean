import EinsteinRelation.Diffusion.FellerKernelUniquenessSupport

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- Source `paper/main.tex:400–402`: weighted Sobolev membership can be tested on an actual weak-gradient representative. -/
theorem physicalH1Member_iff_exists_graph {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (f : Vec d → ℝ) :
    physicalH1Member ω hd lam f ↔
      ∃ u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam),
        u.value =ᵐ[physicalReversibleMeasure ω hd lam] f := by
  have hrep : ∀ u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam),
      SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam)
        (Quotient.mk _ u) =ᵐ[physicalReversibleMeasure ω hd lam] u.value := by
    intro u
    have h := u.value_memLp.coeFn_toLp
    have hvol := (SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp h
    exact (SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) _).mpr hvol
  constructor
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h u => exact ⟨u, (hrep u).symm.trans hq⟩
  · rintro ⟨u, hu⟩
    exact ⟨Quotient.mk _ u, (hrep u).trans hu⟩

end EinsteinRelation.External.GantertSection7Support
