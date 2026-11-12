import EinsteinRelation.Diffusion.PhysicalForceTranslation
import EinsteinRelation.Diffusion.PhysicalMeasureTranslation
import EinsteinRelation.Diffusion.PhysicalH1Representatives
import EinsteinRelation.Calculus.WeakGradientTranslation

/-!
# Spatial translation of the actual weighted Sobolev form

Source `paper/main.tex:406–408`. Representatives retain their actual
distributional gradients. The exponential weight contributes the same
positive constant to the reversible measure and to the energy.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- Translate an actual value and its distributional gradient in the
physical weighted graph. -/
def translatePhysicalGraph {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (a : Vec d)
    (u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam)) :
    SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam) where
  value x := u.value (a + x)
  weakGradient x := u.weakGradient (a + x)
  value_memLp := (memLp_comp_add_left_physicalForceMeasure_iff hd lam a u.value 2).mpr
    u.value_memLp
  gradient_memLp := (memLp_comp_add_left_physicalForceMeasure_iff hd lam a u.weakGradient 2).mpr
    u.gradient_memLp
  distributionalGradient := u.distributionalGradient.comp_add_left a

/-- The physical Sobolev domain is covariant under literal spatial
translation, with its full almost-everywhere representative condition. -/
theorem physicalH1Member_translate_iff {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (a : Vec d) (f : Vec d → ℝ) :
    physicalH1Member (translate a ω) hd lam f ↔
      physicalH1Member ω hd lam (fun y => f ((MeasurableEquiv.addLeft a).symm y)) := by
  rw [physicalH1Member_iff_exists_graph, physicalH1Member_iff_exists_graph]
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft a
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd)))
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hm : (physicalReversibleMeasure (translate a ω) hd lam).map e =
      c • physicalReversibleMeasure ω hd lam :=
    map_add_left_physicalReversibleMeasure ω hd lam a
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨translatePhysicalGraph hd lam (-a) u, ?_⟩
    have hmap : (fun y => u.value (e.symm y)) =ᵐ[
        (physicalReversibleMeasure (translate a ω) hd lam).map e]
          (fun y => f (e.symm y)) :=
      e.measurableEmbedding.ae_map_iff.mpr (by simpa only [e.symm_apply_apply] using hu)
    rw [hm] at hmap
    have h := (Measure.ae_smul_measure_iff hc).mp hmap
    simpa [translatePhysicalGraph, e, sub_eq_neg_add] using h
  · rintro ⟨u, hu⟩
    refine ⟨translatePhysicalGraph hd lam a u, ?_⟩
    have hscaled := Measure.ae_smul_measure hu c
    rw [← hm] at hscaled
    have h := e.measurableEmbedding.ae_map_iff.mp hscaled
    simpa [translatePhysicalGraph, e] using h

/-- The energy of a translated environment and graph has exactly the
constant prescribed by the physical reversible density. -/
theorem physicalH1FormEnergy_translate {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ) (a : Vec d)
    (u : SpatialDirichlet.WeightedSobolevGraph (physicalForceMeasure hd lam)) :
    physicalH1FormEnergy (translate a ω) hd lam u =
      Real.exp (-2 * lam * a (firstCoordinateIndex hd)) *
        physicalH1FormEnergy ω hd lam (translatePhysicalGraph hd lam (-a) u) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addLeft a
  have hm : (physicalReversibleMeasure (translate a ω) hd lam).map e =
      ENNReal.ofReal (Real.exp (-2 * lam * a (firstCoordinateIndex hd))) •
        physicalReversibleMeasure ω hd lam :=
    map_add_left_physicalReversibleMeasure ω hd lam a
  have hi := integral_map_equiv (μ := physicalReversibleMeasure (translate a ω) hd lam) e
    (fun y => SpatialDirichlet.weightedFormIntegrand (translate a ω).1 u u (e.symm y))
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hi
  unfold physicalH1FormEnergy
  calc
    _ = Real.exp (-2 * lam * a (firstCoordinateIndex hd)) *
        ∫ y, SpatialDirichlet.weightedFormIntegrand (translate a ω).1 u u (e.symm y)
          ∂physicalReversibleMeasure ω hd lam := by
      simpa only [e.symm_apply_apply, smul_eq_mul] using hi.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [SpatialDirichlet.weightedFormIntegrand, translatePhysicalGraph, translate,
          e]


end EinsteinRelation.External.GantertSection7Support
