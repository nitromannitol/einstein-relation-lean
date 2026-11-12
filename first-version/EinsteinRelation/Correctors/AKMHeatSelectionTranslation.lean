import EinsteinRelation.Correctors.HeatGradientTranslation
import EinsteinRelation.Correctors.SpatialBallTranslation
import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Translation of the local heat-selection limit

Source: `paper/main.tex:722,755-756`. The larger origin ball controls a
translated local ball. Both independent time cutoffs and their genuine
integrability clauses are retained.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning
open TimeChange

/-- Translating the centered source translates its selected gradient,
including all integrability and local `L²` convergence assertions. -/
theorem isHeatSelectedFluxGradient_translate {d : ℕ}
    {g : Vec d → Vec d} {G : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) (z : Vec d) :
    IsHeatSelectedFluxGradient (fun x => g (x + z))
      (fun j k x => G j k (x + z)) := by
  intro j k l R
  obtain ⟨N, hN⟩ := exists_nat_gt ((R : ℝ) + 1 + euclideanNorm z)
  have hRS : (R : ℝ) + 1 + euclideanNorm z ≤ (N : ℝ) + 1 := by linarith
  have hsub : ball z ((R : ℝ) + 1) ⊆ ball (0 : Vec d) ((N : ℝ) + 1) := by
    intro x hx
    have htri := euclideanNorm_add_le (x - z) z
    rw [sub_add_cancel] at htri
    change euclideanNorm (x - z) < (R : ℝ) + 1 at hx
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    rw [sub_zero]
    linarith
  have hm := Measure.restrict_mono_set (volume : Measure (Vec d)) hsub
  have hmp := measurePreserving_add_center_ball z ((R : ℝ) + 1)
  obtain ⟨hi, hT, hG, hlim⟩ := h j k l N
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n
    filter_upwards [hmp.quasiMeasurePreserving.ae (ae_mono hm (hi m n))] with x hx
    constructor
    · filter_upwards [hx.1] with t ht
      have hc := ((measurePreserving_add_right (volume : Measure (Vec d)) z).integrable_comp_emb
        (Homeomorph.addRight z).measurableEmbedding).mpr ht
      change Integrable (fun y => akmHeatGradientDensity g t j k l (x + z) (y + z))
        volume at hc
      simpa only [← akmHeatGradientDensity_translation] using hc
    · simpa only [akmHeatGradientSpaceIntegral_translation] using hx.2
  · intro m n
    simpa only [iteratedAKMHeatGradientTruncation_translation] using
      ((hT m n).mono_measure hm).comp_measurePreserving hmp
  · exact (hG.mono_measure hm).comp_measurePreserving hmp
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le _) ?_
    intro mn
    simpa only [iteratedAKMHeatGradientTruncation_translation] using
      eLpNorm_add_center_ball_le
        (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G j k x l)
        z ((R : ℝ) + 1) ((N : ℝ) + 1) hRS ((hT mn.1 mn.2).sub hG).aestronglyMeasurable

end EinsteinRelation.Correctors
