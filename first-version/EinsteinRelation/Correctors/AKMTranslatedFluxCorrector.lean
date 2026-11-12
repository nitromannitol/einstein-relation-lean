import EinsteinRelation.Correctors.AKMHeatSelectionTranslation
import EinsteinRelation.Correctors.AKMRealTranslation
import EinsteinRelation.Correctors.SpatialWeakTranslation
import EinsteinRelation.Correctors.AKMHeatFormulaOperations

/-!
# Backwards environment translation of source flux correctors

Source: `paper/main.tex:724-731,755-756`. Translate the environment
backwards and the spatial argument forwards. The canonical scalar gradient
identification gives the same centered source, and the literal heat limit
gives the flux-corrector carrier without an additional uniqueness premise.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Cancellation of opposite translations holds for the actual centered
coefficient-action flux whenever it holds for the scalar gradient. -/
theorem ae_inverse_translated_centeredFlux {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} (φ : Corrector P e) (z : Vec d)
    (hc : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      φ.grad (translateCoefficient (-z) a) (x + z) = φ.grad a x) :
    ∀ᵐ a ∂P,
      (fun x => centeredFlux φ (translateCoefficient (-z) a) (x + z)) =ᵐ[volume]
        centeredFlux φ a := by
  filter_upwards [hc] with a ha
  filter_upwards [ha] with x hx
  have he : -z + (x + z) = x := by abel
  change (a (-z + (x + z))).mulVec
    (e + φ.grad (translateCoefficient (-z) a) (x + z)) - meanFlux φ = _
  rw [he, hx]
  rfl

/-- Recenter a raw flux potential on the same scalar carrier. Every field
of the source flux-corrector structure, including heat selection, is proved. -/
noncomputable def inverseTranslatedFluxCorrector {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d}
    (φ : Corrector P e) (S : FluxCorrector φ) (z : Vec d)
    (hP : MeasurePreserving (translateCoefficient (-z)) P P)
    (hc : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      φ.grad (translateCoefficient (-z) a) (x + z) = φ.grad a x) :
    FluxCorrector φ where
  potential a x := S.potential (translateCoefficient (-z) a) (x + z)
  grad a j k x := S.grad (translateCoefficient (-z) a) j k (x + z)
  measurable_potential := S.measurable_potential.comp
    (((measurable_translateCoefficient (-z)).comp measurable_fst).prodMk
      (measurable_snd.add_const z))
  measurable_grad j k := (S.measurable_grad j k).comp
    (((measurable_translateCoefficient (-z)).comp measurable_fst).prodMk
      (measurable_snd.add_const z))
  weak_gradient := by
    filter_upwards [hP.quasiMeasurePreserving.ae S.weak_gradient] with a ha
    intro j k
    exact hasWeakGradient_translation _ _ (ha j k) z
  locally_square_integrable := by
    filter_upwards [hP.quasiMeasurePreserving.ae S.locally_square_integrable] with a ha
    intro R hR j k
    exact ⟨memLp_two_on_euclidean_balls_translation _
      (fun r hr => (ha r hr j k).1) z R hR,
      memLp_two_on_euclidean_balls_translation _
      (fun r hr => (ha r hr j k).2) z R hR⟩
  heat_selected := by
    filter_upwards [hP.quasiMeasurePreserving.ae S.heat_selected,
      ae_inverse_translated_centeredFlux φ z hc] with a ha hc
    exact isHeatSelectedFluxGradient_congr_source_ae hc
      (isHeatSelectedFluxGradient_translate ha z)

end EinsteinRelation.Correctors
