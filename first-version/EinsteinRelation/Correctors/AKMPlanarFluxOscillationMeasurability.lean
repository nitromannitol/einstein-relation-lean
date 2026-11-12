import EinsteinRelation.Correctors.AKMTranslatedFluxCorrector
import EinsteinRelation.Correctors.FluxHeatAverageTranslation

/-! Source: `paper/main.tex:724-731`. Measurability of the transported planar flux oscillation. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The squared planar flux oscillation remains almost surely measurable
at arbitrary centers, using the same translated raw flux-corrector carrier. -/
theorem aemeasurable_planar_flux_oscillation
    (h615 : FluxPlanarL2Estimate) {K : ℝ} (hK : 1 < K)
    (P : Measure (Coefficient 2 K)) (hP : LawHypotheses P)
    (e : Vec 2) (he : euclideanNorm e = 1)
    (φ : Corrector P e) (S : FluxCorrector φ) (z : Vec 2)
    (hPz : MeasurePreserving (translateCoefficient z) P P)
    (hPnz : MeasurePreserving (translateCoefficient (-z)) P P)
    (hc : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec 2)),
      φ.grad (translateCoefficient (-z) a) (x + z) = φ.grad a x)
    (r : ℝ) (hr : 2 ≤ r) :
    AEMeasurable (fun a => ⨍ x in ball z r,
      frobeniusNorm (S.potential a x - fluxHeatAverage (S.potential a) z r)^2 ∂volume) P := by
  have hs_pos : 0 < (1 : ℝ) := by norm_num
  have hs_lt_two : (1 : ℝ) < 2 := by norm_num
  rcases h615 K 1 hK hs_pos hs_lt_two with ⟨C, hC_pos, hOsBound⟩
  have hOsBound' := hOsBound P hP e he φ S r hr
  rcases hOsBound' with ⟨hAe0, _, _, _⟩
  let S' : FluxCorrector φ := inverseTranslatedFluxCorrector φ S z hPnz hc
  have hOsBoundS' := hOsBound P hP e he φ S' r hr
  rcases hOsBoundS' with ⟨hAeS', _, _, _⟩
  have hball_meas : MeasurableSet (ball (0 : Vec 2) r) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hG_eq : (fun a => ⨍ x in ball z r,
      frobeniusNorm (S.potential a x - fluxHeatAverage (S.potential a) z r) ^ 2 ∂volume) =
      (fun a => ⨍ x in ball 0 r,
        frobeniusNorm (S'.potential a x - fluxHeatAverage (S'.potential a) 0 r) ^ 2 ∂volume) ∘
      (translateCoefficient z) := by
    ext a
    dsimp
    rw [flux_ball_heat_oscillation_translate (S.potential a) z r]
    have h_potential_eq : S'.potential (translateCoefficient z a) =
        fun x => S.potential a (x + z) := by
      ext x
      dsimp [S', inverseTranslatedFluxCorrector]
      simp [translateCoefficient, add_comm]
    have h_heatAvg_eq : fluxHeatAverage (S'.potential (translateCoefficient z a)) 0 r =
        fluxHeatAverage (fun y => S.potential a (y + z)) 0 r := by
      rw [h_potential_eq]
    rw [h_heatAvg_eq]
    refine setAverage_congr_fun hball_meas ?_
    filter_upwards with x hx
    dsimp [S', inverseTranslatedFluxCorrector]
    simp [translateCoefficient, add_comm]
  rw [hG_eq]
  exact hAeS'.comp_quasiMeasurePreserving hPz.quasiMeasurePreserving

end EinsteinRelation.Correctors
