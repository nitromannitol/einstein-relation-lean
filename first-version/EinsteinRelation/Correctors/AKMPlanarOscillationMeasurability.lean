import EinsteinRelation.Correctors.AKMPlanarAllCenterScalarMoments

/-! Source: `paper/main.tex:724-731`. Measurability of the transported planar oscillation. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The arbitrary-center scalar L² oscillation is almost surely measurable,
even though the raw scalar carrier has no joint potential measurability field. -/
theorem aemeasurable_planar_scalar_oscillation
    (h46 : ScalarPlanarL2Estimate) {L r₀ : ℝ}
    (hK : 1 < AKMUpperEllipticity L)
    (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec 2)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec 2) (r : ℝ) (hr : 2 ≤ r) :
    AEMeasurable (fun a => Real.sqrt (⨍ x in ball z r,
      |φ.potential a x - scalarHeatAverage (φ.potential a) z r| ^ 2 ∂volume))
      (actualCoefficientLaw Q) := by
  have hd : 0 < 2 := by norm_num
  let ψ := inverseTranslatedScalarCorrector hd Q i φ hid z
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h_lt_two : (1 : ℝ) < 2 := by norm_num
  have h_euclidean : euclideanNorm (halfDirection i) < 1 := halfDirection_mem_ball i
  have h_law : LawHypotheses (actualCoefficientLaw Q) := lawHypotheses_actualCoefficientLaw Q
  obtain ⟨C, hC, h_bound⟩ := h46 (AKMUpperEllipticity L) (1 : ℝ) hK h_pos h_lt_two
  have h_bound' := h_bound (actualCoefficientLaw Q) h_law (halfDirection i) h_euclidean ψ r hr
  have h_ae_g : AEMeasurable (fun (b : Coefficient 2 (AKMUpperEllipticity L)) =>
      Real.sqrt (⨍ x in ball 0 r,
        |ψ.potential b x - scalarHeatAverage (ψ.potential b) 0 r| ^ 2 ∂volume))
      (actualCoefficientLaw Q) := h_bound'.1
  have h_mp : MeasurePreserving (translateCoefficient z) (actualCoefficientLaw Q)
      (actualCoefficientLaw Q) := measurePreserving_actualCoefficientTranslation Q z
  have h_ae_f : AEMeasurable (fun a =>
      Real.sqrt (⨍ x in ball 0 r,
        |ψ.potential (translateCoefficient z a) x - scalarHeatAverage (ψ.potential (translateCoefficient z a)) 0 r| ^ 2 ∂volume))
      (actualCoefficientLaw Q) :=
    h_ae_g.comp_quasiMeasurePreserving h_mp.quasiMeasurePreserving
  have h_eq : (fun a => Real.sqrt (⨍ x in ball z r,
      |φ.potential a x - scalarHeatAverage (φ.potential a) z r| ^ 2 ∂volume)) =
      (fun a => Real.sqrt (⨍ x in ball 0 r,
        |ψ.potential (translateCoefficient z a) x - scalarHeatAverage (ψ.potential (translateCoefficient z a)) 0 r| ^ 2 ∂volume)) := by
    ext a
    dsimp [ψ, inverseTranslatedScalarCorrector, correctorWithPotential]
    have h_trans : translateCoefficient (-z) (translateCoefficient z a) = a := by
      rw [translateCoefficient_add, neg_add_cancel, translateCoefficient_zero]
    calc
      Real.sqrt (⨍ x in ball z r, |φ.potential a x - scalarHeatAverage (φ.potential a) z r| ^ 2 ∂volume) =
          Real.sqrt (⨍ x in ball 0 r, |φ.potential a (x + z) - scalarHeatAverage (fun y => φ.potential a (y + z)) 0 r| ^ 2 ∂volume) := by
        rw [scalar_ball_heat_oscillation_translate (φ.potential a) z r]
      _ = Real.sqrt (⨍ x in ball 0 r, |φ.potential (translateCoefficient (-z) (translateCoefficient z a)) (x + z) -
          scalarHeatAverage (fun y => φ.potential (translateCoefficient (-z) (translateCoefficient z a)) (y + z)) 0 r| ^ 2 ∂volume) := by
        rw [h_trans]
      _ = Real.sqrt (⨍ x in ball 0 r, |(fun (a' : Coefficient 2 (AKMUpperEllipticity L)) (x' : Vec 2) =>
          φ.potential (translateCoefficient (-z) a') (x' + z)) (translateCoefficient z a) x -
          scalarHeatAverage ((fun (a' : Coefficient 2 (AKMUpperEllipticity L)) (x' : Vec 2) =>
          φ.potential (translateCoefficient (-z) a') (x' + z)) (translateCoefficient z a)) 0 r| ^ 2 ∂volume) := by
        simp [h_trans]
  rw [h_eq]
  exact h_ae_f

end EinsteinRelation.Correctors
