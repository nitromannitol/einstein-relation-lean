import EinsteinRelation.Regeneration.CoupledCovarianceFromLocality
import EinsteinRelation.Regeneration.CouplingSpatialMaps
import EinsteinRelation.Regeneration.RenewalCarriers
import Mathlib.MeasureTheory.Measure.Prod

/-! # Spatial transport of the V2 one-interval ingredients

Source `paper/main.tex:268,383–396`. The killed path restriction transports
under recentering, and stationarity transports origin exceptional sets to
the translated environment at product-almost every starting pair.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration.Renewal

/-- Recenter a killed segment using a covariance identity for the unrestricted law
(`paper/main.tex:268,383–384`). -/
theorem map_recenterPath_killedSegmentLaw {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (x z : Vec d) (ω : FieldPair d)
    (hP : Measure.map (recenterPath x) (P (z, ω)) =
      P (z - x, translate x ω)) :
    Measure.map (recenterPath x) (killedSegmentLaw Δ R i P z ω) =
      killedSegmentLaw Δ R i P (z - x) (translate x ω) := by
  unfold killedSegmentLaw
  rw [← hP]
  change Measure.map (recenterPathEquiv x) _ =
    (Measure.map (recenterPathEquiv x) _).restrict _
  rw [(recenterPathEquiv x).restrict_map]
  have hs : {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R z} =
      (recenterPathEquiv x) ⁻¹'
        {γ : Path d | ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R (z - x)} := by
    ext γ
    exact forall_congr' fun t => imp_congr_right fun _ =>
      (sub_mem_couplingRegion_iff i R x (γ t) z).symm
  rw [hs]

/-- Translating the environment while retaining the spatial point preserves the
product law (`paper/main.tex:397–409`). -/
theorem measurePreserving_spatial_translate {d : ℕ} (Q : Measure (FieldPair d))
    [SFinite Q] (hQ : IsStationary Q) :
    MeasurePreserving (fun p : Vec d × FieldPair d => (p.1, translate p.1 p.2))
      ((volume : Measure (Vec d)).prod Q) ((volume : Measure (Vec d)).prod Q) := by
  exact (MeasurePreserving.id (volume : Measure (Vec d))).skew_product
    Probability.continuous_translate.measurable
    (Filter.Eventually.of_forall hQ)

/-- An origin-a.e. property holds at the translated environment for product-a.e.
starting pair. This retains the distinct origin clause of V2. -/
theorem ae_spatial_translate_of_ae {d : ℕ} (Q : Measure (FieldPair d))
    [SFinite Q] (hQ : IsStationary Q) {p : FieldPair d → Prop} (hp : ∀ᵐ ω ∂Q, p ω) :
    ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), p (translate xω.1 xω.2) := by
  have hsnd : ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q), p xω.2 :=
    Measure.quasiMeasurePreserving_snd.ae hp
  exact (measurePreserving_spatial_translate Q hQ).quasiMeasurePreserving.ae hsnd

/-- The complete V2 coupling is covariant for every admissible coupling in the
positive physical scale range of Lemma 3.1 (`paper/main.tex:348–354,406–408`).
The only literature hypothesis is the already frozen GMP locality input. -/
theorem coupling_covariance_of_isGMPCouplingV2 (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K) :
    ∀ᵐ xω ∂((volume : Measure (Vec d)).prod Q.measure),
      Measure.map (recenterSample xω.1) (K xω) = K (0, translate xω.1 xω.2) := by
  have hΔ : 0 < regenDelta lam := by
    unfold regenDelta
    exact Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hl0))
  exact coupled_spatial_covariance_of_gmp_locality hLoc hd Q lam hl0.le hl1 P K
    hK.1 hK.2.1 hK.2.2.1 (regenDelta lam) hΔ δ (l / lam) (div_pos hl hl0)
    (forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.2

end EinsteinRelation.Regeneration.Renewal
