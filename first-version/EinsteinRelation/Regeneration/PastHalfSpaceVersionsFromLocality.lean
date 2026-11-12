import EinsteinRelation.Regeneration.CoupledHistoryHalfSpaceLocality
import EinsteinRelation.Probability.ParameterLocalVersions

/-!
# Joint past half-space versions from the frozen GMP locality input

Source `paper/main.tex:383–386`. Conditional resampling of the actual
environment yields a single version jointly measurable in the starting
point and the coefficients on the enlarged past half-space. Its origin
and spatial-a.e. identities are retained separately.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- The paper's complete past locality assertion follows from the
one-interval construction, deterministic restart, and frozen GMP locality. -/
theorem hasPastHalfSpaceVersions_of_gmp_locality
    (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hm : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (hr : HasDeterministicRestart Q.measure Δ K)
    (hone : Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K) :
    HasPastHalfSpaceVersions Q.measure Δ i R K := by
  have hgood := ae_coupledEnvironmentRegular hd Q lam h0 h1 P K hK hm hP Δ hΔ δ R i hr hone
  intro n hn v F hF hb hs
  let G : Set (Vec d × FieldPair d) := {p |
    CoupledEnvironmentRegular hd Λ₀ Q.ellipticity_parameter lam h0 h1 Δ δ R i P K p.2 ∧
      CoupledFibreRegular Δ δ R i P K p}
  have hGo : ∀ᵐ ω ∂Q.measure, (0, ω) ∈ G := hgood.mono fun _ h => ⟨h, h.2.1⟩
  have hGp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure, p ∈ G := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hgood, hK.2, hm.2, hr.2,
      hone.2] with p hg hp hm hr ho
    exact ⟨hg, hp, hm, hr, ho⟩
  let f : Vec d × FieldPair d → ℝ := fun p => ∫ z, F z ∂Probability.probabilityPart K p
  have hf : Measurable f :=
    ((hF.mono (Probability.finiteHistorySigma_le Δ n) le_rfl).stronglyMeasurable.integral_kernel
      (κ := Probability.probabilityPart K)).measurable
  have hlocal : ∀ x ω, (x, ω) ∈ G → ∀ ω', (x, ω') ∈ G →
      (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
      f (x, ω) = f (x, ω') := by
    intro x ω hg ω' hg' heq
    haveI := hg.2.1
    haveI := hg'.2.1
    dsimp only [f]
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure,
      Probability.probabilityPart_eq_of_isProbabilityMeasure]
    exact integral_history_eq_of_past_locality hLoc hd Λ₀ Q.ellipticity_parameter lam h0 h1
      Δ hΔ δ R hR i P K ω ω' hg.1 hg'.1 x hg.2 hg'.2 n hn F hF hb v heq hs
  obtain ⟨A, hA, hAo, hAp⟩ := Probability.exists_parameter_local_version_of_fields_eq_on
    Q.measure {y : Vec d | y i ≤ v + 3 * R} f hf G hGo hGp hlocal
  refine ⟨A, hA, ?_, ?_⟩
  · filter_upwards [hAo, hK.1] with ω ha hp
    haveI := hp
    exact ha.trans (congrArg (fun μ : Measure (CoupledSample d) => ∫ z, F z ∂μ)
      (Probability.probabilityPart_eq_of_isProbabilityMeasure K (0, ω)))
  · filter_upwards [hAp, hK.2] with p ha hp
    haveI := hp
    exact ha.trans (congrArg (fun μ : Measure (CoupledSample d) => ∫ z, F z ∂μ)
      (Probability.probabilityPart_eq_of_isProbabilityMeasure K p))


end EinsteinRelation.Regeneration
