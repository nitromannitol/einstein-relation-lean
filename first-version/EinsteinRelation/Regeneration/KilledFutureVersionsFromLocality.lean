import EinsteinRelation.Regeneration.CoupledHistoryHalfSpaceLocality
import EinsteinRelation.Regeneration.KilledHistoryExtension
import EinsteinRelation.Probability.ConditionalLocalVersions

/-!
# Measurable killed-future versions from GMP locality

Source `paper/main.tex:383–387`. Supported finite histories determine the
entire killed path/bit measure. Conditional resampling of the actual
coefficient fields then produces the required local measurable version.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration

/-- Killed future locality follows from the frozen stopped-diffusion
locality and the paper's one-interval construction. -/
theorem hasKilledPathBitFutureVersions_of_gmp_locality
    (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hm : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (hr : HasDeterministicRestart Q.measure Δ K)
    (hone : Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K) :
    HasKilledPathBitFutureVersions Q.measure i R K := by
  have hgood := ae_coupledEnvironmentRegular hd Q lam h0 h1 P K hK hm hP Δ hΔ δ R i hr hone
  intro F hF hb
  let test : CoupledSample d → ℝ := fun z => if NoBacktracking R z.1 i then F z else 0
  have htest : Measurable test :=
    hF.ite ((measurableSet_NoBacktracking R i).preimage measurable_fst) measurable_const
  let f : FieldPair d → ℝ := fun ω => ∫ z, test z ∂Probability.probabilityPart K (0, ω)
  have hf : Measurable f :=
    (htest.stronglyMeasurable.integral_kernel (κ := Probability.probabilityPart K)).measurable.comp
      (measurable_const.prodMk measurable_id)
  let G : Set (FieldPair d) := {ω |
    CoupledEnvironmentRegular hd Λ₀ Q.ellipticity_parameter lam h0 h1 Δ δ R i P K ω}
  have hstart : ∀ ω ∈ G, ∀ᵐ z ∂K (0, ω), z.1 0 = 0 := by
    intro ω hω
    obtain ⟨_, r, hp⟩ := hω.1
    have hs := r.pathLaw_starts_at 0
    rw [← hp 0, ← hω.2.1.2.1] at hs
    exact ae_of_ae_map measurable_fst.aemeasurable hs
  have hlocal : ∀ ω ∈ G, ∀ ω' ∈ G,
      (∀ y ∈ {y : Vec d | -2 * R ≤ y i}, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
      f ω = f ω' := by
    intro ω hg ω' hg' heq
    haveI := hg.2.1.1
    haveI := hg'.2.1.1
    dsimp only [f]
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure,
      Probability.probabilityPart_eq_of_isProbabilityMeasure]
    apply integral_killed_eq_of_supported_history_integrals (K (0, ω)) (K (0, ω'))
      Δ hΔ R i (hstart ω hg) (hstart ω' hg')
    · intro n hn H hH hbH hsH
      exact integral_history_eq_of_future_locality hLoc hd Λ₀ Q.ellipticity_parameter lam h0 h1
        Δ hΔ δ R hR i P K ω ω' hg hg' 0 hg.2.1 hg'.2.1 n hn H hH hbH heq hsH
    · exact hF
    · exact hb
  obtain ⟨A, hA, hAe⟩ := Probability.exists_local_version_of_fields_eq_on Q.measure
    {y : Vec d | -2 * R ≤ y i} f hf G hgood hlocal
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAe, hK.1] with ω ha hp
  haveI := hp
  exact ha.trans (congrArg (fun μ : Measure (CoupledSample d) => ∫ z, test z ∂μ)
    (Probability.probabilityPart_eq_of_isProbabilityMeasure K (0, ω)))


end EinsteinRelation.Regeneration
