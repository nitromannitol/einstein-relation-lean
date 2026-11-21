import EinsteinRelation.Regeneration.CoupledHistoryHalfSpaceLocality
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.CoupledHistoryHalfSpaceLocality`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinRelation.Regeneration.integral_supported_histories_eq_of_regular_environments`. -/
theorem integral_supported_histories_eq_of_regular_environments_phys
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (V : Set (Vec d)) (hV : IsClosed V)
    (hfirst : ∀ x ∈ V, CoupledFibreRegular Δ δ R i P K (x, ω) →
      CoupledFibreRegular Δ δ R i P K (x, ω') →
      ∀ F : CoupledSample d → ℝ,
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
        BoundedRealTest F → (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ 1 V) →
        (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω'))
    (x : Vec d) (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P K (x, ω'))
    (n : ℕ) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ n V) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω') := by
  have := hx.1
  have := hx'.1
  by_cases hxV : x ∈ V
  · apply integral_supported_histories_eq_of_first_interval_eq Δ hΔ V hV K K
      (x, ω) (x, ω') hx.2.2.1 hx'.2.2.1 (hfirst x hxV hx hx') ?_ ?_ ?_ n hn F hF hb hsupport
    · filter_upwards [hg.2.2.1, hg'.2.2.1] with y hy hy'
      exact ⟨hy.1, hy'.1, fun hyV => hfirst y hyV hy hy'⟩
    · intro m hm
      exact coupled_endpoint_density_of_path_marginal P K (x, ω) hx.2.1 _ (hg.2.2.2 m hm x)
    · intro m hm
      exact coupled_endpoint_density_of_path_marginal P K (x, ω') hx'.2.1 _ (hg'.2.2.2 m hm x)
  · have hz : ∀ (η : FieldPair d),
        CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K η →
        (K (x, η)).map Prod.fst = P (x, η) → (∫ z, F z ∂K (x, η)) = 0 := by
      intro η hη hm
      obtain ⟨_, r, hr⟩ := hη.1
      have hs := r.pathLaw_starts_at x
      rw [← hr x, ← hm] at hs
      have hstart := ae_of_ae_map measurable_fst.aemeasurable hs
      exact integral_supported_history_eq_zero_of_start_not_mem Δ n V
        (K (x, η)) x hxV hstart F hsupport
    rw [hz ω hg hx.2.1, hz ω' hg' hx'.2.1]

section
variable (hLoc : External.GMPKernelLocality)
  {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
  (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
  (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
  (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
  (hg : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
  (hg' : CoupledEnvironmentRegularPhys hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
  (x : Vec d) (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
  (hx' : CoupledFibreRegular Δ δ R i P K (x, ω'))
  (n : ℕ) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
  (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F)
  (hb : BoundedRealTest F)
include hLoc hg hg' hx hx' hn hF hb hΔ hR
end
end EinsteinRelation.Regeneration
