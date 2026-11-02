import EinsteinRelation.Regeneration.CoupledEnvironmentRegularity
import EinsteinRelation.Regeneration.CoupledEndpointSupport

/-!
# Half-space locality of every finite coupled history

Source `paper/main.tex:377–381`. Iteration uses the actual coupled
restart laws on their regular fibres. Endpoint absolute continuity
retains the spatial-a.e. qualifiers at each successive restart.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- On regular environments, supported first-interval comparisons
propagate to all actual finite histories. -/
theorem integral_supported_histories_eq_of_regular_environments
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
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
  haveI := hx.1
  haveI := hx'.1
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
        CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K η →
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
  (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
  (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
  (x : Vec d) (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
  (hx' : CoupledFibreRegular Δ δ R i P K (x, ω'))
  (n : ℕ) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
  (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F)
  (hb : BoundedRealTest F)

include hLoc hg hg' hx hx' hn hF hb hΔ hR

/-- The complete finite coupled past depends only on the enlarged past
half-space, with the literal finite-history and path support conditions. -/
theorem integral_history_eq_of_past_locality (v : ℝ)
    (heq : ∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → z.1 t i ≤ v) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω') := by
  apply integral_supported_histories_eq_of_regular_environments hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R i P K ω ω' hg hg' {y | y i ≤ v}
    (isClosed_le (continuous_apply i) continuous_const) ?_ x hx hx' n hn F hF hb hsupport
  intro y hy hyf hyf' G hG hbG hsG
  obtain ⟨hω, r, hr⟩ := hg.1
  obtain ⟨hω', r', hr'⟩ := hg'.1
  haveI := hyf.1
  haveI := hyf'.1
  exact integral_first_history_eq_of_past_locality hLoc hd Λ₀ hΛ₀ ω ω' hω hω'
    lam h0 h1 r r' P P K K y (hr y) (hr' y) hyf.2.1 hyf'.2.1 Δ δ R hR i
    hyf.2.2.2 hyf'.2.2.2 v hy heq G hG hbG (by
      simpa only [Probability.historyStays, Set.mem_setOf_eq, Nat.cast_one, one_mul] using hsG)

/-- The complete finite coupled future constrained above the barrier
depends only on the future half-space. -/
theorem integral_history_eq_of_future_locality
    (heq : ∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω') := by
  apply integral_supported_histories_eq_of_regular_environments hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R i P K ω ω' hg hg' {y | -R ≤ y i}
    (isClosed_le continuous_const (continuous_apply i)) ?_ x hx hx' n hn F hF hb hsupport
  intro y hy hyf hyf' G hG hbG hsG
  obtain ⟨hω, r, hr⟩ := hg.1
  obtain ⟨hω', r', hr'⟩ := hg'.1
  haveI := hyf.1
  haveI := hyf'.1
  exact integral_first_history_eq_of_future_locality hLoc hd Λ₀ hΛ₀ ω ω' hω hω'
    lam h0 h1 r r' P P K K y (hr y) (hr' y) hyf.2.1 hyf'.2.1 Δ δ R hR i
    hyf.2.2.2 hyf'.2.2.2 hy heq G hG hbG (by
      simpa only [Probability.historyStays, Set.mem_setOf_eq, Nat.cast_one, one_mul] using hsG)
end


end EinsteinRelation.Regeneration
