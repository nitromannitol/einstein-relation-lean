import EinsteinRelation.Regeneration.FirstIntervalCoupledLaw

/-!
# Half-space locality of the first actual coupled history

Source `paper/main.tex:377–381`. Diffusion locality, the actual bridge
reweighting and the two first-bit identities give locality for every
bounded test of the first finite history. The environments in the GMP
realizations below are the reduced zero-potential pairs.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Lift supported segment integrals to the complete first history,
including its actual Bernoulli bit. -/
theorem integral_first_history_eq_of_supported_segment_integrals {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (P P' : QuenchedPathLaws d)
    (K K' : CoupledQuenchedLaws d) (xω xω' : Vec d × FieldPair d)
    [IsProbabilityMeasure (K xω)] [IsProbabilityMeasure (K' xω')]
    (hstart : ∀ᵐ z ∂K xω, z.1 0 = xω.1)
    (hstart' : ∀ᵐ z ∂K' xω', z.1 0 = xω'.1)
    (hone : Renewal.OneIntervalKernelAt Δ δ R i P K xω)
    (hone' : Renewal.OneIntervalKernelAt Δ δ R i P' K' xω')
    (V : Set (Vec d))
    (heq : ∀ G : Path d → ℝ, Measurable G → BoundedRealTest G →
      (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → G γ = G γ') →
      (∀ γ, G γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ V) →
      (∫ γ, G γ ∂P xω) = (∫ γ, G γ ∂P' xω') ∧
        (∫ γ, G γ ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2) =
          ∫ γ, G γ ∂Renewal.killedBridgeMixture Δ R i P' xω'.1 xω'.2)
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → z.1 t ∈ V) :
    (∫ z, F z ∂K xω) = ∫ z, F z ∂K' xω' := by
  have h : ∀ b : Bool,
      (∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b) ∂P xω) =
        (∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b) ∂P' xω') ∧
      (∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
        ∂Renewal.killedBridgeMixture Δ R i P xω.1 xω.2) =
        ∫ γ, F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
          ∂Renewal.killedBridgeMixture Δ R i P' xω'.1 xω'.2 := by
    intro b
    apply heq
    · exact (hF.mono (Probability.finiteHistorySigma_le Δ 1) le_rfl).comp
        ((measurable_id.prodMk measurable_const).comp
          (Diffusion.continuous_stopPathAt Δ).measurable)
    · obtain ⟨C, hC⟩ := hb
      exact ⟨C, fun _ => hC _⟩
    · intro γ γ' hh
      have hstop : Diffusion.stopPathAt Δ γ = Diffusion.stopPathAt Δ γ' := by
        apply ContinuousMap.ext
        intro t
        exact hh _ (min_le_right _ _)
      rw [hstop]
    · intro γ hn t ht
      have hv := hsupport (firstBitSample (Diffusion.stopPathAt Δ γ) b) hn t ht
      change γ (min t Δ) ∈ V at hv
      rwa [min_eq_left ht] at hv
  exact integral_first_history_eq_of_oneInterval_integrals Δ δ R i P P' K K' xω xω'
    hstart hstart' hone hone' F hF hb (fun b => (h b).1) (fun b => (h b).2)

section

variable (hLoc : External.GMPKernelLocality)
  {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
  (ω ω' : FieldPair d)
  (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
  (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
  (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
  (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
    (zeroPotentialReducedPair ω) hω lam h0 h1)
  (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
    (zeroPotentialReducedPair ω') hω' lam h0 h1)
  (P P' : QuenchedPathLaws d) (K K' : CoupledQuenchedLaws d) (x : Vec d)
  [IsProbabilityMeasure (K (x, ω))] [IsProbabilityMeasure (K' (x, ω'))]
  (hP : P (x, ω) = r.pathLaw x) (hP' : P' (x, ω') = r'.pathLaw x)
  (hm : (K (x, ω)).map Prod.fst = P (x, ω))
  (hm' : (K' (x, ω')).map Prod.fst = P' (x, ω'))
  (Δ : ℝ≥0) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
  (hone : Renewal.OneIntervalKernelAt Δ δ R i P K (x, ω))
  (hone' : Renewal.OneIntervalKernelAt Δ δ R i P' K' (x, ω'))

include hLoc hP hP' hm hm' hR hone hone'

/-- Past half-space locality for the first actual coupled interval,
derived from the frozen GMP locality input. -/
theorem integral_first_history_eq_of_past_locality (v : ℝ) (hx : x i ≤ v)
    (heq : ∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → z.1 t i ≤ v) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K' (x, ω') := by
  have hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x := by
    have h := r.pathLaw_starts_at x
    rw [← hP, ← hm] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hstart' : ∀ᵐ z ∂K' (x, ω'), z.1 0 = x := by
    have h := r'.pathLaw_starts_at x
    rw [← hP', ← hm'] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  apply integral_first_history_eq_of_supported_segment_integrals Δ δ R i P P' K K'
    (x, ω) (x, ω') hstart hstart' hone hone' {y | y i ≤ v} ?_ F hF hb hsupport
  intro G hG _ hs hsupportG
  exact reduced_oneInterval_past_integrals_eq_of_locality hLoc hd Λ₀ hΛ₀ ω ω' hω hω'
    lam h0 h1 r r' P P' x hP hP' Δ R hR i v hx heq G hG hs hsupportG

/-- Future half-space locality for a first interval constrained above
the no-backtracking barrier, including its actual first bit. -/
theorem integral_first_history_eq_of_future_locality (hx : -R ≤ x i)
    (heq : ∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → -R ≤ z.1 t i) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K' (x, ω') := by
  have hstart : ∀ᵐ z ∂K (x, ω), z.1 0 = x := by
    have h := r.pathLaw_starts_at x
    rw [← hP, ← hm] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hstart' : ∀ᵐ z ∂K' (x, ω'), z.1 0 = x := by
    have h := r'.pathLaw_starts_at x
    rw [← hP', ← hm'] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  apply integral_first_history_eq_of_supported_segment_integrals Δ δ R i P P' K K'
    (x, ω) (x, ω') hstart hstart' hone hone' {y | -R ≤ y i} ?_ F hF hb hsupport
  intro G hG _ hs hsupportG
  exact reduced_oneInterval_future_integrals_eq_of_locality hLoc hd Λ₀ hΛ₀ ω ω' hω hω'
    lam h0 h1 r r' P P' x hP hP' Δ R hR i hx heq G hG hs hsupportG

end


end EinsteinRelation.Regeneration
