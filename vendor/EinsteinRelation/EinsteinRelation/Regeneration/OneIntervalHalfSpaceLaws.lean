import EinsteinRelation.Regeneration.OneIntervalBridgeSupport

/-!
# The two half-space identities for one diffusion interval

Source `paper/main.tex:377–381`. These identities implement the high/low
starting-point split in the past and the killed future calculation for
the actual diffusion and bridge mixture. Passing from one interval to
the full coupled kernels remains an internal proof obligation.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

section

variable (hLoc : External.GMPKernelLocality)
  {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
  (ω ω' : FieldPair d) (hω : IsRegular Λ₀ ω) (hω' : IsRegular Λ₀ ω')
  (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
  (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ₀ hΛ₀ ω hω lam h0 h1)
  (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ₀ hΛ₀ ω' hω' lam h0 h1)
  (P P' : QuenchedPathLaws d) (z : Vec d)
  (hP : P (z, ω) = r.pathLaw z) (hP' : P' (z, ω') = r'.pathLaw z)
  (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R) (i : Fin d)

include hLoc hP hP' hR

/-- The past half-space one-interval calculation, including the successful
bridge that vanishes when its starting point is too close to the barrier. -/
theorem oneInterval_past_integrals_eq_of_locality (v : ℝ) (hz : z i ≤ v)
    (heq : ∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) :
    (∫ γ, F γ ∂P (z, ω)) = (∫ γ, F γ ∂P' (z, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' z ω' := by
  let U : Set (Vec d) := {y | y i < v + 3 * R}
  have hU : IsOpen U := isOpen_lt (continuous_apply i) continuous_const
  have hzU : z ∈ U := by dsimp [U]; linarith
  have heqU : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y :=
    fun y hy => heq y hy.le
  have hsupportU : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U := by
    intro γ hn t ht
    have h := hsupport γ hn t ht
    dsimp [U]
    linarith
  by_cases hlow : z i < v - 8 * R
  · exact oneInterval_integrals_eq_of_locality hLoc hd Λ₀ hΛ₀ U hU ω ω' hω hω'
      lam h0 h1 heqU r r' P P' z hzU hP hP' Δ R i
      (couplingRegion_subset_past_halfSpace i R v z hlow) F hF hsegment hsupportU
  · obtain ⟨hm, hstop⟩ := Diffusion.realization_map_localityStoppedPath_eq hLoc hd Λ₀ hΛ₀
      U hU ω ω' hω hω' lam h0 h1 heqU r r' z hzU
    refine ⟨?_, ?_⟩
    · rw [hP, hP']
      exact integral_supported_segment_eq_of_stoppedLaw_eq U hU Δ _ _ hm hstop F hF
        hsegment hsupportU
    · rw [integral_killedBridgeMixture_eq_zero_of_past_barrier Δ R v i P z ω
          (not_lt.mp hlow) F hsupport,
        integral_killedBridgeMixture_eq_zero_of_past_barrier Δ R v i P' z ω'
          (not_lt.mp hlow) F hsupport]

/-- A future interval constrained above the no-backtracking barrier uses
only the environment in the specified future half-space. -/
theorem oneInterval_future_integrals_eq_of_locality (hz : -R ≤ z i)
    (heq : ∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → -R ≤ γ t i) :
    (∫ γ, F γ ∂P (z, ω)) = (∫ γ, F γ ∂P' (z, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' z ω' := by
  let U : Set (Vec d) := {y | -2 * R < y i}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_apply i)
  have hzU : z ∈ U := by dsimp [U]; linarith
  have heqU : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y :=
    fun y hy => heq y hy.le
  have hsupportU : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U := by
    intro γ hn t ht
    have h := hsupport γ hn t ht
    dsimp [U]
    linarith
  exact oneInterval_integrals_eq_of_locality hLoc hd Λ₀ hΛ₀ U hU ω ω' hω hω'
    lam h0 h1 heqU r r' P P' z hzU hP hP' Δ R i
    (couplingRegion_subset_future_halfSpace i R z hz) F hF hsegment hsupportU

end


end EinsteinRelation.Regeneration
