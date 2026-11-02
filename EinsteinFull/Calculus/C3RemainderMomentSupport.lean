import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinRelation.Diffusion.GMPFamilyAPI

/-! Uniform conditioning and supplied-law facts for the remainder moment.
These lemmas do not assume a Girsanov or martingale-problem identification. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull
open EinsteinRelation

/-- The regeneration-tail dependency supplies a structural threshold with a
uniform lower bound on the actual no-return event, independent of the scale
and coin probability above that threshold. -/
theorem c3Remainder_exists_noReturn_half
    (htail : Blueprint.node_app_u3A_regen_u2D_tailsStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
      ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
        IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K →
        ENNReal.ofReal (1 / 2 : ℝ) ≤ Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) := by
  obtain ⟨l₀, hl₀, hsep, htail⟩ := htail d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l δ hl hδ₀ hδ₁ Q lam h₀ h₁ P K hK
  obtain ⟨c, C, a, M, _, _, _, _, _, htail⟩ := htail l hl δ hδ₀ hδ₁
  obtain ⟨_, hhalf, _⟩ := htail Q lam h₀ h₁ P K hK
  exact hhalf

/-- Restricting the supplied GMP reduced kernel to the origin retains its
actual realization, without replacing the supplied coupling by a canonical one. -/
theorem c3Remainder_originLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K) :
    IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h₀ h₁ (originLaw P) := by
  filter_upwards [hK.2.2.1] with ω hω
  obtain ⟨hω, r, hr⟩ := hω
  exact ⟨hω, r, hr 0⟩

/-- The origin law of the supplied coupling is almost surely a probability
measure; this uses only its actual GMP realization. -/
theorem c3Remainder_origin_probability {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K) :
    ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω) := by
  filter_upwards [isProbabilityMeasure_of_isGMPReducedKernel hd
    Q.ellipticity_parameter Q lam h₀ h₁ P hK.2.2.1] with ω hω
  exact hω 0

/-- The structural lower bound makes conditioning cost at most two on every
measurable event, under the literal conditioned measure in the target. -/
theorem c3Remainder_conditioned_event_le_two {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≤ Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)))
    {A : Set (FieldPair d × Regeneration.CoupledSample d)} (hA : MeasurableSet A) :
    regenerationConditionedLaw hd Q lam l K hK hD A ≤
      2 * Regeneration.annealedCoupledLaw Q.measure K A := by
  unfold regenerationConditionedLaw
  rw [ProbabilityTheory.cond_apply' hA]
  have hinv : (Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)))⁻¹ ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ :=
    ENNReal.inv_le_inv.mpr hhalf
  have hinv' : (Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)))⁻¹ ≤ 2 := by
    calc
      _ ≤ (ENNReal.ofReal (1 / 2 : ℝ))⁻¹ := hinv
      _ = 2 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        norm_num
  exact mul_le_mul' hinv' (measure_mono Set.inter_subset_right)

end EinsteinFull
