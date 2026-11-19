import EinsteinRelation.Regeneration.FirstRegenerationFiniteness

/-!
# Positive regeneration-cycle durations

Every finite regeneration cycle contains at least one grid interval. In particular, an
integrable finite cycle has positive expected duration, as needed for the regeneration
velocity ratio in Gantert–Mathieu–Piatnitski, Proposition 5.9.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Every finite regeneration cycle lasts at least one grid interval. -/
theorem regeneration_cycle_duration_ge {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (z : CoupledSample d) (i : Fin d) (k : ℕ)
    (hfin : regenerationTime Δ lam R z i (k + 1) ≠ ⊤) :
    (Δ : ℝ) ≤ (regenerationTime Δ lam R z i (k + 1)).toNNReal -
      (regenerationTime Δ lam R z i k).toNNReal := by
  have hk : regenerationTime Δ lam R z i k ≠ ⊤ := by
    intro htop
    apply hfin
    rw [regenerationTime, ite_eq_left htop]
  have hstep : firstRegenerationTime Δ lam R
      (sampleTimeShift Δ z (regenerationTime Δ lam R z i k).toNNReal) i ≠ ⊤ := by
    intro htop
    apply hfin
    rw [regenerationTime, ite_eq_right hk, htop, add_top]
  have hd := delta_le_firstRegenerationTime Δ lam R
    (sampleTimeShift Δ z (regenerationTime Δ lam R z i k).toNNReal) i
  have hΔ : Δ ≤ (firstRegenerationTime Δ lam R
      (sampleTimeShift Δ z (regenerationTime Δ lam R z i k).toNNReal) i).toNNReal := by
    apply ENNReal.coe_le_coe.mp
    simpa only [ENNReal.coe_toNNReal hstep] using hd
  rw [regenerationTime, ite_eq_right hk, ENNReal.toNNReal_add hk hstep]
  have hΔ' : (Δ : ℝ) ≤ ((firstRegenerationTime Δ lam R
      (sampleTimeShift Δ z (regenerationTime Δ lam R z i k).toNNReal) i).toNNReal : ℝ) := by
    exact_mod_cast hΔ
  rw [ENNReal.coe_toNNReal_eq_toReal] at hΔ'
  push_cast
  linarith

/-- An almost surely finite, integrable regeneration-cycle duration has positive mean. -/
theorem regeneration_cycle_expected_duration_pos {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) (k : ℕ)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      regenerationTime Δ lam R ωz.2 i (k + 1) ≠ ⊤)
    (hint : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ((regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal : ℝ) -
        (regenerationTime Δ lam R ωz.2 i k).toNNReal) (annealedCoupledLaw Q K)) :
    0 < ∫ ωz : FieldPair d × CoupledSample d,
      (((regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal : ℝ) -
        (regenerationTime Δ lam R ωz.2 i k).toNNReal) ∂annealedCoupledLaw Q K := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hb : ∀ᵐ ωz ∂annealedCoupledLaw Q K, (Δ : ℝ) ≤
      ((regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal : ℝ) -
        (regenerationTime Δ lam R ωz.2 i k).toNNReal := by
    filter_upwards [hfinite] with ωz hf
    exact regeneration_cycle_duration_ge Δ lam R ωz.2 i k hf
  have h := integral_mono_ae (integrable_const (Δ : ℝ)) hint hb
  have hΔ' : 0 < (Δ : ℝ) := by exact_mod_cast hΔ
  simpa using lt_of_lt_of_le hΔ' (by simpa using h)

end EinsteinFull.Regeneration
