import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.EndpointGap

/-!
# The local past version used in the slice factorization

Source `paper/main.tex:385–400`. The endpoint-ball test on the forced trial
event sees only paths below `yᵢ - 7R`. Thus the existing finite-history
locality target gives a version of the actual past integral measurable
below `yᵢ - 4R`. This lemma does not assume the slice factorization.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- No trial can start at the first grid endpoint: the required prestart
displacement is positive, whereas the prestart time is zero. -/
theorem forcedBitTrialEvent_zero_eq_empty {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d) :
    forcedBitTrialEvent Δ lam R i 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := (forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i 0 z hz).2
  simp only [Nat.cast_zero, zero_mul, sub_self] at hh
  linarith

/-- The source's past factor has an a.e. version in the corrected past
half-space, provided finite-history coupled locality has been proved.
The locality premise here is an internal obligation. -/
theorem exists_firstSlicePastIntegral_local_version {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hpast : HasPastHalfSpaceVersions Q Δ i R K)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (y : Vec d) :
    ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧
      (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) =ᵐ[Q] A := by
  by_cases hm : m = 0
  · subst m
    refine ⟨fun _ => 0, measurable_const, Filter.Eventually.of_forall fun ω => ?_⟩
    simp [firstSlicePastIntegral, forcedBitTrialEvent_zero_eq_empty Δ hΔ lam R hlam hR i]
  let G := (forcedBitTrialEvent Δ lam R i m).indicator H
  let E : Set (CoupledSample d) :=
    {z | y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}
  let F := E.indicator G
  have hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance F :=
    (hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)).indicator
      (measurableSet_endpointBall_past Δ R i m y)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · by_cases hΓ : z ∈ forcedBitTrialEvent Δ lam R i m
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
          (hC z).trans (le_max_left C 0)
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ, abs_zero] using
          (le_max_right C 0)
    · simpa only [F, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hbar : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R := by
    intro z hz
    have he : z ∈ E := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    have hΓ : z ∈ forcedBitTrialEvent Δ lam R i m := by
      by_contra h
      exact hz (by simp [F, G, he, h])
    exact forcedBitTrialEvent_endpoint_past_barrier Δ hΔ lam R hlam hR i m z hΓ y he
  obtain ⟨A, hA, hAo, _⟩ := hpast m (by omega) (y i - 7 * R) F hF hbF hbar
  have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hv] at hA
  refine ⟨fun ω => A (0, ω), hA.comp measurable_prodMk_left, ?_⟩
  filter_upwards [hAo] with ω hω
  rw [hω]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) <;> simp [F, G, E, hz]


end EinsteinRelation.Regeneration
