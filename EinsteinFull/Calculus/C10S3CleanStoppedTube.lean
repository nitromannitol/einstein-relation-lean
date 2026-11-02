import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinRelation.Regeneration.HalfSpaces

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

namespace C10Clean
/-- Rounding a finite time adds at most one grid step. -/
theorem roundUp_toNNReal_le_add (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (t : ℝ≥0∞) (ht : t ≠ ⊤) :
    (Regeneration.roundUp Δ t).toNNReal ≤ t.toNNReal + Δ := by
  rw [Regeneration.roundUp, ite_eq_right ht, ENNReal.toNNReal_coe]
  apply NNReal.coe_le_coe.mp
  change (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) * (Δ : ℝ) ≤ t.toReal + (Δ : ℝ)
  have hΔR : (0 : ℝ) < Δ := NNReal.coe_pos.mpr hΔ
  have hq : 0 ≤ t.toReal / (Δ : ℝ) := div_nonneg ENNReal.toReal_nonneg hΔR.le
  have hc : (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) <
      t.toReal / (Δ : ℝ) + 1 := Nat.ceil_lt_add_one hq
  have hmul := mul_lt_mul_of_pos_right hc hΔR
  rw [add_mul, div_mul_cancel₀ _ hΔR.ne', one_mul] at hmul
  exact hmul.le

/-- A full Euclidean tube at the actual passage implies the literal rounded
coordinate guard, retaining every time in the closed rounding interval. -/
theorem isGoodPassage_of_euclidean_tube {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (γ : Path d) (i : Fin d) (n : ℕ)
    (hfin : Regeneration.passageSequence Δ lam R a γ i n ≠ ⊤)
    (htube : ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
      euclideanNorm (γ ((Regeneration.passageSequence Δ lam R a γ i n).toNNReal + s) -
        γ (Regeneration.passageSequence Δ lam R a γ i n).toNNReal) ≤ R / 2) :
    Regeneration.IsGoodPassage Δ lam R a γ i n := by
  have hufin : Regeneration.roundUp Δ
      (Regeneration.passageSequence Δ lam R a γ i n) ≠ ⊤ := by
    rw [Regeneration.roundUp, ite_eq_right hfin]
    exact ENNReal.coe_ne_top
  refine ⟨hfin, hufin, fun t ht => ?_⟩
  have hs : t - (Regeneration.passageSequence Δ lam R a γ i n).toNNReal ≤ Δ :=
    (tsub_le_iff_right).mpr (by
      simpa only [add_comm] using
        (ht.2.trans (roundUp_toNNReal_le_add Δ hΔ _ hfin)))
  have hnorm := htube (t - (Regeneration.passageSequence Δ lam R a γ i n).toNNReal)
    ⟨zero_le, hs⟩
  rw [add_tsub_cancel_of_le ht.1] at hnorm
  exact (Regeneration.coordinate_abs_le_euclideanNorm
    (γ t - γ (Regeneration.passageSequence Δ lam R a γ i n).toNNReal) i).trans hnorm

end C10Clean

/-- The literal passage sequence following a deterministic restart, with its
level evaluated on the original sample. -/
noncomputable def c10CleanCouplingScopePassage {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (n : ℕ) (z : Regeneration.CoupledSample d) : ℝ≥0∞ :=
  Regeneration.passageSequence Δ lam R (A z)
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i n

/-- Even trials test the actual rounded guard, rather than a replacement
oscillation condition. -/
def c10CleanCouplingScopeEvenGuard {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (n : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z | Regeneration.IsGoodPassage Δ lam R (A z)
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ)).1 i (2 * n)}

/-- A finite prefix of failed even guards on finite passages, localized by
an original-sample event. This does not assert that the passages are finite. -/
def c10CleanCouplingScopeEvenGuardFailure {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d)
    (B : Set (Regeneration.CoupledSample d)) (N : ℕ) :
    Set (FieldPair d × Regeneration.CoupledSample d) :=
  {q | q.2 ∈ B ∧ ∀ r < N, c10CleanCouplingScopePassage Δ lam R A m i (2 * r) q.2 ≠ ⊤ ∧
    q.2 ∉ c10CleanCouplingScopeEvenGuard Δ lam R A m i r}

/-- A tube at the finite actual passage implies the rounded even guard. -/
theorem c10_clean_coupling_scope_tube_inter_subset_guard {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ) :
    let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
    let Tube := {q : FieldPair d × Regeneration.CoupledSample d |
      ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
        euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
          (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
    E ∩ Tube ⊆ E ∩ {q | q.2 ∈ c10CleanCouplingScopeEvenGuard Δ lam R A m i N} := by
  dsimp only
  intro q hq
  refine ⟨hq.1, ?_⟩
  exact C10Clean.isGoodPassage_of_euclidean_tube Δ hΔ lam R
    (A q.2) (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 i (2 * N)
    hq.1.2 hq.2

/-- An integrated tube estimate transfers to the actual guard on the same law. -/
theorem c10_clean_coupling_scope_guard_estimate_of_tube_estimate {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R ε : ℝ)
    (A : Regeneration.CoupledSample d → ℝ) (m : ℕ) (i : Fin d) (N : ℕ)
    (htube :
      let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
        {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
      let Tube := {q : FieldPair d × Regeneration.CoupledSample d |
        ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ,
          euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) -
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}
      ε * μ.real E ≤ μ.real (E ∩ Tube)) :
    let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
      {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
    ε * μ.real E ≤ μ.real (E ∩
      {q | q.2 ∈ c10CleanCouplingScopeEvenGuard Δ lam R A m i N}) :=
  htube.trans (measureReal_mono (c10_clean_coupling_scope_tube_inter_subset_guard Δ hΔ lam R A m i N))

/-- A uniform stopped-tube estimate implies the actual even guard estimate. -/
theorem c10_clean_s3_actual_guard_of_stopped_tube (hTube : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube)) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := c10CleanCouplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | c10CleanCouplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ c10CleanCouplingScopeEvenGuard Δ lam R A m i N}) := by
  obtain ⟨ε, hε, hε1, htube⟩ := hTube htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  refine ⟨ε, hε, hε1, ?_⟩
  intro m A hA N
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  exact c10_clean_coupling_scope_guard_estimate_of_tube_estimate μ
    (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) ε A m
    (Regeneration.Renewal.forceCoord hd) N (htube m A hA N)


end EinsteinFull.Blueprint
