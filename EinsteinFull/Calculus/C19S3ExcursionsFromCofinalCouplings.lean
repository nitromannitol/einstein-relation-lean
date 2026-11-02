import EinsteinFull.Calculus.C19S3EscapeFromCofinalCouplings

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- Strict displacement excursions form an open path event. -/
theorem c19_s3_measurableSet_excursion {d : ℕ} (i : Fin d) (B : ℝ) :
    MeasurableSet {γ : Path d | ∃ t : ℝ≥0, B < γ t i - γ 0 i} := by
  apply IsOpen.measurableSet
  have heq : {γ : Path d | ∃ t : ℝ≥0, B < γ t i - γ 0 i} =
      ⋃ t : ℝ≥0, {γ : Path d | B < γ t i - γ 0 i} := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply isOpen_iUnion
  intro t
  have heval (s : ℝ≥0) : Continuous (fun γ : Path d => γ s i) :=
    (continuous_apply i).comp (continuous_eval_const s)
  exact isOpen_lt continuous_const ((heval t).sub (heval 0))

/-- Cofinal couplings and finite regeneration yield unbounded path excursions. -/
@[nolint unusedArguments]
theorem c19_s3_unbounded_of_cofinal_couplings
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (c1_s3_excursion_of_finite_first_regeneration : ∀ {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
      (hlam : 0 < lam) (hR : 0 < R) (z : CoupledSample d) (i : Fin d),
      firstRegenerationTime Δ lam R z i ≠ ⊤ →
      ∃ t : ℝ≥0, 2 * R ≤ z.1 t i - z.1 0 i)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hSplits : ∀ L : ℝ, 0 < L → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ K : CoupledQuenchedLaws d, IsRegenerationCoupling hd Q lam L δ h0.le h1 P K)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (K : CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ B : ℝ,
      ∃ t : ℝ≥0, B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
  obtain ⟨L₀, hL₀, _, htail⟩ := htails d hd Λ₀ r₀
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  have hall : ∀ n : ℕ, ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      ∃ t : ℝ≥0, (n : ℝ) < q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd) := by
    intro n
    let L : ℝ := L₀ + ((n : ℝ) + 1) * lam
    have hL : 0 < L := by dsimp [L]; positivity
    have hLge : L₀ ≤ L := by
      dsimp [L]
      have hnonneg : 0 ≤ ((n : ℝ) + 1) * lam := mul_nonneg (by positivity) h0.le
      linarith
    have hn : (n : ℝ) < 2 * (L / lam) := by
      have hbound : (n : ℝ) + 1 ≤ L / lam := by
        apply (le_div_iff₀ h0).2
        dsimp [L]
        linarith
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨δ', hδ'0, hδ'1, K', hK'⟩ := hSplits L hL
    obtain ⟨c, C, a, M, hc, _, _, _, _, htail'⟩ := htail L hLge δ' hδ'0 hδ'1
    obtain ⟨_, _, htail'', _, _⟩ := htail' Q lam h0 h1 P K' hK'
    have ht : HasFirstRegenerationTail Q.measure (Renewal.regenDelta lam)
        lam (L / lam) c C (Renewal.forceCoord hd) K' := by
      intro t ht
      simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one] using htail'' t ht
    have hfin := firstRegenerationTime_ne_top_ae_of_tail Q.measure K'
      (Renewal.regenDelta lam) lam (L / lam) c C hc h0 (Renewal.forceCoord hd) ht
    have hev : ∀ᵐ q ∂annealedCoupledLaw Q.measure K',
        q.2.1 ∈ {γ : Path d | ∃ t : ℝ≥0, (n : ℝ) < γ t (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd)} := by
      filter_upwards [hfin] with q hq
      obtain ⟨t, ht⟩ := c1_s3_excursion_of_finite_first_regeneration
        (Renewal.regenDelta lam) hΔ lam (L / lam) h0 (div_pos hL h0) q.2
        (Renewal.forceCoord hd) hq
      exact ⟨t, hn.trans_le ht⟩
    exact c19_s3_transfer_path_event Q.measure P K' K hK'.1 hK.1
      hK'.2.1 hK.2.1 _ (c19_s3_measurableSet_excursion _ _) hev
  filter_upwards [ae_all_iff.mpr hall] with q hq
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨t, ht⟩ := hq n
  exact ⟨t, le_of_lt (hn.trans ht)⟩

end EinsteinFull.Blueprint
