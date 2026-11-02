import EinsteinFull.Blueprint.G1.Proofs.S3PrebridgeK

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion
  gridIndex)

/-! # `rt:m-renewal`: deterministic shift and position lemmas -/

theorem sampleTimeShift_add_grid {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (z : CoupledSample d)
    (n : ℕ) (b : ℝ≥0) :
    sampleTimeShift Δ z ((n : ℝ≥0) * Δ + b) =
      sampleTimeShift Δ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) b := by
  apply Prod.ext
  · exact (pathTimeShift_shift z.1 _ _).symm
  · funext k
    change z.2 (gridIndex Δ ((n : ℝ≥0) * Δ + b) + k) =
      z.2 (gridIndex Δ ((n : ℝ≥0) * Δ) + (gridIndex Δ b + k))
    rw [Regeneration.gridIndex_mul Δ hΔ, ← add_assoc]
    have hΔr : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
    have h : gridIndex Δ ((n : ℝ≥0) * Δ + b) = n + gridIndex Δ b := by
      unfold gridIndex
      have : (((n : ℝ≥0) * Δ + b : ℝ≥0) : ℝ) / (Δ : ℝ) = (b : ℝ) / (Δ : ℝ) + (n : ℝ) := by
        push_cast
        field_simp
        try ring
      rw [this, Nat.floor_add_natCast (by positivity), add_comm]
    rw [h]

theorem regenerationTime_succ_first {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) :
    ∀ (j : ℕ) (z : CoupledSample d),
      Regeneration.regenerationTime Δ lam R z i (j + 1) =
        firstRegenerationTime Δ lam R z i +
          Regeneration.regenerationTime Δ lam R
            (sampleTimeShift Δ z (firstRegenerationTime Δ lam R z i).toNNReal) i j := by
  intro j
  induction j with
  | zero =>
    intro z
    rw [Regeneration.regenerationTime_one]
    simp [Regeneration.regenerationTime]
  | succ j ih =>
    intro z
    by_cases hF : firstRegenerationTime Δ lam R z i = ⊤
    · have h1 : Regeneration.regenerationTime Δ lam R z i (j + 1) = ⊤ := by
        rw [ih z, hF, top_add]
      rw [Regeneration.regenerationTime, if_pos h1, hF, top_add]
    · obtain ⟨n, hn⟩ := Regeneration.firstRegenerationTime_mem_grid Δ hΔ lam R z i hF
      by_cases hb : Regeneration.regenerationTime Δ lam R
          (sampleTimeShift Δ z (firstRegenerationTime Δ lam R z i).toNNReal) i j = ⊤
      · have h1 : Regeneration.regenerationTime Δ lam R z i (j + 1) = ⊤ := by
          rw [ih z, hb, add_top]
        have h2 : Regeneration.regenerationTime Δ lam R
            (sampleTimeShift Δ z (firstRegenerationTime Δ lam R z i).toNNReal) i (j + 1) = ⊤ := by
          rw [Regeneration.regenerationTime, if_pos hb]
        rw [Regeneration.regenerationTime, if_pos h1, h2, add_top]
      · set z' := sampleTimeShift Δ z (firstRegenerationTime Δ lam R z i).toNNReal with hz'
        set a := firstRegenerationTime Δ lam R z i with ha
        set τ' := Regeneration.regenerationTime Δ lam R z' i j with hτ'
        have h1 : Regeneration.regenerationTime Δ lam R z i (j + 1) = a + τ' := ih z
        have h1ne : a + τ' ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hF, hb⟩
        have hnat : a.toNNReal = (n : ℝ≥0) * Δ := by
          rw [hn, ENNReal.toNNReal_coe]
        have h3 : (a + τ').toNNReal = (n : ℝ≥0) * Δ + τ'.toNNReal := by
          rw [ENNReal.toNNReal_add hF hb, hnat]
        have hshift : sampleTimeShift Δ z (a + τ').toNNReal =
            sampleTimeShift Δ z' τ'.toNNReal := by
          rw [h3, sampleTimeShift_add_grid Δ hΔ z n, ← hnat]
        have h4 : Regeneration.regenerationTime Δ lam R z' i (j + 1) =
            τ' + firstRegenerationTime Δ lam R (sampleTimeShift Δ z' τ'.toNNReal) i := by
          rw [Regeneration.regenerationTime, if_neg hb]
        have h5 : Regeneration.regenerationTime Δ lam R z i (j + 1 + 1) =
            (a + τ') + firstRegenerationTime Δ lam R (sampleTimeShift Δ z (a + τ').toNNReal) i := by
          rw [Regeneration.regenerationTime, if_neg (by rw [h1]; exact h1ne), h1]
        rw [h5, hshift, h4, add_assoc]

/-- The force-coordinate gain of every regeneration cycle. -/
theorem position_after_regen {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam)
    (hR : 0 < R) (i : Fin d) (hs : SliceChar Δ lam R i) :
    ∀ (j : ℕ) (z : CoupledSample d),
      (∀ n : ℕ, z.2 n = true →
        z.1 ((n : ℝ≥0) * Δ) i + 8 * R ≤ z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ) i) →
      Regeneration.regenerationTime Δ lam R z i j ≠ ⊤ →
      z.1 0 i + 10 * (j : ℝ) * R ≤
        z.1 (Regeneration.regenerationTime Δ lam R z i j).toNNReal i := by
  intro j
  induction j with
  | zero =>
    intro z _ _
    have h0 : Regeneration.regenerationTime Δ lam R z i 0 = 0 := rfl
    rw [h0, ENNReal.toNNReal_zero]
    simp
  | succ j ih =>
    intro z hgain hfin
    have hfj : Regeneration.regenerationTime Δ lam R z i j ≠ ⊤ :=
      regenerationTime_ne_top_of_le Δ lam R z i (Nat.le_succ j) hfin
    have hfj' := ih z hgain hfj
    obtain ⟨s, hs'⟩ := Regeneration.regenerationTime_mem_grid Δ hΔ lam R z i j hfj
    have hnat : (Regeneration.regenerationTime Δ lam R z i j).toNNReal =
        (s : ℝ≥0) * Δ := by rw [hs', ENNReal.toNNReal_coe]
    have hstep : Regeneration.regenerationTime Δ lam R z i (j + 1) =
        Regeneration.regenerationTime Δ lam R z i j +
          firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i := by
      rw [Regeneration.regenerationTime, if_neg hfj, hnat]
    rw [hnat] at hfj'
    have hFfin : firstRegenerationTime Δ lam R (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i ≠ ⊤ := by
      intro h
      apply hfin
      rw [hstep, h, add_top]
    obtain ⟨c, hc⟩ := Regeneration.firstRegenerationTime_mem_grid Δ hΔ lam R _ i hFfin
    have h2 := Regeneration.two_step_le_firstRegenerationTime Δ hΔ lam R hlam hR
      (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)) i
    rw [hc] at h2
    have hc2 : 2 ≤ c := by
      have h5 : (2 : ℝ≥0) * Δ ≤ (c : ℝ≥0) * Δ := by exact_mod_cast h2
      exact_mod_cast le_of_mul_le_mul_right h5 hΔ
    obtain ⟨hforced, hcoin, -⟩ := (hs c hc2 (sampleTimeShift Δ z ((s : ℝ≥0) * Δ))).mp hc
    have hg := (Regeneration.forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i (c - 1) _
      hforced).2
    have e1 : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).1 (((c - 1 : ℕ) : ℝ≥0) * Δ) i =
        z.1 (((s + (c - 1) : ℕ) : ℝ≥0) * Δ) i := by
      change z.1 ((s : ℝ≥0) * Δ + ((c - 1 : ℕ) : ℝ≥0) * Δ) i = _
      rw [← add_mul, ← Nat.cast_add]
    have e0 : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).1 0 i = z.1 ((s : ℝ≥0) * Δ) i := by
      change z.1 ((s : ℝ≥0) * Δ + 0) i = _
      rw [add_zero]
    rw [e1, e0] at hg
    have hcoin' : z.2 (s + (c - 1)) = true := by
      have : (sampleTimeShift Δ z ((s : ℝ≥0) * Δ)).2 (c - 1) = z.2 (s + (c - 1)) := by
        change z.2 (gridIndex Δ ((s : ℝ≥0) * Δ) + (c - 1)) = _
        rw [Regeneration.gridIndex_mul Δ hΔ]
      rw [← this]
      exact hcoin
    have hgn := hgain (s + (c - 1)) hcoin'
    have hsc : s + (c - 1) + 1 = s + c := by omega
    rw [hsc] at hgn
    have hpos : (Regeneration.regenerationTime Δ lam R z i (j + 1)).toNNReal =
        ((s + c : ℕ) : ℝ≥0) * Δ := by
      rw [hstep, hs', hc, ← ENNReal.coe_add, ← add_mul, ← Nat.cast_add, ENNReal.toNNReal_coe]
    rw [hpos, Nat.cast_succ]
    linarith

end EinsteinFull.Blueprint
