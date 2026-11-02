import EinsteinRelation.Probability.FiniteHistoryLpDensity

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:377–381`: exact finite histories exhaust the coupled sample sigma-algebra. -/
theorem iSup_finiteHistorySigma_eq {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    (⨆ n : ℕ, finiteHistorySigma (d := d) Δ n) =
      (inferInstance : MeasurableSpace (CoupledSample d)) := by
  set M : MeasurableSpace (CoupledSample d) := ⨆ n : ℕ, finiteHistorySigma (d := d) Δ n
  apply le_antisymm
  · exact iSup_le fun n => EinsteinRelation.Probability.finiteHistorySigma_le Δ n
  · have h_path_eval (t : ℝ≥0) :
        MeasurableSpace.comap (fun z : CoupledSample d => z.1 t) inferInstance ≤ M := by
      obtain ⟨n, hn⟩ := exists_nat_ge (t / Δ)
      have ht : t ≤ (n : ℝ≥0) * Δ := (div_le_iff₀ hΔ).mp hn
      have hle : MeasurableSpace.comap (fun z : CoupledSample d => z.1 t) inferInstance ≤
          finiteHistorySigma (d := d) Δ n := by
        unfold finiteHistorySigma
        exact le_sup_of_le_left
          (le_iSup_of_le (⟨t, ⟨zero_le, ht⟩⟩ : Set.Icc (0 : ℝ≥0) ((n : ℝ≥0) * Δ)) le_rfl)
      exact hle.trans (le_iSup (fun m : ℕ => finiteHistorySigma (d := d) Δ m) n)
    have h_bit_eval (k : ℕ) :
        MeasurableSpace.comap (fun z : CoupledSample d => z.2 k) inferInstance ≤ M := by
      have hle : MeasurableSpace.comap (fun z : CoupledSample d => z.2 k) inferInstance ≤
          finiteHistorySigma (d := d) Δ (k + 1) := by
        unfold finiteHistorySigma
        exact le_sup_of_le_right
          (le_iSup_of_le (⟨k, Nat.lt_succ_self k⟩ : {k_1 : ℕ // k_1 < k + 1}) le_rfl)
      exact hle.trans (le_iSup (fun n : ℕ => finiteHistorySigma (d := d) Δ n) (k + 1))
    have h_pi_path : @Measurable (CoupledSample d) (ℝ≥0 → Vec d) M MeasurableSpace.pi
        (fun z t => z.1 t) := by
      rw [measurable_pi_iff]
      intro t
      apply (measurable_iff_comap_le (f := fun z : CoupledSample d => z.1 t)).mpr
      exact h_path_eval t
    have h_pi_bit : @Measurable (CoupledSample d) (ℕ → Bool) M MeasurableSpace.pi
        (fun z => z.2) := by
      rw [measurable_pi_iff]
      intro k
      apply (measurable_iff_comap_le (f := fun z : CoupledSample d => z.2 k)).mpr
      exact h_bit_eval k
    obtain ⟨D, hDm, hDinv⟩ :=
      EinsteinRelation.Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)
    have hfst : @Measurable (CoupledSample d) (Path d) M inferInstance Prod.fst := by
      have heq : Prod.fst = D ∘ fun (z : CoupledSample d) (t : ℝ≥0) => z.1 t :=
        funext fun z => (hDinv z.1).symm
      rw [heq]
      exact hDm.comp h_pi_path
    have hsnd : @Measurable (CoupledSample d) (ℕ → Bool) M MeasurableSpace.pi Prod.snd := h_pi_bit
    delta CoupledSample
    apply sup_le
    · rw [← measurable_iff_comap_le]
      exact hfst
    · rw [← measurable_iff_comap_le]
      exact hsnd


end EinsteinRelation.Regeneration
