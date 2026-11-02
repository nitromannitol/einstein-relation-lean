import EinsteinRelation.Probability.StoppedHistory

/-! # Finite-history prefix measurability

Source `paper/main.tex:272,353–364`. The exact finite-history sigma-algebra
`finiteHistorySigma Δ n` keeps the path through `nΔ` and the Bernoulli bits strictly
before `n`; the paper's `F_{n-1}` is its index `n-1` case. It is contained in the
product sigma-algebra, and every function of the coupled sample that depends only on
that finite prefix is measurable for it. The proof composes the function with the
stopped extension `stoppedHistorySample`, which is measurable from the finite-history
sigma-algebra, and uses the prefix hypothesis to identify the two values.
-/

open MeasureTheory EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinRelation.Probability

/-- A fixed-time path coordinate is measurable on the coupled path/Bernoulli space. -/
private theorem measurable_history_path_coord {d : ℕ} (t : ℝ≥0) :
    Measurable (fun z : CoupledSample d => z.1 t) :=
  (measurable_pathPosition (d := d) t).comp measurable_fst

/-- A fixed Bernoulli coordinate is measurable on the coupled path/Bernoulli space. -/
private theorem measurable_history_bit_coord {d : ℕ} (k : ℕ) :
    Measurable (fun z : CoupledSample d => z.2 k) :=
  (measurable_pi_apply (X := fun _ : ℕ => Bool) k).comp measurable_snd

/-- The exact finite-history sigma-algebra is contained in the product sigma-algebra. -/
theorem finiteHistorySigma_le {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    finiteHistorySigma (d := d) Δ n ≤ (inferInstance : MeasurableSpace (CoupledSample d)) := by
  unfold finiteHistorySigma
  apply sup_le
  · apply iSup_le
    intro t
    exact (measurable_history_path_coord (d := d) (t : ℝ≥0)).comap_le
  · apply iSup_le
    intro k
    exact (measurable_history_bit_coord (d := d) (k : ℕ)).comap_le

/-- A function of the coupled sample that agrees on every finite prefix is measurable for the
exact finite-history sigma-algebra. -/
theorem measurable_of_finite_history_prefix {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    {E : Type*} [MeasurableSpace E] (F : CoupledSample d → E) (hF : Measurable F)
    (hpre : ∀ z z' : CoupledSample d,
      (∀ t ∈ Set.Icc (0 : ℝ≥0) ((n : ℝ≥0) * Δ), z.1 t = z'.1 t) →
      (∀ k < n, z.2 k = z'.2 k) → F z = F z') :
    @Measurable (CoupledSample d) E (finiteHistorySigma Δ n) inferInstance F := by
  have hstop : F = fun z => F (stoppedHistorySample Δ n z) := by
    funext z
    exact hpre z (stoppedHistorySample Δ n z)
      (fun t ht => (stoppedHistorySample_path Δ n z t (Set.mem_Icc.mp ht).2).symm)
      (fun k hk => (stoppedHistorySample_bit Δ n z k hk).symm)
  have hcomp : @Measurable (CoupledSample d) E (finiteHistorySigma Δ n) inferInstance
      (F ∘ stoppedHistorySample Δ n) :=
    hF.comp (measurable_stoppedHistorySample Δ n)
  rw [hstop]
  exact hcomp

end EinsteinRelation.Probability
