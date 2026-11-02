import EinsteinRelation.Regeneration.Construction

/-! # Measurability of a finite-window grid-shifted test function

Source `paper/main.tex:353–420`: the regeneration decomposition evaluates a function of the
coupled sample shifted by the deterministic grid time `nΔ` (`θ_{nΔ}`). If the function is
measurable for the finite-history sigma-algebra `finiteHistorySigma Δ m`, its composition with
the grid shift is measurable for `finiteHistorySigma Δ (n + m)`.

The shift `sampleTimeShift Δ z (nΔ)` keeps the absolute path start and moves the bits by
`gridIndex Δ (nΔ) = n`. A retained path value `z ↦ (θ z).1 t` with `t ≤ mΔ` is the original
value at the grid time `nΔ + t ≤ (n+m)Δ`, and a retained bit `z ↦ (θ z).2 k` with `k < m` is
the original bit `n + k < n + m`. Only the two generators of the finite-history sigma-algebras
enter; no new sigma-algebra, shift, or external premise is used.
-/

open MeasureTheory
open scoped NNReal ENNReal

open EinsteinRelation.Regeneration

namespace EinsteinRelation.Probability

/-- A shifted retained path value is an original path value at the grid time `nΔ + t`, which
lies in `[0, (n+m)Δ]`, so it is contained in the finite-history sigma-algebra for `n + m`. -/
private theorem comap_shift_path_le_finiteHistorySigma {d : ℕ} (Δ : ℝ≥0) (n m : ℕ)
    (t : ℝ≥0) (ht : t ∈ Set.Icc (0 : ℝ≥0) ((m : ℝ≥0) * Δ)) :
    MeasurableSpace.comap
        (fun z : CoupledSample d => (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).1 t) inferInstance ≤
      finiteHistorySigma (d := d) Δ (n + m) := by
  have hmem : (n : ℝ≥0) * Δ + t ∈ Set.Icc (0 : ℝ≥0) (((n + m : ℕ) : ℝ≥0) * Δ) := by
    refine ⟨zero_le, ?_⟩
    rw [Nat.cast_add, add_mul]
    exact add_le_add le_rfl ht.2
  show MeasurableSpace.comap
      (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ + t)) inferInstance ≤ _
  unfold finiteHistorySigma
  exact le_sup_of_le_left (le_iSup (fun s : Set.Icc (0 : ℝ≥0) (((n + m : ℕ) : ℝ≥0) * Δ) =>
    MeasurableSpace.comap (fun z : CoupledSample d => z.1 (s : ℝ≥0)) inferInstance)
    ⟨(n : ℝ≥0) * Δ + t, hmem⟩)

/-- A shifted retained bit `k < m` is the original bit `n + k < n + m`, so it is contained in
the finite-history sigma-algebra for `n + m`. The grid index of `nΔ` is `n` since `Δ > 0`. -/
private theorem comap_shift_bit_le_finiteHistorySigma {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (n m k : ℕ) (hk : k < m) :
    MeasurableSpace.comap
        (fun z : CoupledSample d => (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).2 k) inferInstance ≤
      finiteHistorySigma (d := d) Δ (n + m) := by
  have hfun : (fun z : CoupledSample d => (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)).2 k) =
      (fun z : CoupledSample d => z.2 (n + k)) := by
    funext z
    show z.2 (gridIndex Δ ((n : ℝ≥0) * Δ) + k) = z.2 (n + k)
    rw [gridIndex_mul Δ hΔ n]
  rw [hfun]
  unfold finiteHistorySigma
  exact le_sup_of_le_right (le_iSup (fun j : {j : ℕ // j < n + m} =>
    MeasurableSpace.comap (fun z : CoupledSample d => z.2 (j : ℕ)) inferInstance)
    ⟨n + k, by omega⟩)

/-- The grid time shift `z ↦ θ_{nΔ} z` maps the finite-history sigma-algebra for `n + m`
into the one for `m`: it uses only the path values at retained times and the retained bits. -/
private theorem measurable_grid_shift_finiteHistory {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (n m : ℕ) :
    @Measurable (CoupledSample d) (CoupledSample d) (finiteHistorySigma Δ (n + m))
      (finiteHistorySigma Δ m) (fun z => sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) := by
  refine measurable_iff_comap_le.mpr ?_
  unfold finiteHistorySigma
  rw [MeasurableSpace.comap_sup]
  refine sup_le ?_ ?_
  · rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun t => ?_
    rw [MeasurableSpace.comap_comp]
    exact comap_shift_path_le_finiteHistorySigma (d := d) Δ n m (t : ℝ≥0) t.2
  · rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_comp]
    exact comap_shift_bit_le_finiteHistorySigma (d := d) Δ hΔ n m (k : ℕ) k.2

/-- Source main.tex:353–420. If `F` is measurable for the finite-history sigma-algebra
`finiteHistorySigma Δ m`, then `z ↦ F (θ_{nΔ} z)` is measurable for `finiteHistorySigma Δ (n+m)`. -/
theorem measurable_finiteHistory_grid_shift_test {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (n m : ℕ)
    {E : Type*} [MeasurableSpace E] (F : CoupledSample d → E)
    (hF : @Measurable (CoupledSample d) E (finiteHistorySigma Δ m) inferInstance F) :
    @Measurable (CoupledSample d) E (finiteHistorySigma Δ (n+m)) inferInstance
    (fun z => F (sampleTimeShift Δ z ((n : ℝ≥0)*Δ))) := by
  have hcomp := hF.comp (measurable_grid_shift_finiteHistory (d := d) Δ hΔ n m)
  exact hcomp

end EinsteinRelation.Probability
