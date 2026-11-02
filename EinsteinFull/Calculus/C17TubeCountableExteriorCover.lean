import EinsteinFull.Calculus.C17TubeParabolicScaling

open EinsteinRelation PDE MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

private theorem c17_euclideanNorm_neg {d : ℕ} (x : PDE.Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  simpa using TimeChange.euclideanNorm_smul (-1 : ℝ) x

/-- A countable family of Euclidean source balls covers the coordinate space. -/
theorem c17_countable_sourceBall_cover {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ q : ℕ → PDE.Vec d, ∀ x, ∃ n, x ∈ sourceBall (q n) (r/2) := by
  refine ⟨TopologicalSpace.denseSeq (PDE.Vec d), ?_⟩
  intro x
  have hx : x ∈ sourceBall x (r / 2) := by
    simp only [sourceBall, Set.mem_setOf_eq, sub_self]
    simp [euclideanNorm, euclideanSq, dot, hr]
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (PDE.Vec d)).exists_mem_open
    (c17_isOpen_sourceBall x (r / 2)) ⟨x, hx⟩
  refine ⟨n, ?_⟩
  change euclideanNorm (x - TopologicalSpace.denseSeq (PDE.Vec d) n) < r / 2
  change euclideanNorm (TopologicalSpace.denseSeq (PDE.Vec d) n - x) < r / 2 at hn
  simpa only [← neg_sub x (TopologicalSpace.denseSeq (PDE.Vec d) n),
    c17_euclideanNorm_neg] using hn

/-- Local exterior row bounds on all source balls give a global almost-everywhere bound. -/
theorem c17_exterior_row_bound_global_ae {d : ℕ} {r : ℝ} (hr : 0 < r)
    (μ : Measure (PDE.Vec d)) (K : PDE.Vec d → PDE.Vec d → ℝ≥0∞)
    (C : ℝ≥0∞)
    (hrow : ∀ q : PDE.Vec d, ∀ᵐ x ∂μ.restrict (sourceBall q (r/2)),
      (∫⁻ y in {y | r ≤ euclideanNorm (y-q)}, K x y ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, (∫⁻ y in {y | 2*r ≤ euclideanNorm (y-x)}, K x y ∂μ) ≤ C := by
  obtain ⟨q, hcover⟩ := c17_countable_sourceBall_cover (d := d) hr
  have hrows : ∀ᵐ x ∂μ, ∀ n, x ∈ sourceBall (q n) (r/2) →
      (∫⁻ y in {y | r ≤ euclideanNorm (y-q n)}, K x y ∂μ) ≤ C := by
    apply ae_all_iff.mpr
    intro n
    exact (ae_restrict_iff' (c17_isOpen_sourceBall (q n) (r/2)).measurableSet).mp (hrow (q n))
  filter_upwards [hrows] with x hx
  obtain ⟨n, hn⟩ := hcover x
  refine (lintegral_mono_set ?_).trans (hx n hn)
  intro y hy
  change 2*r ≤ euclideanNorm (y-x) at hy
  change r ≤ euclideanNorm (y-q n)
  change euclideanNorm (x-q n) < r/2 at hn
  have ht := TimeChange.euclideanNorm_add_le (y - q n) (q n - x)
  have he : (y - q n) + (q n - x) = y - x := by abel
  rw [he, ← neg_sub x (q n), c17_euclideanNorm_neg] at ht
  linarith

end EinsteinFull.Calculus
