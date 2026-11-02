import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Bases
import Mathlib.Topology.Closure
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Hausdorff

/-! # Compact random bounds from local continuity

Local variant of `EinsteinRelation.Sharpness.exists_positive_probability_compact_bound`
(`CompactRandomBound.lean`) for the residual route of `paper/main.tex:1212–1216`. Each sample
path need only be continuous on the compact set `C`, and each point evaluation need only be
measurable at points `y ∈ C`. Nothing is assumed about `H ω` outside `C`, so the residual
observations indexed by a compact set are covered without global continuity.

The argument is the same as in `CompactRandomBound.lean`. A countable dense `D ⊆ C` reduces the
bound over `C` to countably many scalar bounds, each measurable by evaluation. Compactness gives
a finite real bound on every sample path over `C`, so these events cover `Ω`, and countable
subadditivity forces one of them to have positive probability. The only change is the
closed-sublevel step, which uses that `C ∩ f⁻¹' {x | |x| ≤ M}` is closed whenever `f` is
continuous on the closed set `C`.

This file makes no nondegeneracy claim and does not identify `H` with the noise field of
`NoiseKernel`; the caller supplies the sigma-algebra and measurability identifications.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Dense-subset reduction on a closed set. If `f` is continuous on the closed set `C` and
`D ⊆ C` is dense in `C`, then the bound `|f y| ≤ M` holds on all of `C` iff it holds on `D`.
The set `C ∩ f⁻¹' {x | |x| ≤ M}` is closed, so it contains `closure D`, which contains `C`. -/
private theorem abs_le_on_iff_of_dense_on {d : ℕ} (f : Vec d → ℝ) (C D : Set (Vec d))
    (hC : IsClosed C) (hfC : ContinuousOn f C) (hDC : D ⊆ C) (hCD : C ⊆ closure D) (M : ℝ) :
    (∀ y ∈ C, |f y| ≤ M) ↔ ∀ y ∈ D, |f y| ≤ M := by
  refine ⟨fun h y hy => h y (hDC hy), fun h y hy => ?_⟩
  have hclosed : IsClosed (C ∩ f ⁻¹' {x : ℝ | |x| ≤ M}) :=
    hfC.preimage_isClosed_of_isClosed hC (isClosed_le continuous_abs continuous_const)
  have hsub : D ⊆ C ∩ f ⁻¹' {x : ℝ | |x| ≤ M} := fun z hz => ⟨hDC hz, h z hz⟩
  have hcl : closure D ⊆ C ∩ f ⁻¹' {x : ℝ | |x| ≤ M} := closure_minimal hsub hclosed
  exact (hcl (hCD hy)).2

/-- Local compact bound with positive probability for a random field. Each sample path is
continuous on the compact set `C`, and each point evaluation is measurable for `y ∈ C`. Every
event `{ω | ∀ y ∈ C, |H ω y| ≤ M}` is measurable, and some natural bound `M` makes it have
positive probability. No global continuity, global measurability, or measurability of a
supremum is assumed. -/
theorem exists_positive_probability_compact_bound_of_local
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (H : Ω → Vec d → ℝ) (C : Set (Vec d)) (hC : IsCompact C)
    (hcont : ∀ ω, ContinuousOn (H ω) C)
    (hmeas : ∀ y ∈ C, Measurable (fun ω => H ω y)) :
  (∀ M : ℕ, MeasurableSet {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)}) ∧
  (∃ M : ℕ, 0 < P {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)}) := by
  obtain ⟨D, hDC, hDcount, hCD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace C).exists_countable_dense_subset
  have hmeasSet : ∀ M : ℕ, MeasurableSet {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} := by
    intro M
    have hset : {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} = ⋂ y ∈ D, {ω | |H ω y| ≤ (M : ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact abs_le_on_iff_of_dense_on (H ω) C D hC.isClosed (hcont ω) hDC hCD (M : ℝ)
    rw [hset]
    exact MeasurableSet.biInter hDcount fun y hyD =>
      measurableSet_le (hmeas y (hDC hyD)).abs measurable_const
  refine ⟨hmeasSet, ?_⟩
  have hbound : ∀ ω, ∃ M : ℕ, ∀ y ∈ C, |H ω y| ≤ (M : ℝ) := by
    intro ω
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hcont ω)
    obtain ⟨M, hM⟩ := exists_nat_ge B
    refine ⟨M, fun y hy => ?_⟩
    have h1 : ‖H ω y‖ ≤ B := hB y hy
    rw [Real.norm_eq_abs] at h1
    linarith
  have hcover : (⋃ M : ℕ, {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)}) = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    obtain ⟨M, hM⟩ := hbound ω
    exact Set.mem_iUnion.mpr ⟨M, hM⟩
  by_contra hne
  have hnull : ∀ M : ℕ, P {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} = 0 := by
    intro M
    have hnotpos : ¬ 0 < P {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)} := fun h => hne ⟨M, h⟩
    exact le_antisymm (not_lt.mp hnotpos) zero_le
  have hunion : P (⋃ M : ℕ, {ω | ∀ y ∈ C, |H ω y| ≤ (M : ℝ)}) = 0 :=
    measure_iUnion_null hnull
  rw [hcover, measure_univ] at hunion
  exact one_ne_zero hunion

end EinsteinRelation.Sharpness
