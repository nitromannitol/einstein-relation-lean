import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Set
open scoped Topology Manifold ContDiff

namespace EinsteinFull.Calculus

/-- A compact subset of an interval admits finitely many small windows whose
concentric doubled windows still lie in the interval. -/
theorem c18_compact_time_window_cover {a b : ℝ} (K : Set ℝ)
    (hK : IsCompact K) (hKi : K ⊆ Ioo a b) :
    ∃ n : ℕ, ∃ t r : Fin n → ℝ,
      (∀ i, 0 < r i ∧ Ioo (t i - 2 * r i) (t i + 2 * r i) ⊆ Ioo a b) ∧
      K ⊆ ⋃ i, Ioo (t i - r i) (t i + r i) := by
  classical
  have hrad : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      Ioo ((x : ℝ) - 2*r) ((x : ℝ) + 2*r) ⊆ Ioo a b := by
    intro x
    have hx := hKi x.property
    refine ⟨min ((x.val - a) / 4) ((b - x.val) / 4), ?_, ?_⟩
    · exact lt_min (by linarith [hx.1]) (by linarith [hx.2])
    · intro y hy
      have h₁ := min_le_left ((x.val - a) / 4) ((b - x.val) / 4)
      have h₂ := min_le_right ((x.val - a) / 4) ((b - x.val) / 4)
      constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
  choose r hr using hrad
  let U : K → Set ℝ := fun x => Ioo (x.val - r x) (x.val + r x)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [U, mem_Ioo]
    constructor <;> linarith [(hr ⟨x, hx⟩).1]
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  let e := Fintype.equivFin {x // x ∈ s}
  refine ⟨Fintype.card {x // x ∈ s}, (fun i => (e.symm i).val.val), (fun i => r (e.symm i).val), ?_, ?_⟩
  · intro i
    exact hr (e.symm i).val
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨e ⟨j, hj⟩, by simpa [U] using hxj⟩

/-- Smooth finite partition adapted to middle-half time windows. -/
theorem c18_compact_time_partition {a b : ℝ} (_hab : a < b)
    (K : Set ℝ) (hK : IsCompact K) (hKi : K ⊆ Ioo a b) :
    ∃ n : ℕ, ∃ η : Fin n → ℝ → ℝ, ∃ t r : Fin n → ℝ,
      (∀ i, 0 < r i ∧ Ioo (t i - 2*r i) (t i + 2*r i) ⊆ Ioo a b) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (η i) ∧ HasCompactSupport (η i) ∧
        tsupport (η i) ⊆ Ioo (t i-r i) (t i+r i)) ∧
      (∀ x ∈ K, ∑ i, η i x = 1) := by
  classical
  obtain ⟨n, t, r, hw, hc⟩ := c18_compact_time_window_cover K hK hKi
  let U : Fin n → Set ℝ := fun i => Ioo (t i-r i) (t i+r i)
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ)) hK.isClosed U (fun _ => isOpen_Ioo) hc
  refine ⟨n, (fun i => φ i), t, r, hw, ?_, ?_⟩
  · intro i
    have hi : tsupport (φ i) ⊆ Ioo (t i-r i) (t i+r i) := hφ i
    refine ⟨(φ i).contMDiff.contDiff, ?_, hi⟩
    exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) 
      (hi.trans Ioo_subset_Icc_self)
  · intro x hx
    rw [← φ.sum_eq_one hx]
    exact (finsum_eq_sum_of_support_subset _ (by simp)).symm

end EinsteinFull.Calculus
