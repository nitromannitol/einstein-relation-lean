import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-! CompactIntervalEnclosure: auxiliary analytic estimates. Source: `paper/main.tex:808–816,833–848`. -/
namespace EinsteinRelation.Correctors

theorem compact_subset_inner_Icc {K : Set ℝ} {a b : ℝ} (hab : a < b)
    (hK : IsCompact K) (hsub : K ⊆ Set.Ioo a b) :
    ∃ c e : ℝ, a < c ∧ c ≤ e ∧ e < b ∧ K ⊆ Set.Icc c e := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · refine ⟨(3 * a + b) / 4, (3 * a + b) / 4, ?_, le_rfl, ?_, ?_⟩
    · linarith
    · linarith
    · rw [hempty]
      exact Set.empty_subset _
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne continuousOn_id
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne continuousOn_id
    have hxK : a < x ∧ x < b := hsub hx
    have hyK : a < y ∧ y < b := hsub hy
    have hxy : x ≤ y := isMinOn_iff.mp hmin y hy
    refine ⟨(a + x) / 2, (y + b) / 2, ?_, ?_, ?_, ?_⟩
    · linarith [hxK.1]
    · linarith [hxK.1, hxK.2, hyK.2]
    · linarith [hyK.2]
    · intro z hz
      have h1 : x ≤ z := isMinOn_iff.mp hmin z hz
      have h2 : z ≤ y := isMaxOn_iff.mp hmax z hz
      constructor
      · linarith [hxK.1]
      · linarith [hyK.2]

end EinsteinRelation.Correctors
