import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.HittingTimes
import EinsteinRelation.Probability.JointCrossingEvents
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurability of joint hitting times with a variable threshold

Source: `paper/main.tex:278-306` (`regen.hitting`, `regen.D`). For a pair `p = (u, γ)`
of a level and a continuous path, the downward and upward hitting times
`⨅ t (_ : γ t i - γ 0 i ≤ u), t` and `⨅ t (_ : u ≤ γ t i - γ 0 i), t` are measurable
as `ℝ≥0∞`-valued functions. Each sublevel `{≤ T}` is the finite-horizon event over
`[0, T]`, which is closed in `(u, γ)` by `isClosed_joint_downcrossing_by` and
`isClosed_joint_upcrossing_by`; the infinity branch is handled separately.
-/

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Probability

/-- Upward hitting times are downward hitting times of the negated path at the negated
level, so the finite-horizon characterization transfers. The algebraic step is
`-(x) - -(y) ≤ -a ↔ a ≤ x - y`. -/
private theorem upcrossing_inf_le_iff {d : ℕ} (γ : Path d) (i : Fin d) (a : ℝ) (T : ℝ≥0) :
    (⨅ (t : ℝ≥0) (_ : a ≤ γ t i - γ 0 i), (t : ℝ≥0∞)) ≤ (T : ℝ≥0∞) ↔
      ∃ t ∈ Set.Icc (0 : ℝ≥0) T, a ≤ γ t i - γ 0 i := by
  have hiff : ∀ t : ℝ≥0, (a ≤ γ t i - γ 0 i ↔ (-γ) t i - (-γ) 0 i ≤ -a) := by
    intro t
    simp only [ContinuousMap.neg_apply, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  have hcongr : (⨅ (t : ℝ≥0) (_ : a ≤ γ t i - γ 0 i), (t : ℝ≥0∞)) =
      ⨅ (t : ℝ≥0) (_ : (-γ) t i - (-γ) 0 i ≤ -a), (t : ℝ≥0∞) :=
    iInf_congr fun t => iInf_congr_Prop (hiff t) fun _ => rfl
  rw [hcongr, downcrossing_inf_le_iff (-γ) i (-a) T]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hiff t).mpr h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hiff t).mp h⟩

theorem measurable_joint_downcrossing_inf {d : ℕ} (i : Fin d) :
    Measurable (fun p : ℝ × Path d =>
      ⨅ (t : ℝ≥0) (_ : p.2 t i - p.2 0 i ≤ p.1), (t : ℝ≥0∞)) := by
  apply measurable_of_Iic
  intro T
  by_cases hT : T = ⊤
  · subst T
    simp
  · rw [← ENNReal.coe_toNNReal hT]
    have hset : (fun p : ℝ × Path d =>
        ⨅ (t : ℝ≥0) (_ : p.2 t i - p.2 0 i ≤ p.1), (t : ℝ≥0∞)) ⁻¹'
        Set.Iic (T.toNNReal : ℝ≥0∞) =
        {p : ℝ × Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T.toNNReal, p.2 t i - p.2 0 i ≤ p.1} := by
      ext p
      exact downcrossing_inf_le_iff p.2 i p.1 T.toNNReal
    rw [hset]
    exact (isClosed_joint_downcrossing_by i T.toNNReal).measurableSet

theorem measurable_joint_upcrossing_inf {d : ℕ} (i : Fin d) :
    Measurable (fun p : ℝ × Path d =>
      ⨅ (t : ℝ≥0) (_ : p.1 ≤ p.2 t i - p.2 0 i), (t : ℝ≥0∞)) := by
  apply measurable_of_Iic
  intro T
  by_cases hT : T = ⊤
  · subst T
    simp
  · rw [← ENNReal.coe_toNNReal hT]
    have hset : (fun p : ℝ × Path d =>
        ⨅ (t : ℝ≥0) (_ : p.1 ≤ p.2 t i - p.2 0 i), (t : ℝ≥0∞)) ⁻¹'
        Set.Iic (T.toNNReal : ℝ≥0∞) =
        {p : ℝ × Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T.toNNReal, p.1 ≤ p.2 t i - p.2 0 i} := by
      ext p
      exact upcrossing_inf_le_iff p.2 i p.1 T.toNNReal
    rw [hset]
    exact (isClosed_joint_upcrossing_by i T.toNNReal).measurableSet

end EinsteinRelation.Probability
