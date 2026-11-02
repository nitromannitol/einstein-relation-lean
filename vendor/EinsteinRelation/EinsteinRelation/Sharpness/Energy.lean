import EinsteinRelation.Environment.Basic
import Mathlib.Tactic.ByContra

/-! # The positive energy in the sharpness coefficient

`paper/main.tex`, `eq.sharp-constant`, lines 1261–1265. These pointwise facts use
the Euclidean sum of squares. The event that the actual constructed gradient is
nonzero with positive probability is a separate obligation.
-/

namespace EinsteinRelation.Sharpness

/-- The Euclidean squared norm is nonnegative. -/
theorem euclideanSq_nonneg {d : ℕ} (g : Vec d) : 0 ≤ euclideanSq g :=
  show 0 ≤ ∑ i, g i * g i from
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (g i))

/-- Positive Euclidean energy is equivalent to a nonzero vector. -/
theorem euclideanSq_pos_iff {d : ℕ} (g : Vec d) :
    0 < euclideanSq g ↔ g ≠ 0 := by
  rw [euclideanSq, dot, Finset.sum_pos_iff_of_nonneg (fun i _ => mul_self_nonneg (g i))]
  constructor
  · rintro ⟨i, _, hi⟩ hg
    simp only [hg, Pi.zero_apply, mul_zero, lt_self_iff_false] at hi
  · intro hg
    have hex : ∃ i, g i ≠ 0 := by
      by_contra! h
      exact hg (funext h)
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- The scalar energy appearing inside the expectation defining `c`. -/
noncomputable def sharpEnergy {d : ℕ} (i : Fin d) (g : Vec d) : ℝ :=
  euclideanSq g / (1 + g i)

theorem sharpEnergy_nonneg {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : 0 < 1 + g i) : 0 ≤ sharpEnergy i g :=
  div_nonneg (euclideanSq_nonneg g) hj.le

theorem sharpEnergy_pos_iff {d : ℕ} (i : Fin d) (g : Vec d)
    (hj : 0 < 1 + g i) : 0 < sharpEnergy i g ↔ g ≠ 0 := by
  rw [sharpEnergy, div_pos_iff_of_pos_right hj, euclideanSq_pos_iff]

end EinsteinRelation.Sharpness
