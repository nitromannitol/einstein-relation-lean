import EinsteinFull.Regeneration.SlabSmoothPayoff
import EinsteinFull.Regeneration.BoxCutoff

/-!
# Compact smooth extensions of slab payoffs

A box cutoff leaves a prescribed closed ball unchanged and makes the smooth
slab payoff compactly supported.
-/

open Set PDE

namespace EinsteinFull.Regeneration

/-- The slab payoff has a unit-bounded compact smooth extension on any closed ball. -/
theorem exists_compact_smooth_slabPayoff {d : ℕ} (i : Fin d) (c y : PDE.Vec d)
    (R N : ℝ) :
    ∃ f : PDE.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      Set.EqOn f (slabSmoothPayoff i c R) (Metric.closedBall y N) := by
  let a : PDE.Vec d := fun j => y j - (N + 2)
  let b : PDE.Vec d := fun j => y j + (N + 2)
  let δ : PDE.Vec d := fun _ => 1
  let η := quantitativeBoxCutoff a b δ (fun _ => by dsimp [δ]; norm_num)
  let f : PDE.Vec d → ℝ := fun z => η z * slabSmoothPayoff i c R z
  have hplateau : ∀ z ∈ Metric.closedBall y N, η z = 1 := by
    intro z hz
    apply η.eq_one_on_inner
    intro j _
    have hz' : ‖z - y‖ ≤ N := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hc : |z j - y j| ≤ N := by
      have h := (norm_le_pi_norm (z - y) j).trans hz'
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using h
    have hc' := abs_le.mp hc
    change y j - (N + 2) + 1 ≤ z j ∧ z j ≤ y j + (N + 2) - 1
    constructor <;> linarith [hc'.1, hc'.2]
  refine ⟨f, η.smooth.mul (slabSmoothPayoff_smooth i c R), ?_, ?_, ?_⟩
  · exact η.hasCompactSupport.mul_right
  · intro z
    have hp := slabSmoothPayoff_mem_Icc i c R z
    exact ⟨mul_nonneg (η.nonneg z) hp.1,
      (mul_le_mul_of_nonneg_right (η.le_one z) hp.1).trans (by simpa only [one_mul] using hp.2)⟩
  · intro z hz
    simp only [f, hplateau z hz, one_mul]

end EinsteinFull.Regeneration
