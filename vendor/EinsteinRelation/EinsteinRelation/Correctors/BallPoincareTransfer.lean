import EinsteinRelation.Correctors.InteriorGradientTransfer

/-!
# Normalization of the Euclidean ball Poincaré inequality

Source: `paper/main.tex:722-729`. GT (7.45), p. 164, uses two
unnormalized norms. The canonical unit energy uses a normalized gradient
norm. This file proves their conversion and discharges the existing
`UnitBallPoincare` interface from the proposed deterministic GT contract.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- Euclidean unit balls have positive, finite coordinate Lebesgue volume.
The norm of the coordinate carrier is used only to bound this Euclidean ball. -/
theorem unitBall_volume_pos_finite (d : ℕ) :
    0 < volume.real (ball (0 : Vec d) 1) := by
  have hU : IsOpen (ball (0 : Vec d) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hne : (ball (0 : Vec d) 1).Nonempty := by
    refine ⟨0, ?_⟩
    simp [ball, euclideanNorm, euclideanSq, dot]
  have hfin : volume (ball (0 : Vec d) 1) ≠ ⊤ := by
    have hcompact : IsCompact
        ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) '' Metric.closedBall 0 1) :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).image
        (PiLp.continuous_ofLp 2 _)
    apply ne_top_of_le_ne_top (hcompact.measure_ne_top (μ := volume))
    apply measure_mono
    intro x hx
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) - 0‖ ≤ 1
    rw [sub_zero, EuclideanSpace.norm_eq]
    have hnorm : (∑ j : Fin d, ‖x j‖ ^ 2) = euclideanSq x := by
      simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]
    rw [hnorm]
    exact le_of_lt (by simpa only [ball, Set.mem_setOf_eq, sub_zero,
      euclideanNorm] using hx)
  exact ENNReal.toReal_pos (hU.measure_pos volume hne).ne' hfin

/-- Conversion of the unnormalized GT Poincaré inequality to the exact
unit-ball interface. The factor `sqrt |B₁|` depends only on the dimension. -/
theorem unitBallPoincare_of_gt (hP : BallPoincareEstimate) : UnitBallPoincare := by
  intro d hd
  obtain ⟨C, hC, hest⟩ := hP d hd
  let V : ℝ := volume.real (ball (0 : Vec d) 1)
  have hV : 0 < V := unitBall_volume_pos_finite d
  refine ⟨C * Real.sqrt V, mul_pos hC (Real.sqrt_pos.2 hV), ?_⟩
  intro u g hu hg hgrad hmean
  have hzero : (⨍ x in ball (0 : Vec d) 1, u x ∂volume) = 0 := by
    simp only [average_eq, hmean, smul_zero]
  have h := hest 0 1 zero_lt_one u g hu hg hgrad
  simp only [hzero, sub_zero, mul_one] at h
  have hnorm : Real.sqrt (∫ x in ball (0 : Vec d) 1, euclideanSq (g x) ∂volume) =
      Real.sqrt V * Real.sqrt (⨍ x in ball (0 : Vec d) 1, euclideanSq (g x) ∂volume) := by
    simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change Real.sqrt _ = Real.sqrt V * Real.sqrt (V⁻¹ * _)
    rw [← Real.sqrt_mul hV.le, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
  rw [hnorm, ← mul_assoc] at h
  exact h

end EinsteinRelation.Correctors

