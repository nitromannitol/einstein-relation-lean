import EinsteinRelation.Correctors.HarmonicRepresentativeNormalization
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Centered amplitudes of paired harmonic functions

Source: `paper/main.tex:862–873`. GT local boundedness and ball Poincaré
control oscillation about the ball mean. Both literature propositions are
explicit hypotheses; their presence in this theorem does not freeze them
or prove the missing literature contracts.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- Euclidean balls are open in the actual coordinate carrier.
Source: `paper/main.tex:862–866`. -/
theorem paired_isOpen_ball {d : ℕ} (y : Vec d) (R : ℝ) : IsOpen (ball y R) := by
  unfold ball euclideanNorm euclideanSq dot
  exact isOpen_lt (by fun_prop) continuous_const

/-- Positive-radius Euclidean balls have positive finite coordinate volume.
Source: `paper/main.tex:862–866`. -/
theorem paired_ball_volume_pos_finite {d : ℕ} {R : ℝ} (hR : 0 < R) :
    0 < volume.real (ball (0 : Vec d) R) := by
  have hne : (ball (0 : Vec d) R).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [ball, euclideanNorm, euclideanSq, dot] using hR
  have hcompact : IsCompact
      ((WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) '' Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).image
      (PiLp.continuous_ofLp 2 _)
  have hsub : ball (0 : Vec d) R ⊆
      (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) '' Metric.closedBall 0 R := by
    intro x hx
    refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
    change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) - 0‖ ≤ R
    rw [sub_zero, ← TimeChange.euclideanNorm_eq_norm_toLp]
    exact le_of_lt (by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hx)
  exact ENNReal.toReal_pos
    ((paired_isOpen_ball 0 R).measure_pos volume hne).ne'
    (ne_top_of_le_ne_top (hcompact.measure_ne_top (μ := volume)) (measure_mono hsub))

/-- Deterministic oscillation estimate for the continuous harmonic
representative. The constant is chosen before the coefficient, radius and
solution. Source: `paper/main.tex:862–866`; GT (8.46), p. 194, and (7.45),
p. 164. The norms on the right are unnormalized at this stage. -/
theorem paired_harmonic_ball_oscillation_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {d : ℕ} (hd : 2 ≤ d) {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (a : Vec d → Mat d) (u : Vec d → ℝ) (G : Vec d → Vec d),
        EllipticBound (ball 0 (2 * R)) a lam Λ →
        WeakSolution (ball 0 (2 * R)) a u G →
        ContinuousOn u (ball 0 R) →
        ∀ x ∈ ball 0 R,
          |u x - ⨍ y in ball 0 (2 * R), u y ∂volume| ≤
            C * R ^ (-(d : ℝ) / 2) * (2 * R) *
              Real.sqrt (∫ y in ball 0 (2 * R), euclideanSq (G y) ∂volume) := by
  obtain ⟨CB, hCB, hB⟩ := h817 d hd lam Λ 2 hlam hΛ (by norm_num)
  obtain ⟨CP, hCP, hPoincare⟩ := hP d hd
  refine ⟨CB * CP, mul_pos hCB hCP, ?_⟩
  intro R hR a u G hell hweak hcont
  have hvol := paired_ball_volume_pos_finite (d := d) (mul_pos (by norm_num : (0 : ℝ) < 2) hR)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (2 * R))) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hvol).2.ne
  let c := ⨍ y in ball 0 (2 * R), u y ∂volume
  have hcenter := weakSolution_sub_const hweak c
  have hbound := hB (ball 0 (2 * R)) (paired_isOpen_ball 0 (2 * R)) a hell
    (fun x => u x - c) G hcenter 0 R hR Set.Subset.rfl (by
      simpa using hcenter.1)
  have hpoint : ∀ x ∈ ball 0 R,
      |u x - c| ≤ CB * R ^ (-(d : ℝ) / 2) *
        Real.sqrt (∫ y in ball 0 (2 * R), |u y - c| ^ 2 ∂volume) := by
    apply abs_le_on_open_of_ae (paired_isOpen_ball 0 R) (hcont.sub continuousOn_const)
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using! hbound
  have hpc := hPoincare 0 (2 * R) (by positivity) u G
    hweak.1 hweak.2.1 hweak.2.2.1
  intro x hx
  calc
    |u x - c| ≤ CB * R ^ (-(d : ℝ) / 2) *
        Real.sqrt (∫ y in ball 0 (2 * R), |u y - c| ^ 2 ∂volume) := hpoint x hx
    _ ≤ CB * R ^ (-(d : ℝ) / 2) *
        (CP * (2 * R) * Real.sqrt (∫ y in ball 0 (2 * R), euclideanSq (G y) ∂volume)) :=
      mul_le_mul_of_nonneg_left hpc (mul_nonneg hCB.le (Real.rpow_nonneg hR.le _))
    _ = _ := by ring

end EinsteinRelation.Correctors
