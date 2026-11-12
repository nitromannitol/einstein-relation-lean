import Mathlib
import DeGiorgi.SobolevPoincare
import DeGiorgi.UnitBallApproximationCore.Rescaling
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-- The `L²` rescaling factor from `B_R(x₀)` to the unit ball is a positive finite constant
depending only on `R` and `d`. -/
private lemma exists_rescale_eLpNorm_factor {d : ℕ} {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 < R) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      eLpNorm (fun z => f (x₀ + R • z)) (ENNReal.ofReal 2)
          (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) =
        κ * eLpNorm f (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ R)) := by
  have h2 : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.2 (by norm_num)).ne'
  refine ⟨ENNReal.ofReal (R⁻¹ ^ ((d : ℝ) / (ENNReal.ofReal 2).toReal)),
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (inv_pos.2 hR) _)).ne',
    ENNReal.ofReal_ne_top, fun f => ?_⟩
  exact DeGiorgi.eLpNorm_rescale_to_unitBall hR h2 ENNReal.ofReal_ne_top

/-- Change of variables `x = x₀ + R • z` for an integral over the unit ball. -/
private lemma setIntegral_rescale_ball {d : ℕ} {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 < R) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, f (x₀ + R • z) =
      (R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))⁻¹ *
        ∫ x in Metric.ball x₀ R, f x := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (x₀ + x))
    (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) hR
  open scoped Pointwise in
  rw [show R • Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 =
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from by
    rw [smul_unitBall hR.ne']
    simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [hscale, smul_eq_mul]
  congr 1
  rw [show Metric.ball x₀ R = (x₀ + ·) '' Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from by
    simp]
  exact ((measurePreserving_add_left volume x₀).setIntegral_image_emb
    (MeasurableEquiv.addLeft x₀).measurableEmbedding f
    (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)).symm

/-- The average over the unit ball of a rescaled function is the average over `B_R(x₀)`. -/
private lemma setAverage_rescale_ball {d : ℕ} {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 < R) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, u (x₀ + R • y) ∂volume =
      ⨍ y in Metric.ball x₀ R, u y ∂volume := by
  rw [setAverage_eq, setAverage_eq, setIntegral_rescale_ball (x₀ := x₀) hR u]
  simp only [measureReal_def, smul_eq_mul]
  rw [Measure.addHaar_ball_of_pos volume x₀ hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hR.le _)]
  ring

/-- Poincaré inequality on `B_R(x₀)` for the exponent `q = ENNReal.ofReal 2`, obtained by
rescaling to the unit ball. -/
private lemma poincare_ball_W1p_aux {d : ℕ} [NeZero d] {x₀ : EuclideanSpace ℝ (Fin d)}
    {R : ℝ} (hR : 0 < R) {q : ℝ≥0∞} (hq : q = ENNReal.ofReal 2)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : DeGiorgi.MemW1pWitness q u (Metric.ball x₀ R)) :
    eLpNorm (fun x => u x - ⨍ y in Metric.ball x₀ R, u y ∂volume) q
        (volume.restrict (Metric.ball x₀ R)) ≤
      ENNReal.ofReal (DeGiorgi.C_poinc_val d * R) *
        eLpNorm (fun x => ‖hw.weakGrad x‖) q (volume.restrict (Metric.ball x₀ R)) := by
  subst hq
  obtain ⟨κ, hκ0, hκtop, hκ⟩ := exists_rescale_eLpNorm_factor (x₀ := x₀) hR
  have havg := setAverage_rescale_ball (x₀ := x₀) hR u
  have hLHS : eLpNorm (fun z => u (x₀ + R • z) -
      ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, u (x₀ + R • y) ∂volume)
      (ENNReal.ofReal 2) (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) =
      κ * eLpNorm (fun x => u x - ⨍ y in Metric.ball x₀ R, u y ∂volume)
        (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ R)) := by
    rw [havg]
    exact hκ (fun x => u x - ⨍ y in Metric.ball x₀ R, u y ∂volume)
  have hconst : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      eLpNorm (fun z => R * f z) (ENNReal.ofReal 2)
          (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) =
        ENNReal.ofReal R * eLpNorm f (ENNReal.ofReal 2)
          (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
    intro f
    rw [← Real.enorm_eq_ofReal hR.le]
    exact eLpNorm_const_smul R f _ _
  have hgrad : ∀ z : EuclideanSpace ℝ (Fin d),
      ‖(hw.rescale_to_unitBall hR).weakGrad z‖ = R * ‖hw.weakGrad (x₀ + R • z)‖ := by
    intro z
    show ‖R • hw.weakGrad (x₀ + R • z)‖ = R * ‖hw.weakGrad (x₀ + R • z)‖
    rw [norm_smul, Real.norm_of_nonneg hR.le]
  have hgrad_fun : (fun z => ‖(hw.rescale_to_unitBall hR).weakGrad z‖) =
      fun z => R * ‖hw.weakGrad (x₀ + R • z)‖ := funext hgrad
  have hgrad_eq : eLpNorm (fun z => ‖(hw.rescale_to_unitBall hR).weakGrad z‖) (ENNReal.ofReal 2)
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) =
      ENNReal.ofReal R * (κ * eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal 2)
        (volume.restrict (Metric.ball x₀ R))) := by
    rw [hgrad_fun, hconst (fun z => ‖hw.weakGrad (x₀ + R • z)‖),
      hκ (fun x => ‖hw.weakGrad x‖)]
  have hpoinc : eLpNorm (fun z => u (x₀ + R • z) -
      ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, u (x₀ + R • y) ∂volume)
      (ENNReal.ofReal 2) (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) ≤
      ENNReal.ofReal (DeGiorgi.C_poinc_val d) *
        eLpNorm (fun z => ‖(hw.rescale_to_unitBall hR).weakGrad z‖) (ENNReal.ofReal 2)
          (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    DeGiorgi.poincare_unitBall_W1p_public (d := d) (p := 2) (by norm_num)
      (hw.rescale_to_unitBall hR)
  have hkey : κ * eLpNorm (fun x => u x - ⨍ y in Metric.ball x₀ R, u y ∂volume)
      (ENNReal.ofReal 2) (volume.restrict (Metric.ball x₀ R)) ≤
      κ * (ENNReal.ofReal (DeGiorgi.C_poinc_val d) * ENNReal.ofReal R *
        eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal 2)
          (volume.restrict (Metric.ball x₀ R))) := by
    rw [← hLHS]
    refine le_trans hpoinc (le_of_eq ?_)
    rw [hgrad_eq]
    ring
  rw [ENNReal.ofReal_mul' hR.le]
  exact (ENNReal.mul_le_mul_iff_right hκ0 hκtop).1 hkey

/-- Poincaré inequality on a ball `B_R(x₀)` for a `W^{1,2}` witness: the `L²` oscillation of `u`
about its mean is bounded by `C_poinc_val d * R` times the `L²` norm of its weak gradient. -/
theorem poincare_ball_W1p {d : ℕ} [NeZero d] {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ}
    (hR : 0 < R) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u (Metric.ball x₀ R)) :
    eLpNorm (fun x => u x - ⨍ y in Metric.ball x₀ R, u y ∂volume) 2
        (volume.restrict (Metric.ball x₀ R)) ≤
      ENNReal.ofReal (DeGiorgi.C_poinc_val d * R) *
        eLpNorm (fun x => ‖hw.weakGrad x‖) 2 (volume.restrict (Metric.ball x₀ R)) := by
  exact poincare_ball_W1p_aux hR (by simp) hw

end EinsteinRelation.Correctors
