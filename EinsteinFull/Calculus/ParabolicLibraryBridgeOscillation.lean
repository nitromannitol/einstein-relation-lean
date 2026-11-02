import EllipticRegularity.Parabolic.Nash.WeakHarnackProof
import EinsteinFull.Calculus.ParabolicLibraryBridgeAffineH1

/-!
# Oscillation reduction from the weak Harnack inequality

In the unit cylinder `B₁ × (-1, 0]`, if `m ≤ u ≤ M` almost everywhere for a weak solution `u`, then
on `B_{1/2} × (-1/4, 0]` (which contains the top time) the oscillation is at most `(1 - η)(M - m)`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE

/-- Lower bound on `Q⁺` from the weak Harnack inequality, for a nonnegative weak solution that is
at least `c` on half of `Q⁻`. -/
theorem weakHarnack_lower (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ w : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) w →
      (∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
        0 ≤ w.toFun z) →
      ∀ c : ℝ, 0 < c →
      volume (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)) ≤
        2 * volume ({z | c ≤ w.toFun z} ∩
          (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2))) →
      ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)),
        η₀ * c ≤ w.toFun z := by
  obtain ⟨C, hC, hH⟩ := PDE.Ch5NashWeakHarnackProof.result d hd Lam hLam (1 / 2)
    (by norm_num) (by norm_num)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set pe : ℝ := 1 / 2 * ((d : ℝ) + 2) / d with hpe
  have hpe0 : 0 < pe := by positivity
  set κ : ℝ := (2 : ℝ) ^ (1 / pe) with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨(κ * C)⁻¹, by positivity, ?_⟩
  intro a ha w hw hnn c hc hmass
  have hH' := hH a ha w (solution_supersolution hw) hnn
  set Qm : Set (Vec d × ℝ) := euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioo (-3 / 4 : ℝ) (-1 / 2)
    with hQm
  have hQsub : Qm ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 := fun z hz =>
    ⟨euclideanBall_mono (by norm_num) (by norm_num) hz.1,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hQmeas : MeasurableSet Qm := (measurableSet_euclideanBall _ _).prod measurableSet_Ioo
  have hVfin : volume Qm ≠ ⊤ := by
    rw [hQm, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top _ (by norm_num)) (by simp)
  have hVpos : volume Qm ≠ 0 := by
    rw [hQm, Measure.volume_eq_prod, Measure.prod_prod]
    refine (ENNReal.mul_pos (volume_euclideanBall_pos _ (by norm_num)).ne' ?_).ne'
    simp <;> norm_num
  -- Markov-type lower bound for the Lp integral
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (w.toFun z) ^ pe)
      (volume.restrict Qm) :=
    ((w.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hQsub le_rfl)).aemeasurable.ennreal_ofReal).pow_const pe
  have hmk := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal c ^ pe)
  have hsetsub : {z | c ≤ w.toFun z} ⊆
      {z | ENNReal.ofReal c ^ pe ≤ ENNReal.ofReal (w.toFun z) ^ pe} := by
    intro z hz
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hz) hpe0.le
  have hS : volume ({z | c ≤ w.toFun z} ∩ Qm) ≤
      (volume.restrict Qm) {z | ENNReal.ofReal c ^ pe ≤ ENNReal.ofReal (w.toFun z) ^ pe} := by
    rw [Measure.restrict_apply' hQmeas]
    exact measure_mono (inter_subset_inter_left _ hsetsub)
  set I : ℝ≥0∞ := ∫⁻ z in Qm, ENNReal.ofReal (w.toFun z) ^ pe with hI
  have hε : ENNReal.ofReal c ^ pe ≤ 2 * ((volume Qm)⁻¹ * I) := by
    have h1 : ENNReal.ofReal c ^ pe * volume Qm ≤ 2 * I := by
      calc ENNReal.ofReal c ^ pe * volume Qm
          ≤ ENNReal.ofReal c ^ pe * (2 * volume ({z | c ≤ w.toFun z} ∩ Qm)) :=
            mul_le_mul' le_rfl hmass
        _ = 2 * (ENNReal.ofReal c ^ pe * volume ({z | c ≤ w.toFun z} ∩ Qm)) := by ring
        _ ≤ 2 * I := mul_le_mul' le_rfl (le_trans (mul_le_mul' le_rfl hS) hmk)
    calc ENNReal.ofReal c ^ pe
        = (volume Qm)⁻¹ * (ENNReal.ofReal c ^ pe * volume Qm) := by
          rw [mul_comm (ENNReal.ofReal c ^ pe), ← mul_assoc, ENNReal.inv_mul_cancel hVpos hVfin,
            one_mul]
      _ ≤ (volume Qm)⁻¹ * (2 * I) := mul_le_mul' le_rfl h1
      _ = 2 * ((volume Qm)⁻¹ * I) := by ring
  have hX : ENNReal.ofReal c ≤ ENNReal.ofReal κ *
      ((volume Qm)⁻¹ * I) ^ (1 / pe) := by
    have h2 := ENNReal.rpow_le_rpow hε (by positivity : (0 : ℝ) ≤ 1 / pe)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hpe0.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h2
    have e2 : (2 : ℝ≥0∞) ^ (1 / pe) = ENNReal.ofReal κ := by
      rw [hκ, ← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_nonneg (by norm_num)
        (by positivity)]
    rw [e2] at h2
    exact h2
  have hlow : ENNReal.ofReal c ≤ ENNReal.ofReal κ * (ENNReal.ofReal C *
      essInf (fun z => ENNReal.ofReal (w.toFun z))
        (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0))) :=
    hX.trans (mul_le_mul' le_rfl hH')
  have hnn' : ∀ᵐ z ∂(volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)),
      0 ≤ w.toFun z := by
    refine ae_restrict_of_ae_restrict_of_subset ?_ hnn
    exact prod_mono (euclideanBall_mono (by norm_num) (by norm_num))
      (Ioc_subset_Ioc_left (by norm_num))
  filter_upwards [ae_essInf_le (μ := volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ
    Ioc (-1 / 4 : ℝ) 0)) (f := fun z => ENNReal.ofReal (w.toFun z)), hnn'] with z hz hz0
  have h3 : ENNReal.ofReal c ≤ ENNReal.ofReal (κ * C * w.toFun z) := by
    refine hlow.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    exact mul_le_mul' le_rfl hz
  have h4 : c ≤ κ * C * w.toFun z :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  have hκC : 0 < κ * C := by positivity
  rw [inv_mul_le_iff₀ hκC]
  linarith

end EinsteinFull.ParabolicBridge
