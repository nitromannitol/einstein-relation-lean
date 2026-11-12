import EinsteinRelation.Correctors.AverageCenteringBounds
import EinsteinRelation.Correctors.MeasurableLocalMajorants
import EinsteinRelation.Correctors.ProbabilityAverageIntegration
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import EinsteinRelation.Correctors.SpatialBallVolume
open MeasureTheory
open scoped ENNReal
open Matrix
noncomputable section
namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:733-745`. Measurable tensor local majorants
in one common gauge control the entrywise mean-centered Frobenius moment. -/
theorem centered_tensor_moment_of_local_measurable_majorants
    (d : ℕ) (hd : 0 < d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (S : Ω → Vec d → Mat d) (c : Ω → Mat d)
      (hSm : Measurable (Function.uncurry S)) (hcm : Measurable c)
      (z : Vec d) (R : ℝ) (hR : 0 < R) (B : ℝ),
      (∀ᵐ ω ∂P, ∀ j k, Integrable (fun x => S ω x j k)
        (volume.restrict (External.AKM.ball z R))) →
      (∀ x ∈ External.AKM.ball z R, ∃ M : Ω → ℝ,
        AEMeasurable M P ∧ (∀ ω, 0 ≤ M ω) ∧
        (∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂P) ≤ ENNReal.ofReal B ∧
        ∀ᵐ ω ∂P, ∀ᵐ y ∂volume.restrict (External.AKM.ball x (1 / 4)),
          frobeniusNorm (S ω y - c ω) ≤ M ω) →
      (∫⁻ ω, (⨍⁻ x in External.AKM.ball z R,
        ENNReal.ofReal (frobeniusNorm (S ω x - Matrix.of (fun j k =>
          ⨍ y in External.AKM.ball z R, S ω y j k ∂volume)) ^ p) ∂volume) ∂P) ≤
        ENNReal.ofReal (C * max B 0) := by
  classical
  have hdim : 0 < (d : ℝ) := by exact_mod_cast hd
  refine ⟨(d : ℝ) ^ p * 2 ^ p, by positivity, ?_⟩
  intro Ω _ P _ S c hSm hcm z R hR B hint hlocal
  let U := External.AKM.ball z R
  have hU : IsOpen U := by
    unfold U External.AKM.ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict_euclideanBall z R hR
  letI : NeZero μ := ⟨by
    intro h
    have hh : μ Set.univ = 0 := by rw [h]; simp
    have hpos := (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).1
    exact hpos.ne' (by simpa [μ, U, volume_euclideanBall_center] using hh)⟩
  let F : Ω → Vec d → ℝ≥0∞ := fun ω x => ENNReal.ofReal (frobeniusNorm (S ω x - c ω) ^ p)
  have hFm : Measurable (Function.uncurry F) := by
    have he (j k : Fin d) : Measurable (fun q : Ω × Vec d => S q.1 q.2 j k - c q.1 j k) :=
      ((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hSm).sub
        (((show Continuous (fun A : Mat d => A j k) by fun_prop).measurable.comp hcm).comp measurable_fst)
    have hnorm : Measurable (fun q : Ω × Vec d => frobeniusNorm (S q.1 q.2 - c q.1)) := by
      unfold frobeniusNorm frobeniusSq
      apply Measurable.sqrt
      exact Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
        (he j k).mul (he j k)
    exact (hnorm.pow_const p).ennreal_ofReal
  have hb : (∫⁻ ω, ⨍⁻ x in U, F ω x ∂volume ∂P) ≤ ENNReal.ofReal B := by
    apply lintegral_laverage_le_of_measurable_local_majorants P volume U hU.measurableSet
      (by simpa [U, volume_euclideanBall_center] using (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).1.ne')
      (by simpa [U, volume_euclideanBall_center] using (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne) F hFm _
    intro x hx
    obtain ⟨M, hm, hm0, hmB, hmb⟩ := hlocal x hx
    refine ⟨External.AKM.ball x (1 / 4), ?_, ?_,
      (fun ω => ENNReal.ofReal (M ω ^ p)), (hm.pow_const p).ennreal_ofReal, hmB, ?_⟩
    · unfold External.AKM.ball euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const
    · simp [External.AKM.ball, euclideanNorm, euclideanSq, dot]
    · filter_upwards [hmb] with ω hω
      filter_upwards [hω] with y hy
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Real.sqrt_nonneg _) hy (by linarith))
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) * (⨍⁻ x in U, F ω x ∂volume) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hint] with ω hω
      exact laverage_frobenius_sub_average_rpow_le μ hd (S ω) (c ω) p hp
        (hSm.of_uncurry_left (x := ω)) hω
    _ = ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) * (∫⁻ ω, ⨍⁻ x in U, F ω x ∂volume ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) * ENNReal.ofReal B := mul_le_mul_right hb _
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
end EinsteinRelation.Correctors
