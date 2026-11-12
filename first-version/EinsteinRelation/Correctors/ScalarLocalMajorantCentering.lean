import EinsteinRelation.Correctors.MeasurableLocalMajorants
import EinsteinRelation.Correctors.PairwiseCentering
import EinsteinRelation.Correctors.TwoMajorantMoments
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import EinsteinRelation.Correctors.SpatialBallVolume
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory
open scoped ENNReal
open Set
namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:718-723,743-745`. Local measurable random
majorants in one common gauge control the centered scalar moment, even
when only the centered representative is jointly measurable. -/
theorem centered_scalar_moment_of_local_measurable_majorants
    (d : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (f v : Ω → Vec d → ℝ) (c b : Ω → ℝ)
      (hfm : Measurable (Function.uncurry f))
      (z : Vec d) (R : ℝ) (hR : 0 < R) (B : ℝ),
      (∀ᵐ ω ∂P, Integrable (f ω)
        (volume.restrict (External.AKM.ball z R))) →
      (∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f ω x = v ω x + b ω) →
      (∀ x ∈ External.AKM.ball z R, ∃ M : Ω → ℝ,
        AEMeasurable M P ∧ (∀ ω, 0 ≤ M ω) ∧
        (∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂P) ≤ ENNReal.ofReal B ∧
        ∀ᵐ ω ∂P, ∀ᵐ y ∂volume.restrict (External.AKM.ball x (1 / 4)),
          |v ω y - c ω| ≤ M ω) →
      (∫⁻ ω, (⨍⁻ x in External.AKM.ball z R,
        ENNReal.ofReal (|f ω x -
          (⨍ y in External.AKM.ball z R, f ω y ∂volume)| ^ p) ∂volume) ∂P) ≤
        ENNReal.ofReal (C * max B 0) := by
  classical
  refine ⟨2 ^ p * (2 ^ p * 2), by positivity, ?_⟩
  intro Ω _ P _ f v c b hfm z R hR B hint hgauge hlocal
  let U := External.AKM.ball z R
  have hU : IsOpen U := by
    unfold U External.AKM.ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict_euclideanBall z R hR
  letI : NeZero μ := ⟨by
    intro h
    have hh : μ Set.univ = 0 := by rw [h]; simp
    have hp := (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).1
    exact hp.ne' (by simpa [μ, U, volume_euclideanBall_center] using hh)⟩
  let ν := (μ Set.univ)⁻¹ • μ
  have hνac : ν ≪ volume := Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  have hνrest : ν.restrict U = ν := by simp [ν, μ, Measure.restrict_smul, Measure.restrict_restrict hU.measurableSet]
  have hprodrest : (ν.prod ν).restrict (U ×ˢ U) = ν.prod ν := by
    rw [← Measure.prod_restrict, hνrest]
  let F : Ω → (Vec d × Vec d) → ℝ≥0∞ := fun ω q => ENNReal.ofReal (|f ω q.1 - f ω q.2| ^ p)
  have hFm : Measurable (Function.uncurry F) := by
    exact ((continuous_abs.measurable.comp ((hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).sub
      (hfm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))).pow_const p).ennreal_ofReal
  let D := 2 ^ p * (max B 0 + max B 0)
  have hD : 0 ≤ D := by positivity
  have hb : (∫⁻ ω, ⨍⁻ q in U ×ˢ U, F ω q ∂ν.prod ν ∂P) ≤ ENNReal.ofReal D := by
    apply lintegral_laverage_le_of_measurable_local_majorants P (ν.prod ν)
      (U ×ˢ U) (hU.prod hU).measurableSet
      (by rw [← Measure.restrict_apply_univ, hprodrest]; simp)
      (by rw [← Measure.restrict_apply_univ, hprodrest]; simp) F hFm (ENNReal.ofReal D)
    intro q hq
    obtain ⟨M, hm, hm0, hmB, hmb⟩ := hlocal q.1 hq.1
    obtain ⟨N, hn, hn0, hnB, hnb⟩ := hlocal q.2 hq.2
    let V := External.AKM.ball q.1 (1 / 4)
    let W := External.AKM.ball q.2 (1 / 4)
    have hVo : IsOpen V := by
      unfold V External.AKM.ball euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const
    have hWo : IsOpen W := by
      unfold W External.AKM.ball euclideanNorm euclideanSq dot
      exact isOpen_lt (by fun_prop) continuous_const
    refine ⟨V ×ˢ W, hVo.prod hWo, ⟨?_, ?_⟩,
      (fun ω => ENNReal.ofReal ((M ω + N ω) ^ p)), ((hm.add hn).pow_const p).ennreal_ofReal, ?_, ?_⟩
    · simp [V, External.AKM.ball, euclideanNorm, euclideanSq, dot]
    · simp [W, External.AKM.ball, euclideanNorm, euclideanSq, dot]
    · have h := lintegral_rpow_le_of_two_majorants P
        (fun ω => M ω + N ω) M N 1 p B B (by norm_num) (by linarith) hm0 hn0 hm hn
        (ae_of_all _ fun ω => ⟨add_nonneg (hm0 ω) (hn0 ω), by simp⟩) hmB hnB
      simpa only [Real.one_rpow, one_mul, D] using h
    · filter_upwards [hmb, hnb, hgauge] with ω hM hN hg
      have ha : ∀ᵐ x ∂ν.restrict V, |f ω x - (c ω + b ω)| ≤ M ω := by
        filter_upwards [((hνac.restrict V).ae_le hM),
          (hνac.restrict V).ae_le (ae_restrict_of_ae hg)] with x hx hgx
        simpa [hgx, add_sub_add_right_eq_sub] using hx
      have hb : ∀ᵐ y ∂ν.restrict W, |f ω y - (c ω + b ω)| ≤ N ω := by
        filter_upwards [((hνac.restrict W).ae_le hN),
          (hνac.restrict W).ae_le (ae_restrict_of_ae hg)] with y hy hgy
        simpa [hgy, add_sub_add_right_eq_sub] using hy
      rw [← Measure.prod_restrict]
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
        ((hfm.of_uncurry_left (x := ω)).comp measurable_fst |>.sub
          ((hfm.of_uncurry_left (x := ω)).comp measurable_snd) |> continuous_abs.measurable.comp |>.pow_const p |>.ennreal_ofReal)
        measurable_const)).mpr
      filter_upwards [ha] with x hx
      filter_upwards [hb] with y hy
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
      calc
        |f ω x - f ω y| = |(f ω x - (c ω + b ω)) - (f ω y - (c ω + b ω))| := by congr 1; ring
        _ ≤ |f ω x - (c ω + b ω)| + |f ω y - (c ω + b ω)| := abs_sub _ _
        _ ≤ _ := add_le_add hx hy
  have hpair : (∫⁻ ω, ∫⁻ y, ∫⁻ x, F ω (x,y) ∂ν ∂ν ∂P) ≤ ENNReal.ofReal D := by
    convert hb using 1
    apply lintegral_congr
    intro ω
    rw [hprodrest, laverage_eq_lintegral]
    exact (MeasureTheory.lintegral_prod_symm _ (hFm.of_uncurry_left (x := ω)).aemeasurable).symm
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ p) * (∫⁻ y, ∫⁻ x, F ω (x,y) ∂ν ∂ν) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hint] with ω hω
      exact lintegral_centered_rpow_le_pair_difference ν (f ω) p hp hω.to_average
    _ = ENNReal.ofReal (2 ^ p) * (∫⁻ ω, ∫⁻ y, ∫⁻ x, F ω (x,y) ∂ν ∂ν ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ p) * ENNReal.ofReal D := mul_le_mul_right hpair _
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; dsimp [D]; ring
end EinsteinRelation.Correctors
