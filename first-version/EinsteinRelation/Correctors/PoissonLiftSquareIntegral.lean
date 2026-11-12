import EinsteinRelation.Correctors.PoissonLiftLocalL2
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import Mathlib.MeasureTheory.Integral.Prod

/-! Source: `paper/main.tex:735-739`. The explicit dimensional lift has
an L² bound with constants depending only on the original dimension. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Integrating a height-independent square over the lifted unit ball
costs at most the length of its containing height interval. -/
theorem integral_sq_poissonLiftBase_le {d : ℕ} (u : Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (ball 0 1))) :
    (∫ x in ball (0 : Vec (d + 1)) 1, |u (poissonLiftBase x)| ^ 2 ∂volume) ≤
      2 * (∫ x in ball (0 : Vec d) 1, |u x| ^ 2 ∂volume) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hb : MeasurableSet (ball (0 : Vec d) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  let s : Set (ℝ × Vec d) := Set.Icc (-1) 1 ×ˢ ball 0 1
  have hs : MeasurableSet s := measurableSet_Icc.prod hb
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => ℝ) 0).restrict_preimage hs
  have hp : MemLp (fun p : ℝ × Vec d => u p.2) 2
      ((volume : Measure (ℝ × Vec d)).restrict s) := by
    simpa only [Measure.prod_restrict] using
      hu.comp_snd (volume.restrict (Set.Icc (-1 : ℝ) 1))
  have hi : Integrable (fun x : Vec (d + 1) => |u (poissonLiftBase x)| ^ 2)
      (volume.restrict (e ⁻¹' s)) := by
    simpa only [sq_abs] using (hp.comp_measurePreserving he).integrable_sq
  have hsub : ball (0 : Vec (d + 1)) 1 ⊆ e ⁻¹' s := by
    intro x hx
    change x 0 ∈ Set.Icc (-1) 1 ∧ poissonLiftBase x ∈ ball (0 : Vec d) 1
    have hx' : euclideanNorm x < 1 := by simpa only [ball, sub_zero] using hx
    refine ⟨abs_le.mp ((Regeneration.coordinate_abs_le_euclideanNorm x 0).trans hx'.le), ?_⟩
    simpa only [ball, sub_zero] using (euclideanNorm_poissonLiftBase_le x).trans_lt hx'
  calc
    _ ≤ ∫ x in e ⁻¹' s, |u (poissonLiftBase x)| ^ 2 ∂volume :=
      setIntegral_mono_set hi (ae_of_all _ fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall hsub)
    _ = ∫ p in s, |u p.2| ^ 2 ∂volume :=
      he.integral_comp' (fun p : ℝ × Vec d => |u p.2| ^ 2)
    _ = 2 * (∫ x in ball (0 : Vec d) 1, |u x| ^ 2 ∂volume) := by
      calc
        _ = (∫ t in Set.Icc (-1 : ℝ) 1, (1 : ℝ) ∂volume) *
            (∫ x in ball (0 : Vec d) 1, |u x| ^ 2 ∂volume) := by
          simpa only [one_mul, s] using
            (setIntegral_prod_mul (fun _ : ℝ => (1 : ℝ))
              (fun x : Vec d => |u x| ^ 2) (Set.Icc (-1) 1) (ball 0 1))
        _ = _ := by norm_num

/-- The augmented potential has a dimension-only L² bound on the actual
Euclidean unit ball in one higher dimension. -/
theorem integral_sq_poissonLift_le {d : ℕ} (u : Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (ball 0 1))) (M : ℝ) :
    (∫ x in ball (0 : Vec (d + 1)) 1, |poissonLiftPotential u M x| ^ 2 ∂volume) ≤
      4 * (∫ x in ball (0 : Vec d) 1, |u x| ^ 2 ∂volume) +
        4 * M ^ 2 * (2 : ℝ) ^ d := by
  letI := isFiniteMeasure_restrict_euclideanBall (0 : Vec (d + 1)) 1 (by norm_num)
  have hi : Integrable (fun x : Vec (d + 1) => |u (poissonLiftBase x)| ^ 2)
      (volume.restrict (ball 0 1)) := by
    simpa only [sq_abs] using
      (memLp_poissonLiftBase_on_ball u 1 (by norm_num) hu).integrable_sq
  have hsub : ball (0 : Vec (d + 1)) 1 ⊆ Metric.closedBall 0 1 := by
    intro x hx
    have hx' : euclideanNorm x < 1 := by simpa only [ball, sub_zero] using hx
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro j
    simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using
      (Regeneration.coordinate_abs_le_euclideanNorm x j).trans hx'.le
  have hmass : volume.real (ball (0 : Vec (d + 1)) 1) ≤ 2 * (2 : ℝ) ^ d := by
    have h := measureReal_mono (μ := (volume : Measure (Vec (d + 1))))
      hsub (isCompact_closedBall (0 : Vec (d + 1)) 1).measure_ne_top
    simpa only [measureReal_def, Real.volume_pi_closedBall 0 (by norm_num : (0 : ℝ) ≤ 1),
      Fintype.card_fin, mul_one, one_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 ^ (d + 1)),
      pow_succ, mul_comm,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * 2 ^ d)] using h
  have hb : MeasurableSet (ball (0 : Vec (d + 1)) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hbound : (∫ x in ball (0 : Vec (d + 1)) 1,
      |poissonLiftPotential u M x| ^ 2 ∂volume) ≤
      2 * (∫ x in ball (0 : Vec (d + 1)) 1,
        |u (poissonLiftBase x)| ^ 2 ∂volume) +
        2 * M ^ 2 * volume.real (ball (0 : Vec (d + 1)) 1) := by
    calc
      _ ≤ ∫ x in ball (0 : Vec (d + 1)) 1,
          2 * |u (poissonLiftBase x)| ^ 2 + 2 * M ^ 2 ∂volume := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          ((hi.const_mul 2).add (integrable_const _))
        filter_upwards [ae_restrict_mem hb] with x hx
        have hx' : euclideanNorm x < 1 := by simpa only [ball, sub_zero] using hx
        have hxabs := (Regeneration.coordinate_abs_le_euclideanNorm x 0).trans hx'.le
        have hx2 : (x 0) ^ 2 ≤ 1 := by nlinarith [sq_abs (x 0), abs_nonneg (x 0)]
        simp only [poissonLiftPotential, sq_abs, Pi.add_apply]
        nlinarith [sq_nonneg (u (poissonLiftBase x) - M * x 0),
          mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hx2)]
      _ = _ := by
        rw [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul]
        simp only [setIntegral_const, smul_eq_mul, mul_comm (volume.real _) (2 * M ^ 2)]
  have hbase := integral_sq_poissonLiftBase_le u hu
  nlinarith [mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2 * M ^ 2)]

end EinsteinRelation.Correctors
