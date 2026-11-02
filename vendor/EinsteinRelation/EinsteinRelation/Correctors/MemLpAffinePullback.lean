import Mathlib
import EinsteinRelation.External.AKMEnergyDensity

/-! # Lᵖ membership under affine pullback to the unit ball

Source: scaling to unit balls for the GT/Poisson estimates, `paper/main.tex:727-731`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

private theorem memLp_comp_affine_ball_norm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanNorm (c • x) = |c| * euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  have hsum : ∑ i, (c • x) i * (c • x) i = c ^ 2 * ∑ i, x i * x i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private theorem memLp_comp_affine_ball_measurableSet {d : ℕ} (c : Vec d) (r : ℝ) :
    MeasurableSet (External.AKM.ball c r) := by
  have hcont : Continuous fun z : Vec d => euclideanNorm (z - c) := by
    unfold euclideanNorm euclideanSq dot
    refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => ?_)
    fun_prop
  unfold External.AKM.ball
  exact measurableSet_lt hcont.measurable measurable_const

/-- Lᵖ membership under affine pullback to the unit ball. Source: scaling to unit balls for the GT/Poisson estimates, `paper/main.tex:727-731`. -/
theorem memLp_comp_affine_ball {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    {y : Vec d} {R : ℝ} (hR : 0 < R) {f : Vec d → F} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (External.AKM.ball y R))) :
    MemLp (fun x => f (y + R • x)) p (volume.restrict (External.AKM.ball 0 1)) := by
  have hcont : Measurable (fun x : Vec d => R • x) := by fun_prop
  have hTcont : Measurable (fun x : Vec d => y + R • x) := by fun_prop
  have hBm : MeasurableSet (External.AKM.ball y R) :=
    memLp_comp_affine_ball_measurableSet y R
  -- Volume of preimages under the affine map, for measurable sets
  have hpre : ∀ S : Set (Vec d), MeasurableSet S →
      volume ((fun x : Vec d => y + R • x) ⁻¹' S) =
        ENNReal.ofReal |(R ^ Module.finrank ℝ (Vec d))⁻¹| * volume S := by
    intro S hS
    have hA : MeasurableSet ((fun z : Vec d => y + z) ⁻¹' S) :=
      hS.preimage (by fun_prop)
    calc volume ((fun x : Vec d => y + R • x) ⁻¹' S)
        = volume ((fun x : Vec d => R • x) ⁻¹' ((fun z : Vec d => y + z) ⁻¹' S)) := rfl
      _ = Measure.map (fun x : Vec d => R • x) volume ((fun z : Vec d => y + z) ⁻¹' S) :=
          (Measure.map_apply hcont hA).symm
      _ = ENNReal.ofReal |(R ^ Module.finrank ℝ (Vec d))⁻¹| *
            volume ((fun z : Vec d => y + z) ⁻¹' S) := by
          rw [Measure.map_addHaar_smul volume hR.ne', Measure.smul_apply, smul_eq_mul]
      _ = ENNReal.ofReal |(R ^ Module.finrank ℝ (Vec d))⁻¹| * volume S := by
          rw [measure_preimage_add]
  -- The affine map carries the unit ball onto `ball y R`
  have hiff : ∀ x : Vec d, (y + R • x) ∈ External.AKM.ball y R ↔
      x ∈ External.AKM.ball (0 : Vec d) 1 := by
    intro x
    simp only [External.AKM.ball, Set.mem_setOf_eq, sub_zero, add_sub_cancel_left]
    rw [memLp_comp_affine_ball_norm_smul, abs_of_pos hR]
    constructor <;> intro h <;> nlinarith
  have hpreB : (fun x : Vec d => y + R • x) ⁻¹' External.AKM.ball y R =
      External.AKM.ball (0 : Vec d) 1 := by
    ext x
    exact hiff x
  have hmap : (volume.restrict (External.AKM.ball (0 : Vec d) 1)).map
      (fun x : Vec d => y + R • x) =
        ENNReal.ofReal |(R ^ Module.finrank ℝ (Vec d))⁻¹| •
          volume.restrict (External.AKM.ball y R) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hTcont hA, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (hTcont hA), Measure.restrict_apply hA, ← hpreB,
      ← Set.preimage_inter, hpre _ (hA.inter hBm)]
  have hf' : MemLp f p ((volume.restrict (External.AKM.ball (0 : Vec d) 1)).map
      (fun x : Vec d => y + R • x)) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hf'.comp_of_map hTcont.aemeasurable

end EinsteinRelation.Correctors
