import EinsteinRelation.External.GantertSection7Support
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped ENNReal NNReal
namespace EinsteinRelation.External.GantertSection7Support

/-- The physical force weight satisfies `w(x - a) = w(x) * w(-a)`. -/
theorem physicalForceWeight_sub {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (x a : Vec d) :
    physicalForceWeight hd lam (x - a) =
      physicalForceWeight hd lam x * physicalForceWeight hd lam (-a) := by
  dsimp [physicalForceWeight]
  calc
    Real.exp (2 * lam * (x - a) (firstCoordinateIndex hd))
        = Real.exp (2 * lam * (x (firstCoordinateIndex hd) - a (firstCoordinateIndex hd))) := rfl
    _ = Real.exp ((2 * lam * x (firstCoordinateIndex hd)) +
        (-(2 * lam * a (firstCoordinateIndex hd)))) := by ring
    _ = Real.exp (2 * lam * x (firstCoordinateIndex hd)) *
        Real.exp (-(2 * lam * a (firstCoordinateIndex hd))) := by rw [Real.exp_add]
    _ = Real.exp (2 * lam * x (firstCoordinateIndex hd)) *
        Real.exp (2 * lam * (-a (firstCoordinateIndex hd))) := by ring
    _ = physicalForceWeight hd lam x * physicalForceWeight hd lam (-a) := rfl

/-- Source `paper/main.tex:406–408`: translating a function preserves membership in the actual exponential-weighted Lp space. -/
theorem memLp_comp_add_left_physicalForceMeasure_iff {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ) (a : Vec d) {E : Type*} [NormedAddCommGroup E]
    (f : Vec d → E) (p : ℝ≥0∞) :
    MemLp (fun y => f (a + y)) p (physicalForceMeasure hd lam) ↔
      MemLp f p (physicalForceMeasure hd lam) := by
  let μ := physicalForceMeasure hd lam
  let w : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (physicalForceWeight hd lam x)
  have hw_meas : Measurable w :=
    ENNReal.measurable_ofReal.comp (physicalForceWeight_continuous hd lam).measurable
  let T : MeasurableEquiv (Vec d) (Vec d) := MeasurableEquiv.addLeft a
  have hT_meas : Measurable (T : Vec d → Vec d) := T.measurable
  have hT_symm_meas : Measurable (T.symm : Vec d → Vec d) := T.symm.measurable
  have hvol_map : Measure.map (T : Vec d → Vec d) volume = volume := by
    simpa using (measurePreserving_add_left volume a).map_eq
  have h_map_eq : Measure.map (T : Vec d → Vec d) μ =
      ENNReal.ofReal (physicalForceWeight hd lam (-a)) • μ := by
    dsimp [μ, physicalForceMeasure]
    ext s hs
    have hs' : MeasurableSet (T ⁻¹' s) := hT_meas hs
    calc
      (Measure.map (T : Vec d → Vec d) (volume.withDensity w)) s =
          (volume.withDensity w) (T ⁻¹' s) := by
        rw [Measure.map_apply hT_meas hs]
      _ = ∫⁻ y in T ⁻¹' s, w y ∂volume := by rw [withDensity_apply _ hs']
      _ = ∫⁻ x in s, w (T.symm x) ∂(Measure.map (T : Vec d → Vec d) volume) := by
        simpa [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using
          (setLIntegral_map hs (hw_meas.comp hT_symm_meas) hT_meas).symm
      _ = ∫⁻ x in s, w (T.symm x) ∂volume := by rw [hvol_map]
      _ = ∫⁻ x in s, (w x * ENNReal.ofReal (physicalForceWeight hd lam (-a))) ∂volume := by
        apply setLIntegral_congr_fun hs
        intro x hx
        have hTsymm_eq : T.symm x = x - a := by
          dsimp [T]
          simp [add_comm, sub_eq_add_neg]
        dsimp [w]
        rw [hTsymm_eq, physicalForceWeight_sub hd lam x a]
        simp [ENNReal.ofReal_mul (physicalForceWeight_pos hd lam x).le]
      _ = ENNReal.ofReal (physicalForceWeight hd lam (-a)) *
          ∫⁻ x in s, w x ∂volume := by
        rw [lintegral_mul_const (ENNReal.ofReal (physicalForceWeight hd lam (-a))) hw_meas, mul_comm]
      _ = ENNReal.ofReal (physicalForceWeight hd lam (-a)) • (volume.withDensity w) s := by
        rw [smul_eq_mul, withDensity_apply _ hs]
  set c := ENNReal.ofReal (physicalForceWeight hd lam (-a)) with hc_def
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
  have hc_top : c ≠ ∞ := ENNReal.ofReal_ne_top
  have h_smul_equiv : MemLp f p (c • μ) ↔ MemLp f p μ := by
    have h_inv_top : c⁻¹ ≠ ∞ := by
      rw [ENNReal.inv_ne_top]
      exact hc0
    constructor
    · intro h
      have h_inv : MemLp f p (c⁻¹ • (c • μ)) :=
        MemLp.smul_measure h h_inv_top
      have h_eq : c⁻¹ • (c • μ) = μ := by
        calc
          c⁻¹ • (c • μ) = (c⁻¹ * c) • μ := by rw [smul_smul]
          _ = 1 • μ := by simp [ENNReal.inv_mul_cancel hc0 hc_top]
          _ = μ := by rw [one_smul]
      rwa [h_eq] at h_inv
    · exact fun h => MemLp.smul_measure h hc_top
  have h_memLp_equiv : MemLp (fun y => f (a + y)) p μ ↔ MemLp f p (Measure.map (T : Vec d → Vec d) μ) := by
    simpa [T] using (T.memLp_map_measure_iff (g := f)).symm
  rw [h_memLp_equiv, h_map_eq]
  exact h_smul_equiv

end EinsteinRelation.External.GantertSection7Support
