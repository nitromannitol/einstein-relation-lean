import EinsteinFull.Blueprint.G1.node_rt_u3A_factorization_u23_small_u2D_indices
import EinsteinRelation.Regeneration.TrialBounds
import EinsteinRelation.Regeneration.RenewalRecordIteration
import EinsteinRelation.Regeneration.CycleRewardFactorsDecoder

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- The literal first regeneration time cannot equal either of the first two
lattice points. This graph leaf uses only the pathwise trial definitions. -/
theorem node_rt_u3A_factorization_u23_small_u2D_indices_of_deps :
    node_rt_u3A_factorization_u23_small_u2D_indicesStmt := by
  intro d hd lam l hlam hl n hn
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ωz hωz
  have hΔ := EinsteinRelation.regenDelta_pos hlam
  have hb := Regeneration.two_step_le_firstRegenerationTime
    (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam)
    hlam (div_pos hl hlam) ωz.2 (Regeneration.Renewal.forceCoord hd)
  rw [← Regeneration.regenerationTime_one] at hb
  change (2 : ℝ≥0∞) * (Regeneration.Renewal.regenDelta lam : ℝ≥0∞) ≤
    regenerationTime hd lam l 1 ωz.2 at hb
  rw [hωz] at hb
  have hb' := ENNReal.toReal_mono ENNReal.coe_ne_top hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
    NNReal.coe_mul, NNReal.coe_natCast] at hb'
  have hnr : (n : ℝ) ≤ 1 := by exact_mod_cast hn
  have hΔr : 0 < (Regeneration.Renewal.regenDelta lam : ℝ) := hΔ
  nlinarith

end EinsteinFull.Blueprint
