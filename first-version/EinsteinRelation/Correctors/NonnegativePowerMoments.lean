import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Power conversion in the probability Minkowski step, paper/main.tex:844–849. -/
theorem nonnegative_rpow_moment {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) {p q C : ℝ} (hp : 0 < p) (hq : 0 < q) (hC : 0 ≤ C)
    {f : Ω → ℝ} (hf : Measurable f) (hfn : ∀ ω, 0 ≤ f ω)
    (hmem : MemLp f (ENNReal.ofReal p) Q)
    (hbound : eLpNorm f (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    MemLp (fun ω => (f ω)^q) (ENNReal.ofReal (p / q)) Q ∧
      eLpNorm (fun ω => (f ω)^q) (ENNReal.ofReal (p / q)) Q ≤
        ENNReal.ofReal (C^q) := by
  have hq_nonneg : 0 ≤ q := hq.le
  have hp_nonneg : 0 ≤ p := hp.le
  have h_div_nonneg : 0 ≤ p / q := div_nonneg hp_nonneg hq_nonneg
  -- For nonnegative real f, the norm equals the function itself
  have hnorm : ∀ ω, ‖f ω‖ = f ω := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hfn ω)]
  -- Part 1: MemLp membership via MemLp.norm_rpow_div
  have hmem_div : MemLp (fun ω => (f ω)^q) (ENNReal.ofReal (p / q)) Q := by
    have h := hmem.norm_rpow_div (ENNReal.ofReal q)
    simpa [hnorm, ENNReal.toReal_ofReal hq_nonneg, ENNReal.ofReal_div_of_pos hq] using h
  -- Part 2: norm bound via eLpNorm_norm_rpow
  have hnorm_bound : eLpNorm (fun ω => (f ω)^q) (ENNReal.ofReal (p / q)) Q ≤ ENNReal.ofReal (C^q) := by
    have h_eq : eLpNorm (fun ω => ‖f ω‖ ^ q) (ENNReal.ofReal (p / q)) Q =
               eLpNorm f ((ENNReal.ofReal (p / q)) * ENNReal.ofReal q) Q ^ q :=
      eLpNorm_norm_rpow (p := ENNReal.ofReal (p / q)) f hq
    have h_mul : (ENNReal.ofReal (p / q)) * ENNReal.ofReal q = ENNReal.ofReal p := by
      calc
        (ENNReal.ofReal (p / q)) * ENNReal.ofReal q = ENNReal.ofReal ((p / q) * q) := by
          rw [ENNReal.ofReal_mul h_div_nonneg]
        _ = ENNReal.ofReal p := by field_simp [hq.ne.symm]
    have h_fun : (fun ω => ‖f ω‖ ^ q) = (fun ω => (f ω)^q) := by
      ext ω; simp [hnorm ω]
    rw [h_fun, h_mul] at h_eq
    rw [h_eq]
    have h_rpow_le : (eLpNorm f (ENNReal.ofReal p) Q) ^ q ≤ (ENNReal.ofReal C) ^ q :=
      ENNReal.rpow_le_rpow hbound hq_nonneg
    have h_C_rpow : (ENNReal.ofReal C) ^ q = ENNReal.ofReal (C ^ q) :=
      ENNReal.ofReal_rpow_of_nonneg hC hq_nonneg
    calc
      (eLpNorm f (ENNReal.ofReal p) Q) ^ q ≤ (ENNReal.ofReal C) ^ q := h_rpow_le
      _ = ENNReal.ofReal (C ^ q) := h_C_rpow
  exact ⟨⟨(hf.pow_const q).aestronglyMeasurable, hmem_div.2⟩, hnorm_bound⟩

end EinsteinRelation.Correctors
