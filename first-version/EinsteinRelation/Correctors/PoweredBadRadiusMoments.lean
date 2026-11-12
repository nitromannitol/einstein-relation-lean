import EinsteinRelation.Correctors.RandomRadiusCutoffMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Source: paper/main.tex:856–862. Polynomial suppression of the bad-radius
event from higher moments. No independence is assumed. -/
theorem powered_badRadius_eLpNorm_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X E : Ω → ℝ} (hXm : Measurable X) (hX : ∀ ω, 0 ≤ X ω)
    {m R a : ℝ} (hm : 0 < m) (hR : 0 < R) (ha : 0 < a)
    (hXLp : MemLp (fun ω => (X ω) ^ a) (ENNReal.ofReal (2*m)) P)
    (hELp : MemLp E (ENNReal.ofReal (2*m)) P) :
    MemLp ({ω | R < X ω}.indicator E) (ENNReal.ofReal m) P ∧
      eLpNorm ({ω | R < X ω}.indicator E) (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (R ^ (-a)) *
          (eLpNorm (fun ω => (X ω) ^ a) (ENNReal.ofReal (2*m)) P *
            eLpNorm E (ENNReal.ofReal (2*m)) P) := by
  have hS : MeasurableSet {ω | R < X ω} :=
    measurableSet_lt measurable_const hXm
  have hXLp_ae : AEStronglyMeasurable (fun ω => (X ω) ^ a) P := hXLp.1
  have hELp_ae : AEStronglyMeasurable E P := hELp.1
  have hdom : ∀ᵐ ω ∂P,
      ‖{ω | R < X ω}.indicator E ω‖ ≤
        (R ^ (-a)) * ‖(fun ω => (X ω) ^ a) ω * E ω‖ := by
    apply ae_of_all
    intro ω
    by_cases hω : R < X ω
    · have hmem : ω ∈ {ω | R < X ω} := hω
      rw [Set.indicator_of_mem hmem, norm_mul,
        Real.norm_of_nonneg (Real.rpow_nonneg (hX ω) a)]
      have hcoef : (1 : ℝ) ≤ R ^ (-a) * (X ω) ^ a := by
        have hXpos : 0 < X ω := hR.trans hω
        have hrpow : R ^ a < (X ω) ^ a :=
          Real.rpow_lt_rpow hR.le hω ha
        have hpos : 0 < R ^ a := Real.rpow_pos_of_pos hR a
        have h_one : (1 : ℝ) < ((X ω) ^ a) * (R ^ a)⁻¹ := by
          apply (one_lt_div hpos).mpr hrpow
        have h_eq : (R ^ a)⁻¹ = R ^ (-a) := by rw [Real.rpow_neg hR.le a]
        have h_lt : (1 : ℝ) < (X ω) ^ a * R ^ (-a) := by
          rwa [h_eq] at h_one
        linarith
      calc
        ‖E ω‖ = 1 * ‖E ω‖ := (one_mul _).symm
        _ ≤ (R ^ (-a) * (X ω) ^ a) * ‖E ω‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
        _ = R ^ (-a) * ((X ω) ^ a * ‖E ω‖) := by ring
    · have hmem : ω ∉ {ω | R < X ω} := hω
      rw [Set.indicator_of_notMem hmem, norm_zero]
      have h_nonneg : 0 ≤ (R ^ (-a)) * ‖(fun ω => (X ω) ^ a) ω * E ω‖ :=
        mul_nonneg (Real.rpow_nonneg hR.le _) (norm_nonneg _)
      exact h_nonneg
  have hprod : MemLp (fun ω => (X ω) ^ a * E ω) (ENNReal.ofReal m) P := by
    have h_holder : ENNReal.HolderTriple (ENNReal.ofReal (2*m)) (ENNReal.ofReal (2*m))
        (ENNReal.ofReal m) := holderTriple_double_ofReal hm
    have h := hXLp.mul' hELp (r := ENNReal.ofReal m)
    simpa [mul_comm] using h
  have h_mem : MemLp ({ω | R < X ω}.indicator E) (ENNReal.ofReal m) P :=
    hprod.of_le_mul (hELp_ae.indicator hS) hdom
  have h_bound : eLpNorm ({ω | R < X ω}.indicator E) (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (R ^ (-a)) *
        eLpNorm (fun ω => (X ω) ^ a * E ω) (ENNReal.ofReal m) P :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
  have h_holder_eLp : eLpNorm (fun ω => (X ω) ^ a * E ω) (ENNReal.ofReal m) P ≤
      eLpNorm (fun ω => (X ω) ^ a) (ENNReal.ofReal (2*m)) P *
        eLpNorm E (ENNReal.ofReal (2*m)) P := by
    have h_mul : (fun ω => (X ω) ^ a * E ω) = (fun ω => (X ω) ^ a) • E := by
      ext ω; simp [smul_eq_mul]
    rw [h_mul]
    have h_holder : ENNReal.HolderTriple (ENNReal.ofReal (2*m)) (ENNReal.ofReal (2*m))
        (ENNReal.ofReal m) := holderTriple_double_ofReal hm
    exact eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2*m))
      (q := ENNReal.ofReal (2*m)) (r := ENNReal.ofReal m)
      (f := E) (φ := fun ω => (X ω) ^ a) hELp_ae hXLp_ae (hpqr := h_holder)
  have h_final : eLpNorm ({ω | R < X ω}.indicator E) (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (R ^ (-a)) *
        (eLpNorm (fun ω => (X ω) ^ a) (ENNReal.ofReal (2*m)) P *
          eLpNorm E (ENNReal.ofReal (2*m)) P) := by
    refine le_trans h_bound ?_
    have h_nonneg : 0 ≤ ENNReal.ofReal (R ^ (-a)) := zero_le _
    exact mul_le_mul_of_nonneg_left h_holder_eLp h_nonneg
  exact ⟨h_mem, h_final⟩

end EinsteinRelation.Correctors
