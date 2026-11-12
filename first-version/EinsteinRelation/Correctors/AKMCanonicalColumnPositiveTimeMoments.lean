import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace
import EinsteinRelation.Correctors.PositiveTimeDecayProfile

/-! # The entire positive-time scalar profile of a specified column flow

Source: `paper/main.tex:842–847`. Coefficient regularity supplies the
initial-layer bound. The large-time scalar moments remain explicit
internal hypotheses concerning this same specified canonical flow.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Bounded weak divergence supplies the initial layer, so only the
large-time scalar moment estimate of the same canonical column flow is
needed. The profile constant precedes the environment law, column, and
flow. Source: `paper/main.tex:777–784,842–847`. -/
theorem actualCoefficientLaw_canonical_column_positive_time_moments
    (d : ℕ) (L r₀ C : ℝ) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 < M ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ p : ℝ, 2 ≤ p →
      (∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ t : ℝ, 0 < t → ∀ x : Vec d,
        MemLp (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ∧
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (M*(1+t)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
  let D : ℝ := (d : ℝ) * akmColumnLipschitzConstant d L r₀
  let β : ℝ := 1/2+(d : ℝ)/4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  let M : ℝ := 2^β * max D C + 1
  have hM₀ : 0 ≤ 2^β * max D C :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hD.trans (le_max_left _ _))
  have hM : 0 < M := by dsimp only [M]; linarith only [hM₀]
  refine ⟨M, hM, ?_⟩
  intro Q i u G hum hflow p _hp hlate t ht x
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) :=
    (isAdmissibleLaw_actualCoefficientLaw Q).1
  have hm : AEStronglyMeasurable (fun A => u A (t,x)) (actualCoefficientLaw Q) :=
    (hum.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hβeq : -β = -(1 : ℝ)/2-(d : ℝ)/4 := by dsimp only [β]; ring
  have hb : eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
      ENNReal.ofReal (M*(1+t)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
    have hinc : (2^β * max D C) * (1+t)^(-β) ≤ M * (1+t)^(-β) :=
      mul_le_mul_of_nonneg_right (by dsimp only [M]; linarith)
        (Real.rpow_nonneg (by linarith) _)
    rw [← hβeq]
    by_cases ht1 : t ≤ 1
    · have hbounded : ∀ᵐ A ∂actualCoefficientLaw Q, ‖u A (t,x)‖ ≤ D := by
        filter_upwards [ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
          with A hA
        exact (Real.norm_eq_abs _).trans_le (hA t ht x)
      have hnorm : eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p)
          (actualCoefficientLaw Q) ≤ ENNReal.ofReal D := by
        simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
          (eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p) hbounded)
      exact hnorm.trans (ENNReal.ofReal_le_ofReal
        ((le_shifted_power_profile_of_small_time hD hβ ht.le ht1).trans hinc))
    · have hlarge := hlate t (le_of_not_ge ht1) x
      rw [← hβeq] at hlarge
      exact hlarge.trans (ENNReal.ofReal_le_ofReal
        ((power_le_shifted_power_profile_of_large_time hC hβ (le_of_not_ge ht1)).trans hinc))
  exact ⟨⟨hm, hb.trans_lt ENNReal.ofReal_lt_top⟩, hb⟩

end EinsteinRelation.Correctors
