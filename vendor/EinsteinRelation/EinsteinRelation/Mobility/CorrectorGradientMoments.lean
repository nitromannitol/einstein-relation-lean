import EinsteinRelation.Mobility.AKMFluxDecaySplit
import EinsteinRelation.Correctors.CanonicalGradientSecondMoment
import Mathlib.MeasureTheory.Integral.Average

/-! # Gradient moments from unit-scale energy and regularity estimates

The gradient assertion of Lemma 5.1 (`paper/main.tex:704-713,727-729`) reduces
to moments of the spatial unit-scale energy and a deterministic interior
gradient estimate. The estimates remain explicit hypotheses below: this file
does not register them as permitted external inputs or prove the full lemma.

The spatial ball and the vector norm are Euclidean. The energy uses the
canonical gradient along the actual translation action. All constants are
chosen before the environment law and direction.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- The unit-ball root-mean-square of `e_i + ∇φ_i`, used in Step 2 of the
proof of Lemma 5.1 (`paper/main.tex:727-729`). -/
noncomputable def canonicalCorrectorUnitEnergy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ω : FieldPair d) : ℝ :=
  Real.sqrt (⨍ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
    ‖correctorUnitVector i +
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate x.ofLp ω)‖ ^ 2 ∂volume)

theorem canonicalCorrectorUnitEnergy_nonneg {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ω : FieldPair d) :
    0 ≤ canonicalCorrectorUnitEnergy Q i ω := Real.sqrt_nonneg _

/-- Measurability of the unit-scale energy in `paper/main.tex:727-729`. -/
theorem measurable_canonicalCorrectorUnitEnergy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Measurable (canonicalCorrectorUnitEnergy Q i) := by
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have hT : Measurable (fun p : FieldPair d × EuclideanSpace ℝ (Fin d) =>
      translate p.2.ofLp p.1) :=
    Probability.continuous_translate.measurable.comp
      (((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
        measurable_snd).prodMk measurable_fst)
  have hsq : Measurable (fun p : FieldPair d × EuclideanSpace ℝ (Fin d) =>
      ‖correctorUnitVector i + G (translate p.2.ofLp p.1)‖ ^ 2) :=
    (measurable_const.add ((Lp.stronglyMeasurable G).measurable.comp hT)).norm.pow_const 2
  unfold canonicalCorrectorUnitEnergy
  simp only [average_eq]
  exact (measurable_const.mul
    (hsq.stronglyMeasurable.integral_prod_right'.measurable)).sqrt

/-- Integration of a pointwise bound by a nonnegative random amplitude.
This is the probability step in `paper/main.tex:727-729`. -/
theorem lintegral_norm_rpow_le_of_unit_energy {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω → E} {A : Ω → ℝ} {K C m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hA : ∀ ω, 0 ≤ A ω) (hG : ∀ᵐ ω ∂μ, ‖G ω‖ ≤ K * A ω + 1)
    (hC : ∫⁻ ω, ENNReal.ofReal (A ω ^ m) ∂μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (‖G ω‖ ^ m) ∂μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ m * (K ^ m * max C 0 + 1)) := by
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (‖G ω‖ ^ m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ m) *
        (ENNReal.ofReal (K ^ m) * ENNReal.ofReal (A ω ^ m) + 1) := by
    filter_upwards [hG] with ω hω
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hm]
    calc ENNReal.ofReal ‖G ω‖ ^ m
        ≤ ENNReal.ofReal (K * A ω + 1) ^ m :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hω) hm
      _ = (ENNReal.ofReal K * ENNReal.ofReal (A ω) + 1) ^ m := by
          rw [ENNReal.ofReal_add (mul_nonneg hK (hA ω)) zero_le_one,
            ENNReal.ofReal_mul hK, ENNReal.ofReal_one]
      _ ≤ (2 : ℝ≥0∞) ^ m *
          ((ENNReal.ofReal K * ENNReal.ofReal (A ω)) ^ m + (1 : ℝ≥0∞) ^ m) :=
          ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hm
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hm, ENNReal.one_rpow,
            ← ENNReal.ofReal_rpow_of_nonneg hK hm,
            ← ENNReal.ofReal_rpow_of_nonneg (hA ω) hm,
            ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm]
  calc (∫⁻ ω, ENNReal.ofReal (‖G ω‖ ^ m) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ m) *
          (ENNReal.ofReal (K ^ m) * ENNReal.ofReal (A ω ^ m) + 1) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((2 : ℝ) ^ m) *
        (ENNReal.ofReal (K ^ m) * (∫⁻ ω, ENNReal.ofReal (A ω ^ m) ∂μ) + 1) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ m) *
        (ENNReal.ofReal (K ^ m) * ENNReal.ofReal (max C 0) + 1) := by
        gcongr
        exact hC.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal ((2 : ℝ) ^ m * (K ^ m * max C 0 + 1)) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
          ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hK _) (le_max_right _ _))
            zero_le_one,
          ENNReal.ofReal_mul (Real.rpow_nonneg hK _), ENNReal.ofReal_one]

end EinsteinRelation.Correctors

namespace EinsteinRelation

open Correctors

private theorem euclideanNorm_ofLp_eq_norm {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d)) : euclideanNorm u.ofLp = ‖u‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (u.ofLp j)).symm

/-- The gradient conclusion of Lemma 5.1 (`paper/main.tex:712,727-729`),
conditional on two unresolved analytic obligations. `henergy` is the finite
moment consequence of AKM Theorem 4.1, (4.4), p. 124, at a fixed scale, after
rescaling and canonical-gradient identification. `hregularity` is the unit-scale
interior gradient estimate. Neither hypothesis is discharged or added to the
repository's permitted external-input boundary here. -/
theorem correctorGradientMoments_of_inputs
    (henergy : ∀ (d : ℕ) (_ : 2 ≤ d) (Λ₀ r₀ m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
        ∫⁻ ω, ENNReal.ofReal (canonicalCorrectorUnitEnergy Q i ω ^ m)
          ∂reducedEnvironmentLaw Q ≤ ENNReal.ofReal C)
    (hregularity : ∀ (d : ℕ) (_ : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ K : ℝ, 0 ≤ K ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
        ∀ᵐ ω ∂reducedEnvironmentLaw Q,
          ‖correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω‖ ≤
            K * canonicalCorrectorUnitEnergy Q i ω) :
    CorrectorGradientMoments := by
  intro d hd Λ₀ r₀ m hm
  obtain ⟨C, hC⟩ := henergy d hd Λ₀ r₀ m hm
  obtain ⟨K, hK, hreg⟩ := hregularity d hd Λ₀ r₀
  refine ⟨(2 : ℝ) ^ m * (K ^ m * max C 0 + 1), fun Q i => ?_⟩
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have hpoint : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ‖G ω‖ ≤ K * canonicalCorrectorUnitEnergy Q i ω + 1 := by
    filter_upwards [hreg Q i] with ω hω
    have hunit : ‖correctorUnitVector i‖ = 1 := by simp [correctorUnitVector]
    calc ‖G ω‖ = ‖(correctorUnitVector i + G ω) - correctorUnitVector i‖ := by
          rw [add_sub_cancel_left]
      _ ≤ ‖correctorUnitVector i + G ω‖ + ‖correctorUnitVector i‖ := norm_sub_le _ _
      _ ≤ K * canonicalCorrectorUnitEnergy Q i ω + 1 := by
          rw [hunit]
          exact add_le_add hω le_rfl
  simpa only [StationarySpatialRealization.spatialRealization, translate_zero,
    euclideanNorm_ofLp_eq_norm] using
    lintegral_norm_rpow_le_of_unit_energy (reducedEnvironmentLaw Q) hK
      (le_trans zero_le_two hm) (canonicalCorrectorUnitEnergy_nonneg Q i) hpoint (hC Q i)

end EinsteinRelation

