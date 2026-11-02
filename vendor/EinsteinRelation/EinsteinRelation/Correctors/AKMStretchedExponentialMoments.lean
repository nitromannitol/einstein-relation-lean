import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.FieldSimp

/-! # Finite moments of the AKM stochastic bounds

Source: `paper/main.tex:779–800,938–945`. The cited AKM statements use
stretched exponential bounds, while the manuscript uses finite moments.
This module makes that passage quantitative without imposing additional
integrability hypotheses on the random variable.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM

/-- An explicit finite moment bound from the convention (0.41)--(0.42)
in AKM, p. xxxvi. Source: `paper/main.tex:779–800,938–945`. -/
theorem lintegral_rpow_le_of_stretchedExponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {s θ m : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hm : 0 < m) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hbound : StretchedExponentialBound μ s θ X) :
    (∫⁻ ω, ENNReal.ofReal ((X ω) ^ m) ∂μ) ≤
      ENNReal.ofReal (2 * (m / s) ^ (m / s) * θ ^ m) := by
  have hpoint : ∀ᵐ ω ∂μ,
      ENNReal.ofReal ((X ω) ^ m) ≤
        ENNReal.ofReal ((m / s) ^ (m / s) * θ ^ m) *
          ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) := by
    filter_upwards [hX] with ω hω
    have hy : 0 ≤ X ω / θ := div_nonneg hω hθ.le
    have hz : 0 ≤ (X ω / θ) ^ s := Real.rpow_nonneg hy _
    have hpower : (X ω / θ) ^ m = |(X ω / θ) ^ s| ^ (m / s) := by
      rw [abs_of_nonneg hz, ← Real.rpow_mul hy]
      congr 1
      field_simp
    have hpoly := ProbabilityTheory.rpow_abs_le_mul_max_exp_of_pos
      ((X ω / θ) ^ s) (p := m / s) (t := 1) (by positivity) zero_lt_one
    have hexp : Real.exp (-((X ω / θ) ^ s)) ≤ Real.exp ((X ω / θ) ^ s) :=
      Real.exp_le_exp.mpr (by linarith)
    simp only [div_one, one_mul, neg_one_mul, max_eq_left hexp] at hpoly
    have hfactor : (X ω) ^ m = θ ^ m * (X ω / θ) ^ m := by
      rw [← Real.mul_rpow hθ.le hy]
      congr 1
      field_simp
    rw [← ENNReal.ofReal_mul (by positivity), max_eq_left hω]
    apply ENNReal.ofReal_le_ofReal
    calc
      (X ω) ^ m = θ ^ m * (X ω / θ) ^ m := hfactor
      _ ≤ θ ^ m * ((m / s) ^ (m / s) * Real.exp ((X ω / θ) ^ s)) := by
        rw [hpower]
        exact mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  calc
    (∫⁻ ω, ENNReal.ofReal ((X ω) ^ m) ∂μ) ≤
        ∫⁻ ω, ENNReal.ofReal ((m / s) ^ (m / s) * θ ^ m) *
          ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂μ :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal ((m / s) ^ (m / s) * θ ^ m) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((max (X ω) 0 / θ) ^ s)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((m / s) ^ (m / s) * θ ^ m) * 2 :=
      mul_le_mul_right hbound _
    _ = ENNReal.ofReal (2 * (m / s) ^ (m / s) * θ ^ m) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- The `L^m` version of the AKM stretched exponential convention, with
the exact scale factor `θ` and a constant depending only on `s,m`.
Source: `paper/main.tex:779–800,938–945`. -/
theorem eLpNorm_le_of_stretchedExponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {s θ m : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hm : 0 < m) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hXm : AEStronglyMeasurable X μ)
    (hbound : StretchedExponentialBound μ s θ X) :
    eLpNorm X (ENNReal.ofReal m) μ ≤
      ENNReal.ofReal ((2 * (m / s) ^ (m / s)) ^ (1 / m) * θ) := by
  have hmoment := lintegral_rpow_le_of_stretchedExponential μ hs hθ hm hX hbound
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hXm,
    ENNReal.toReal_ofReal hm.le]
  have hnorm : (∫⁻ ω, ‖X ω‖ₑ ^ m ∂μ) = ∫⁻ ω, ENNReal.ofReal ((X ω) ^ m) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hX] with ω hω
    rw [Real.enorm_eq_ofReal hω, ENNReal.ofReal_rpow_of_nonneg hω hm.le]
  rw [hnorm]
  calc
    _ ≤ ENNReal.ofReal (2 * (m / s) ^ (m / s) * θ ^ m) ^ (1 / m) :=
      ENNReal.rpow_le_rpow hmoment (by positivity)
    _ = ENNReal.ofReal ((2 * (m / s) ^ (m / s)) ^ (1 / m) * θ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hθ.le]
      congr 2
      rw [mul_one_div_cancel hm.ne', Real.rpow_one]

/-- Measurability and an AKM stochastic bound imply every positive finite
moment. Source: `paper/main.tex:779–800,938–945`. -/
theorem memLp_of_stretchedExponential {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {s θ m : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hm : 0 < m) (hXm : AEStronglyMeasurable X μ) (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hbound : StretchedExponentialBound μ s θ X) :
    MemLp X (ENNReal.ofReal m) μ :=
  (eLpNorm_le_of_stretchedExponential μ hs hθ hm hX hXm hbound).trans_lt
    ENNReal.ofReal_lt_top

/-- An almost sure absolute bound by an AKM random upper bound gives the
same finite-moment estimate. The upper bound may have either sign, as the
source convention controls its positive part.
Source: `paper/main.tex:938–945`. -/
theorem eLpNorm_le_of_stretchedExponential_domination {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Y Z : Ω → ℝ} {s θ m : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hm : 0 < m) (hYZ : ∀ᵐ ω ∂μ, |Y ω| ≤ max (Z ω) 0) (hYm : AEStronglyMeasurable Y μ)
    (hbound : StretchedExponentialBound μ s θ Z) :
    eLpNorm Y (ENNReal.ofReal m) μ ≤
      ENNReal.ofReal ((2 * (m / s) ^ (m / s)) ^ (1 / m) * θ) := by
  have habs : StretchedExponentialBound μ s θ (fun ω => |Y ω|) := by
    apply le_trans (lintegral_mono_ae ?_) hbound
    filter_upwards [hYZ] with ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow (by positivity) _ hs.le
    rw [max_eq_left (abs_nonneg _)]
    exact div_le_div_of_nonneg_right hω hθ.le
  simpa only [← Real.norm_eq_abs, eLpNorm_norm Y hYm] using
    eLpNorm_le_of_stretchedExponential μ hs hθ hm
      (Filter.Eventually.of_forall fun ω => abs_nonneg (Y ω)) hYm.norm habs

/-- Theorem 9.1, p. 349, in the finite-moment form used by the manuscript.
The constant is uniform over the coefficient law and all the source's
bounded local stationary initial vector fields. The same flow witnesses
carry the source PDE and all finite moments at the specified exponent.
Identification with a separately constructed flow is not asserted.
Source: `paper/main.tex:779–788`. -/
theorem parabolicSemigroupDecay_moments (hAKM : ParabolicSemigroupDecay)
    (d : ℕ) (hd : 2 ≤ d) (K s m : ℝ) (hK : 1 < K) (hs : 0 < s)
    (hs2 : s < 2) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ P : Measure (Environment.AKMTestIntegralSupport.Coefficient d K),
        IsAdmissibleLaw P →
        ∀ g : Environment.AKMTestIntegralSupport.Coefficient d K → Vec d → Vec d,
          IsStationaryField P g →
          (∀ᵐ A ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanNorm (g A x) ≤ 1) →
          (∀ x : Vec d, Measurable[Environment.AKMTestIntegralSupport.localSigma
              {y | euclideanNorm (y - x) < 1}] (fun A => g A x)) →
          ∃ (u : Environment.AKMTestIntegralSupport.Coefficient d K → ℝ × Vec d → ℝ)
            (G : Environment.AKMTestIntegralSupport.Coefficient d K → ℝ × Vec d → Vec d),
            Measurable (fun z : Environment.AKMTestIntegralSupport.Coefficient d K ×
              (ℝ × Vec d) => u z.1 z.2) ∧
            (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) ∧
            ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
              MemLp (fun A => u A (t, x)) (ENNReal.ofReal m) P ∧
                eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
                  ENNReal.ofReal (C * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  obtain ⟨C, hC, hdecay⟩ := hAKM d hd K s hK hs hs2
  refine ⟨(2 * (m / s) ^ (m / s)) ^ (1 / m) * C, by positivity, ?_⟩
  intro P hP g hg hgb hgl
  obtain ⟨u, G, hu, hsol, hstoch⟩ := hdecay P hP g hg hgb hgl
  refine ⟨u, G, hu, hsol, ?_⟩
  intro t ht x
  have hθ : 0 < C * t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4) :=
    mul_pos hC (Real.rpow_pos_of_pos (by linarith) _)
  have hum : AEStronglyMeasurable (fun A => u A (t, x)) P :=
    (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hbound := eLpNorm_le_of_stretchedExponential P hs hθ hm
    (Filter.Eventually.of_forall fun A => abs_nonneg (u A (t, x))) hum.norm (hstoch t ht x)
  have hnorm : eLpNorm (fun A => u A (t, x)) (ENNReal.ofReal m) P ≤
      ENNReal.ofReal (((2 * (m / s) ^ (m / s)) ^ (1 / m) * C) *
        t ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
    simpa only [← Real.norm_eq_abs, eLpNorm_norm (fun A => u A (t, x)) hum, mul_assoc] using hbound
  exact ⟨hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

end EinsteinRelation.Correctors


/-! Moment conversion for the stochastic estimates used at `paper/main.tex:718-723`. -/
open MeasureTheory
namespace EinsteinRelation.External.AKM

open scoped ENNReal

/-- Every positive stochastic exponent supplies every finite positive moment. -/
theorem OsBound.moment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ p : ℝ}
    (h : OsBound P X s θ) (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal ((max (X ω) 0) ^ p) ∂P) ≤
      ENNReal.ofReal (2 * θ ^ p * (p / s) ^ (p / s)) := by
  have hs : 0 < s := h.2.1
  have hθ : 0 < θ := h.2.2.1
  have hexp : (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) ≤ 2 := by
    simpa [OsBound] using h.2.2.2
  have hpt (ω : Ω) : (max (X ω) 0) ^ p ≤
      (θ ^ p * (p / s) ^ (p / s)) * Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) := by
    have hx_nonneg : 0 ≤ θ⁻¹ * max (X ω) 0 := by
      positivity
    have hx_rpow : 0 ≤ (θ⁻¹ * max (X ω) 0) ^ s := Real.rpow_nonneg hx_nonneg _
    have hps : 0 < p / s := div_pos hp hs
    have hdom := rpow_le_exp_mul hx_rpow hps
    have h_eq : (max (X ω) 0) ^ p = θ ^ p * ((θ⁻¹ * max (X ω) 0) ^ s) ^ (p / s) := by
      calc
        (max (X ω) 0) ^ p = (θ * (θ⁻¹ * max (X ω) 0)) ^ p := by
          field_simp [hθ.ne']
        _ = θ ^ p * (θ⁻¹ * max (X ω) 0) ^ p :=
          by rw [Real.mul_rpow hθ.le hx_nonneg]
        _ = θ ^ p * ((θ⁻¹ * max (X ω) 0) ^ s) ^ (p / s) := by
          rw [show (θ⁻¹ * max (X ω) 0) ^ p = ((θ⁻¹ * max (X ω) 0) ^ s) ^ (p / s) from by
            calc
              (θ⁻¹ * max (X ω) 0) ^ p = (θ⁻¹ * max (X ω) 0) ^ (s * (p / s)) := by
                field_simp [hs.ne']
              _ = ((θ⁻¹ * max (X ω) 0) ^ s) ^ (p / s) := by
                rw [Real.rpow_mul hx_nonneg s (p / s)]
            ]
    rw [h_eq]
    calc
      θ ^ p * ((θ⁻¹ * max (X ω) 0) ^ s) ^ (p / s)
          ≤ θ ^ p * ((p / s) ^ (p / s) * Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) :=
        mul_le_mul_of_nonneg_left hdom (Real.rpow_nonneg hθ.le _)
      _ = (θ ^ p * (p / s) ^ (p / s)) * Real.exp ((θ⁻¹ * max (X ω) 0) ^ s) := by ring
  calc
    (∫⁻ ω, ENNReal.ofReal ((max (X ω) 0) ^ p) ∂P)
        ≤ ∫⁻ ω, ENNReal.ofReal ((θ ^ p * (p / s) ^ (p / s)) *
            Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (θ ^ p * (p / s) ^ (p / s)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)) ∂P) := by
      simp_rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hθ.le _)
        (Real.rpow_nonneg (div_nonneg hp.le hs.le) _))]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (θ ^ p * (p / s) ^ (p / s)) * 2 := mul_le_mul_right hexp _
    _ = ENNReal.ofReal (2 * θ ^ p * (p / s) ^ (p / s)) := by
      rw [show (2 * θ ^ p * (p / s) ^ (p / s)) = (θ ^ p * (p / s) ^ (p / s)) * 2 by ring,
        ENNReal.ofReal_mul (by
          positivity
          : 0 ≤ θ ^ p * (p / s) ^ (p / s)), ENNReal.ofReal_ofNat]

end EinsteinRelation.External.AKM
