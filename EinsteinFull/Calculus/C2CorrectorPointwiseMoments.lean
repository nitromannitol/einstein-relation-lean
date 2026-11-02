import EinsteinFull.Calculus.C2PhysicalCorrectorMoments
import EinsteinFull.Frozen.CorrectorGradient
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Stationarity and Tonelli for the literal canonical gradient. These identities
hold before any higher-moment finiteness assertion. They do not select a spatial
weak derivative at the origin or assert the smooth-moments source node. -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

/-- The canonical L² representative has a jointly measurable spatial orbit. -/
theorem measurable_correctorGradient_orbit {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Measurable (fun q : FieldPair d × Vec d =>
      correctorGradient Q i (translate q.2 q.1)) := by
  exact (Lp.stronglyMeasurable (correctorGradient Q i)).measurable.comp
    (Probability.continuous_translate.measurable.comp measurable_swap)

/-- Every translated marginal has exactly the origin moment, including when
the nonnegative extended integral is infinite. -/
theorem lintegral_correctorGradient_translate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (z : Vec d) (p : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i (translate z ω)‖ ^ p)
      ∂reducedLaw Q) =
    ∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ p) ∂reducedLaw Q := by
  have hm := (((Lp.stronglyMeasurable (correctorGradient Q i)).measurable.norm
    ).pow_const p).ennreal_ofReal
  exact (EinsteinRelation.measurePreserving_translate (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) z).lintegral_comp hm

/-- Tonelli and stationarity identify the spatially averaged moment with the
actual canonical marginal. No integrability is assumed. -/
theorem lintegral_correctorGradient_spatial_moment {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ν : Measure (Vec d)) [SFinite ν] (p : ℝ) :
    (∫⁻ ω, ∫⁻ x, ENNReal.ofReal
      (‖correctorGradient Q i (translate x ω)‖ ^ p) ∂ν ∂reducedLaw Q) =
    ν Set.univ *
      (∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ p) ∂reducedLaw Q) := by
  have hprob : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hm := (((measurable_correctorGradient_orbit Q i).norm).pow_const p).ennreal_ofReal
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simp_rw [lintegral_correctorGradient_translate]
  rw [lintegral_const, mul_comm]

/-- The same identity holds on the actual physical reference probability
space, using its proved reduction map. -/
theorem lintegral_physical_correctorGradient_spatial_moment
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ν : Measure (Vec d)) [SFinite ν] (p : ℝ) :
    (∫⁻ ω, ∫⁻ x, ENNReal.ofReal
      (‖correctorGradient Q i (translate x (reduce ω.1))‖ ^ p)
        ∂ν ∂physicalReferenceLaw Q) =
    ν Set.univ *
      (∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ p) ∂reducedLaw Q) := by
  have hm := (((measurable_correctorGradient_orbit Q i).norm).pow_const p).ennreal_ofReal
  calc
    _ = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal
        (‖correctorGradient Q i (translate x ω)‖ ^ p) ∂ν ∂reducedLaw Q :=
      (measurePreserving_physicalReduction Q).lintegral_comp hm.lintegral_prod_right
    _ = _ := lintegral_correctorGradient_spatial_moment Q i ν p

/-- The existing canonical L² construction gives genuine pointwise-law
membership up to exponent two at every deterministic translate. This does not
claim the higher moments or their uniform structural constant. -/
theorem correctorGradient_translate_memLp_of_le_two {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (z : Vec d) {p : ℝ≥0∞}
    (hp : p ≤ 2) :
    MemLp (fun ω => correctorGradient Q i (translate z ω)) p (reducedLaw Q) := by
  have hprob : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hmem : MemLp (fun ω => correctorGradient Q i ω) 2 (reducedLaw Q) :=
    Lp.memLp (correctorGradient Q i)
  exact (hmem.mono_exponent hp).comp_measurePreserving
    (EinsteinRelation.measurePreserving_translate (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) z)

/-- In the positive real exponent range the actual moment is finite exactly
when the canonical field belongs to Lᵖ; measurability is proved internally. -/
theorem correctorGradient_memLp_iff_finite_moment {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) {p : ℝ} (hp : 0 < p) :
    MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p) (reducedLaw Q) ↔
      (∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ p) ∂reducedLaw Q) < ⊤ := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    (Lp.stronglyMeasurable (correctorGradient Q i)).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le]
  have heq : (∫⁻ ω, ENNReal.ofReal (‖correctorGradient Q i ω‖ ^ p) ∂reducedLaw Q) =
      ∫⁻ ω, ‖correctorGradient Q i ω‖ₑ ^ p ∂reducedLaw Q := by
    apply lintegral_congr
    intro ω
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ofReal_norm]
  rw [heq]

/-- For any nonzero finite spatial measure, finiteness of the annealed local
moment is equivalent to genuine Lᵖ membership of the frozen gradient. -/
theorem correctorGradient_memLp_iff_finite_spatial_moment
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] (hν : ν Set.univ ≠ 0)
    {p : ℝ} (hp : 0 < p) :
    MemLp (fun ω => correctorGradient Q i ω) (ENNReal.ofReal p) (reducedLaw Q) ↔
      (∫⁻ ω, ∫⁻ x, ENNReal.ofReal
        (‖correctorGradient Q i (translate x ω)‖ ^ p) ∂ν ∂reducedLaw Q) < ⊤ := by
  rw [correctorGradient_memLp_iff_finite_moment Q i hp,
    lintegral_correctorGradient_spatial_moment]
  constructor
  · exact ENNReal.mul_lt_top (measure_lt_top ν Set.univ)
  · intro h
    rcases ENNReal.mul_lt_top_iff.mp h with h | h | h
    · exact h.2
    · exact (hν h).elim
    · rw [h]
      exact ENNReal.zero_lt_top

/-- Up to exponent two the real norm moment is genuinely integrable, so the
Bochner integral is not using its nonintegrability fallback. -/
theorem integrable_correctorGradient_translate_norm_rpow_of_le_two
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) (z : Vec d)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    Integrable (fun ω => ‖correctorGradient Q i (translate z ω)‖ ^ p) (reducedLaw Q) := by
  have hmem := correctorGradient_translate_memLp_of_le_two Q i z
    (p := ENNReal.ofReal p) (by exact_mod_cast hp2)
  have hint := hmem.integrable_norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hp.le] using hint

end EinsteinFull
