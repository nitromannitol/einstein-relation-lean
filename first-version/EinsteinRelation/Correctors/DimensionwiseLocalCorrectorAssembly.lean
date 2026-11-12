import EinsteinRelation.Correctors.LocalCorrectorFieldAssembly

/-! # Dimensionwise assembly of Proposition 5.3

Source: `paper/main.tex:895–906,921–938,968–977`. The same five families
are chosen before the moment exponent. Uniform separate estimates and the
actual spatial equations give the production local-corrector construction.
All supplied field estimates are internal obligations. Families are defined
only in the source dimension range; no extension to smaller dimensions is needed.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation

open Correctors

/-- Assemble the production local-corrector construction from spatial fields.
The fields are fixed before `m`, while every estimate constant is fixed before
the environment law and radius. Source: `paper/main.tex:895–906,921–938,968–977`.
This theorem does not construct the source scalar or heat-selected skew field. -/
theorem correctorLocalConstruction_of_dimensionwise_spatial_fields
    (fields : ∀ {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}, EnvironmentLaw d L r₀ → ℝ → Fin d →
      LocalCorrectorFields d)
    (hlocal : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀)
      (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      let f := fields Q R i
      let obs := Carriers.reducedCoefficientObservationSigma
        {y : Vec d | euclideanNorm (y - 0) < 33 * R}
      Measurable[obs] f.scalar ∧ Measurable[obs] f.skew ∧
        Measurable[obs] f.gradientAverage ∧ Measurable[obs] f.scalarCorrection ∧
        Measurable[obs] f.skewCorrection)
    (hskew : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀)
      (R : ℝ), 1 ≤ R → ∀ (i : Fin d) (ω : FieldPair d),
        ((fields Q R i).skew ω).transpose = -(fields Q R i).skew ω)
    (hspatial : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀)
      (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      let f := fields Q R i
      ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        HasWeakGradient Set.univ (orbit f.scalar ω)
          (fun x => f.gradient (translate x ω)) ∧
        HasWeakRowDivergence Set.univ (fun x => f.skew (translate x ω))
          (fun x => (ω.1 x).mulVec (unitVector i + f.gradient (translate x ω)) -
            (expectedCorrectorFlux Q i).ofLp - f.flux (translate x ω)))
    (hamplitude : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        eLpNorm (fields Q R i).scalar (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
          eLpNorm (fun ω => frobeniusNorm ((fields Q R i).skew ω))
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * correctorAmplitude d R))
    (haverage : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ m : ℝ), 2 ≤ m →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        eLpNorm (fun ω => euclideanNorm ((fields Q R i).gradientAverage ω -
          ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) ω).ofLp))
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
            ENNReal.ofReal (2 * (A * R ^ (-(d : ℝ) / 2))))
    (hscalarCorrection : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ m : ℝ), 2 ≤ m →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        eLpNorm (fun ω => euclideanNorm ((fields Q R i).scalarCorrection ω))
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (B * R⁻¹))
    (hskewCorrection : ∀ (d : ℕ) [Fact (2 ≤ d)], ∀ (L r₀ m : ℝ), 2 ≤ m →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        eLpNorm (fun ω => euclideanNorm ((fields Q R i).skewCorrection ω))
          (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (D * R⁻¹)) :
    CorrectorLocalConstruction := by
  intro d hd L r₀
  letI : Fact (2 ≤ d) := ⟨hd⟩
  have hobs (R : ℝ) : Carriers.reducedCoefficientObservationSigma
      {y : Vec d | euclideanNorm (y - 0) < 33 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {y : Vec d | euclideanNorm (y - 0) < 33 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hmeas (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 1 ≤ R) (i : Fin d) :
      Measurable (fields Q R i).scalar ∧ Measurable (fields Q R i).skew ∧
        Measurable (fields Q R i).gradientAverage ∧
        Measurable (fields Q R i).scalarCorrection ∧ Measurable (fields Q R i).skewCorrection := by
    obtain ⟨hφ, hS, hV, hH, hK⟩ := hlocal d L r₀ Q R hR i
    exact ⟨hφ.mono (hobs R) le_rfl, hS.mono (hobs R) le_rfl,
      hV.mono (hobs R) le_rfl, hH.mono (hobs R) le_rfl, hK.mono (hobs R) le_rfl⟩
  have herror (m : ℝ) (hm : 2 ≤ m) : ∃ E : ℝ,
      ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        eLpNorm (fun ω => euclideanNorm ((fields Q R i).flux ω))
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
          eLpNorm (fun ω => euclideanNorm ((fields Q R i).gradient ω -
            ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
              (reducedEnvironmentLaw Q)) ω).ofLp))
            (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (E * R⁻¹) := by
    obtain ⟨A, hA, hV⟩ := haverage d L r₀ m hm
    obtain ⟨B, hB, hH⟩ := hscalarCorrection d L r₀ m hm
    obtain ⟨D, hD, hK⟩ := hskewCorrection d L r₀ m hm
    refine ⟨(Real.exp (2 * L) * L) * B + D + (2 * A + B), ?_⟩
    intro Q R hR i
    obtain ⟨_, _, hVm, hHm, hKm⟩ := hmeas Q R hR i
    exact (fields Q R i).error_rate hd Q
      (fun ω => ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) ω).ofLp)
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous.measurable.comp
        (Lp.stronglyMeasurable _).measurable)
      (one_le_two.trans hm) hR hA hB hD hVm hHm hKm
      (hV Q R hR i) (hH Q R hR i) (hK Q R hR i)
  refine ⟨(fun Q R i => (fields Q R i).scalar), (fun Q R i => (fields Q R i).skew),
    (fun Q R i => (fields Q R i).flux), (fun Q R i => (fields Q R i).gradient), ?_, ?_⟩
  · intro Q R hR i
    obtain ⟨hφ, hS, hV, hH, hK⟩ := hlocal d L r₀ Q R hR i
    have hF := measurable_local_flux_error (x := (0 : Vec d))
      (show (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - 0) < 33 * R} by
        change euclideanNorm ((0 : Vec d) - 0) < 33 * R
        simp only [sub_self, TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_zero, norm_zero]
        linarith) hH hK
    refine ⟨⟨hφ, hS, hF, hV.add hH⟩, hskew d L r₀ Q R hR i, ?_⟩
    obtain ⟨C, hC⟩ := hamplitude d L r₀ 2 le_rfl
    obtain ⟨E, hE⟩ := herror 2 le_rfl
    have ha := hC Q R hR i
    have he := hE Q R hR i
    have hφfinite := (le_add_right le_rfl : eLpNorm (fields Q R i).scalar
      (ENNReal.ofReal 2) (reducedEnvironmentLaw Q) ≤ _).trans_lt
        (ha.trans_lt ENNReal.ofReal_lt_top)
    have hSfinite := (le_add_left le_rfl : eLpNorm (fun ω => frobeniusNorm
      ((fields Q R i).skew ω)) (ENNReal.ofReal 2) (reducedEnvironmentLaw Q) ≤ _).trans_lt
        (ha.trans_lt ENNReal.ofReal_lt_top)
    have hFfinite := (le_add_right le_rfl : eLpNorm (fun ω => euclideanNorm
      ((fields Q R i).flux ω)) (ENNReal.ofReal 2) (reducedEnvironmentLaw Q) ≤ _).trans_lt
        (he.trans_lt ENNReal.ofReal_lt_top)
    have hGfinite := (le_add_left le_rfl : eLpNorm (fun ω => euclideanNorm
      ((fields Q R i).gradient ω - ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp))
      (ENNReal.ofReal 2) (reducedEnvironmentLaw Q) ≤ _).trans_lt
        (he.trans_lt ENNReal.ofReal_lt_top)
    obtain ⟨hφm, hSm, hVm, hHm, _⟩ := hmeas Q R hR i
    exact (fields Q R i).horizontal_equations Q i hφm hSm hVm hHm
      (hF.mono (hobs R) le_rfl)
      (by simpa using hφfinite) (by simpa using hSfinite)
      (by simpa using hGfinite) (by simpa using hFfinite) (hspatial d L r₀ Q R hR i)
  · intro m hm
    obtain ⟨C, hC⟩ := hamplitude d L r₀ m hm
    obtain ⟨E, hE⟩ := herror m hm
    refine ⟨max C E, ?_⟩
    intro Q R hR i
    constructor
    · exact (hC Q R hR i).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left C E) (by
          unfold correctorAmplitude
          split <;> positivity)))
    · simpa only [StationarySpatialRealization.spatialRealization, translate_zero] using
        (hE Q R hR i).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_right C E) (by positivity)))

end EinsteinRelation
