import EinsteinRelation.Correctors.CorrectorConditionalFromCopyBounds
import EinsteinRelation.Correctors.NormalizedScalarMollifierMean
import EinsteinRelation.Correctors.CanonicalScalarTranslation
import EinsteinRelation.Correctors.P53SourceSkewScalarPotential

/-! # Lemma 5.2 tails for the literal normalized source values

Source: `paper/main.tex:774–786,948–973`. Normalization identifies the
centered observables in Lemma 5.2 with the source values at the origin.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport
open HeatSelectedSkewMeaning StationarySpatialRealization

local instance : Fact (2 ≤ (2 : ℕ)) := ⟨le_rfl⟩

/-- The two source-carrier versions of the mollifier average coincide.
Source: `paper/main.tex:762–764`. -/
theorem integral_canonicalSourceKernel_eq_centerMean {d : ℕ} {R : ℝ}
    (hR : 0 < R) (v : Vec d → ℝ) :
    (∫ x : Point d, sourceScaledMollifierKernel (canonicalSourceMollifier d) R 0 x *
      v x.ofLp) = ∫ y, v (-y) ∂mollifierCenterMeasure d R := by
  rw [integral_mollifierCenterMeasure hR]
  have hneg := (Measure.measurePreserving_neg (volume : Measure (Vec d))).integral_comp
    (Homeomorph.neg (Vec d)).measurableEmbedding
    (fun x => Calculus.unitMassScaledMollifier d R x * v x)
  rw [hneg]
  have ht := (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv.measurableEmbedding
    (fun x => Calculus.unitMassScaledMollifier d R x * v x)
  rw [← ht]
  apply integral_congr_ae
  filter_upwards [] with x
  have hk := canonicalSourceKernel_eq_coordinateMollifier R (0 : Vec d) x.ofLp
  simpa only [WithLp.toLp_zero, WithLp.toLp_ofLp, sub_zero] using
    congrArg (fun a : ℝ => a * v x.ofLp) hk

/-- The source observation ball at zero has the literal Euclidean formula.
Source: `paper/main.tex:774–776`. -/
theorem conditionalCorrectorBall_zero {d : ℕ} (R : ℝ) :
    conditionalCorrectorBall (d := d) R 0 =
      {z : Vec d | euclideanNorm (z - 0) < 8 * R} := by
  ext z
  simp only [conditionalCorrectorBall, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball,
    dist_zero_right, sub_zero, TimeChange.euclideanNorm_eq_norm_toLp]

/-- The conditional gradient at zero is the original environment-space
representative. Source: `paper/main.tex:774–776`. -/
theorem conditionalCorrectorGradient_zero {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    conditionalCorrectorGradient Q i 0 = fun ω =>
      ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) ω).ofLp := by
  funext ω
  simp only [conditionalCorrectorGradient, WithLp.ofLp_zero, spatialRealization,
    translate_zero]

/-- The two conditional centered errors in dimension two control the
literal origin tails of the same normalized scalar and skew sources.
Source: `paper/main.tex:778–786,948–963`. -/
theorem canonical_planar_origin_tails_of_correctorConditional
    (h52 : CorrectorConditionalStatement) {L r₀ p : ℝ} (hp : 2 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ) (hR : 1 ≤ R)
      (i : Fin 2) (u : FieldPair 2 → Vec 2 → ℝ) (S : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier 2) R hR 0
        (fun ω x => u ω x.ofLp) →
      HasHeatSelectedSkewCorrectorColumn (by norm_num) Q i S →
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S ω (-z) j k ∂mollifierCenterMeasure 2 R) = 0) →
      eLpNorm ((fun ω => u ω 0) - (reducedEnvironmentLaw Q)[fun ω => u ω 0 |
        Carriers.reducedCoefficientObservationSigma
          {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}])
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A ∧
      eLpNorm (fun ω => frobeniusNorm (fun j k => S ω 0 j k -
        (reducedEnvironmentLaw Q)[fun a => S a 0 j k |
          Carriers.reducedCoefficientObservationSigma
            {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}] ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A := by
  obtain ⟨C, hb⟩ := h52 2 L r₀ (canonicalSourceMollifier 2) p hp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro Q R hR i u S hu hS hSn
  have h := (hb Q R hR 0 i (fun ω x => u ω x.ofLp) S hu hS).2 rfl
  dsimp only at h
  let μ := reducedEnvironmentLaw Q
  let obs := Carriers.reducedCoefficientObservationSigma (conditionalCorrectorBall (d := 2) R 0)
  let cφ := conditionalCenteredScalar (canonicalSourceMollifier 2) R 0
    (fun ω x => u ω x.ofLp)
  let cσ := conditionalCenteredSkew (canonicalSourceMollifier 2) R 0 S
  have hφ : cφ =ᵐ[μ] (fun ω => u ω 0) := by
    filter_upwards [normalizedCanonicalScalar_mollifierCenterMean_eq_zero Q i hR u hu]
      with ω hω
    simp only [cφ, conditionalCenteredScalar, WithLp.ofLp_zero,
      integral_canonicalSourceKernel_eq_centerMean (zero_lt_one.trans_le hR), hω, sub_zero]
  have hσ (j k : Fin 2) : (fun ω => cσ ω j k) =ᵐ[μ] (fun ω => S ω 0 j k) := by
    filter_upwards [hSn j k] with ω hω
    change S ω 0 j k - (∫ z : Point 2,
      sourceScaledMollifierKernel (canonicalSourceMollifier 2) R 0 z * S ω z.ofLp j k) = _
    rw [integral_canonicalSourceKernel_eq_centerMean (zero_lt_one.trans_le hR)
      (fun x => S ω x j k), hω, sub_zero]
  have hs := condExp_congr_ae (m := obs) hφ
  have ht := ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
    (hσ j k).and (condExp_congr_ae (m := obs) (hσ j k))
  have heqφ : eLpNorm (fun ω => cφ ω - condExp obs μ cφ ω) (ENNReal.ofReal p) μ =
      eLpNorm ((fun ω => u ω 0) - condExp obs μ (fun ω => u ω 0))
        (ENNReal.ofReal p) μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hφ, hs] with ω hω hc
    exact congrArg₂ (· - ·) hω hc
  have heqσ : eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun j k => cσ ω j k -
      condExp obs μ (fun a => cσ a j k) ω))) (ENNReal.ofReal p) μ =
      eLpNorm (fun ω => frobeniusNorm (fun j k => S ω 0 j k -
        condExp obs μ (fun a => S a 0 j k) ω)) (ENNReal.ofReal p) μ := by
    apply eLpNorm_congr_ae
    filter_upwards [ht] with ω hω
    congr 1
    funext j k
    exact congrArg₂ (· - ·) (hω j k).1 (hω j k).2
  change eLpNorm (fun ω => cφ ω - condExp obs μ cφ ω) _ μ +
    eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun j k => cσ ω j k -
      condExp obs μ (fun a => cσ a j k) ω))) _ μ ≤ _ at h
  rw [heqφ, heqσ] at h
  dsimp only [obs, μ] at h
  rw [conditionalCorrectorBall_zero] at h
  exact ⟨(le_add_right le_rfl |>.trans h).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
    (le_add_left le_rfl |>.trans h).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩

/-- Lemma 5.2 supplies the literal canonical-gradient tail, once an actual
skew source exists. The scalar source is supplied by proved existence.
Source: `paper/main.tex:774–776,968–973`. -/
theorem canonical_gradient_origin_tail_of_correctorConditional
    (h52 : CorrectorConditionalStatement)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hp : 2 ≤ p)
    (hskew : ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      ∃ S : FieldPair d → Vec d → Mat d,
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i S) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
      eLpNorm (fun ω => euclideanNorm
        (((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ω).ofLp -
          (reducedEnvironmentLaw Q)[fun a =>
            ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
              (reducedEnvironmentLaw Q)) a).ofLp |
            Carriers.reducedCoefficientObservationSigma
              {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (A * R ^ (-(d : ℝ) / 2)) := by
  obtain ⟨C, hb⟩ := h52 d L r₀ (canonicalSourceMollifier d) p hp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro Q R hR i
  obtain ⟨φ, hφ⟩ := exists_normalizedCanonicalScalarCorrector hP Q i
    (canonicalSourceMollifier d) R hR 0
  obtain ⟨S, hS⟩ := hskew Q R hR i
  have h := (hb Q R hR 0 i φ S hφ hS).1
  rw [conditionalCorrectorGradient_zero, conditionalCorrectorBall_zero] at h
  exact h.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg
      (zero_le_one.trans hR) _)))

end EinsteinRelation.Correctors
