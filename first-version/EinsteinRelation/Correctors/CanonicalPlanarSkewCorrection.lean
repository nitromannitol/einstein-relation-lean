import EinsteinRelation.Correctors.CanonicalPlanarScalarCorrection
import EinsteinRelation.Correctors.CanonicalPlanarSkewTranslation
import EinsteinRelation.Correctors.CanonicalConditionalSkewCorrection
import EinsteinRelation.Correctors.CoordinateMomentProjections

/-! # Planar cancellation for the literal skew correction

Source: `paper/main.tex:948–963`. The source Frobenius tail and the
existing AKM shifted-mean bound control the actual common conditional field.
Integrability of the source columns follows from the tail estimate.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

local instance : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- Finite Frobenius conditional-tail moments imply integrability of each
source column. Source: `paper/main.tex:956–963`. -/
theorem integrable_columns_of_frobenius_conditional_tail_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {d : ℕ} (m : MeasurableSpace Ω) (f : Ω → Mat d)
    (hf : ∀ j k, @AEStronglyMeasurable Ω ℝ _ mΩ mΩ (fun ω => f ω j k) μ)
    {p A : ℝ} (hp : 1 ≤ p)
    (ht : eLpNorm (fun ω => frobeniusNorm (fun j k => f ω j k -
      μ[fun a => f a j k | m] ω)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A) :
    ∀ k, Integrable (fun ω j => f ω j k) μ := by
  letI : MeasurableSpace Ω := mΩ
  intro k
  apply integrable_pi_iff.mpr
  intro j
  apply integrable_of_conditional_tail_bound m (hf j k) hp
  exact (eLpNorm_entry_le (fun ω a b => f ω a b -
    μ[fun c => f c a b | m] ω) j k).trans ht

/-- The normalized heat-selected planar source gives the sharp
inverse-radius bound for the common field's literal skew correction.
Continuity and normalization are internal source-construction obligations.
Source: `paper/main.tex:948–963`. -/
theorem canonicalConditionalMollifierFields_planar_skewCorrection_of_literature
    (hAKM : CorrectorWeakH2) (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ p A : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 1 ≤ p) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ) (hR : 1 ≤ R)
      (i : Fin 2) (u : FieldPair 2 → Vec 2 → ℝ) (S : FieldPair 2 → Vec 2 → Mat 2),
      IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier 2) R hR 0
        (fun ω x => u ω x.ofLp) →
      HasHeatSelectedSkewCorrectorColumn (by omega) Q i S →
      (∀ j k, StronglyMeasurable (fun z : FieldPair 2 × Vec 2 => S z.1 z.2 j k)) →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (S ω)) →
      (∀ j k, ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        (∫ z, S ω (-z) j k ∂mollifierCenterMeasure 2 R) = 0) →
      eLpNorm (fun ω => frobeniusNorm (fun j k => S ω 0 j k -
        (reducedEnvironmentLaw Q)[fun a => S a 0 j k |
          reducedCoefficientObservationSigma
            {z : Vec 2 | euclideanNorm (z - 0) < 8 * R}] ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A →
      MemLp (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹) := by
  obtain ⟨B, hB, hshift⟩ := canonical_planar_source_shifted_means_of_literature
    hAKM hP L r₀ p hL hr₀ hp
  obtain ⟨W, hW, hbound⟩ := canonicalConditionalMollifierFields_skewCorrection_bound 2
  refine ⟨2 * (2 * A + B) * W, by positivity, ?_⟩
  intro Q R hR i u S hu hS hSm hSc hSn htail
  have hSvalue (x : Vec 2) (k : Fin 2) : Measurable (fun ω j => S ω x j k) := by
    apply measurable_pi_lambda
    intro j
    exact (hSm j k).measurable.comp (measurable_id.prodMk measurable_const)
  have hf := integrable_columns_of_frobenius_conditional_tail_bound _ (fun ω => S ω 0)
    (fun j k => ((hSm j k).measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable) hp htail
  let g : Fin 2 → Vec 2 → FieldPair 2 → Vec 2 := fun k y ω j => ∫ z,
    (Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k
  have hgm (k : Fin 2) (y : Vec 2) : Measurable (g k y) := by
    apply measurable_pi_lambda
    intro j
    have hζ := (Entropy.contDiff_unitMassScaledMollifier (d := 2) R).continuous.measurable
    have hm : Measurable (fun z : FieldPair 2 × Vec 2 =>
        (Calculus.unitMassScaledMollifier 2 R z.2 -
          Calculus.unitMassScaledMollifier 2 R (z.2 - y)) * S z.1 z.2 j k) :=
      ((hζ.comp measurable_snd).sub
        (hζ.comp (measurable_snd.sub measurable_const))).mul (hSm j k).measurable
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hg (k : Fin 2) (y : Vec 2) (hy : euclideanNorm y ≤ R) :
      MemLp (fun ω => euclideanNorm (g k y ω)) (ENNReal.ofReal p)
          (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (g k y ω)) (ENNReal.ofReal p)
          (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B :=
    (hshift Q i (canonicalSourceMollifier 2) R hR 0
      (fun ω x => u ω x.ofLp) S hu hS R hR y hy).2 k
  have hgi (k : Fin 2) (y : Vec 2) (hy : euclideanNorm y ≤ R) :
      Integrable (g k y) (reducedEnvironmentLaw Q) := by
    apply (MemLp.mono' (hg k y hy).1 (hgm k y).aestronglyMeasurable
      (ae_of_all _ fun ω => Entropy.norm_le_euclideanNorm'' (g k y ω))).integrable
    exact ENNReal.one_le_ofReal.mpr hp
  have hsource (k : Fin 2) (y : Vec 2) :
      (fun ω j => S (translate y ω) (-y) j k) =ᵐ[reducedEnvironmentLaw Q]
        (fun ω j => S ω 0 j k) + g k y := by
    filter_upwards [ae_normalizedPlanarSkew_translation Q i hR S hS hSc hSn y] with ω hω
    exact congrArg (fun M : Mat 2 => fun j => M j k) hω
  have hSi (k : Fin 2) (y : {y : Vec 2 // euclideanNorm y ≤ R}) :
      Integrable (fun ω j => S ω (-y.1) j k) (reducedEnvironmentLaw Q) := by
    have hpres : MeasurePreserving (translate y.1)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
    apply (hpres.integrable_comp (hSvalue (-y.1) k).aestronglyMeasurable).mp
    exact ((hf k).add (hgi k y.1 y.2)).congr (hsource k y.1).symm
  simpa only [Nat.cast_ofNat] using hbound Q i hR u S hSm hSi (fun ω => S ω 0) hf
    (fun k y => g k y.1) (fun k y => hgi k y.1 y.2)
    (fun k y => hsource k y.1) p A B hp hA hB.le (fun k y => (hg k y.1 y.2).2) htail

end EinsteinRelation.Correctors
