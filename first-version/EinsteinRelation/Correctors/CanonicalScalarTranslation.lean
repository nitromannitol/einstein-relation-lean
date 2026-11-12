import EinsteinRelation.Correctors.NormalizedPotentialTranslation
import EinsteinRelation.Correctors.NormalizedScalarMollifierMean

/-! # Translation identity for the actual normalized scalar corrector

Source: `paper/main.tex:948–963`. The normalized scalar corrector has a
stationary weak gradient. A continuous representative therefore satisfies
the precise shifted-mean decomposition used by planar cancellation.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- The reflected center-measure zero mean is the ordinary mollifier zero
mean, by Haar invariance under negation. Source: `paper/main.tex:913–925`. -/
theorem mollifier_mean_eq_zero_of_centerMean {d : ℕ} {R : ℝ} (hR : 0 < R)
    (u : Vec d → ℝ) (hu : (∫ y, u (-y) ∂mollifierCenterMeasure d R) = 0) :
    (∫ z, Calculus.unitMassScaledMollifier d R z * u z) = 0 := by
  rw [integral_mollifierCenterMeasure hR] at hu
  rw [← integral_neg_eq_self (fun z => Calculus.unitMassScaledMollifier d R z * u z)]
  exact hu

/-- The translated normalized potential equals its value at zero plus the
literal shifted mean. Only continuity of the chosen representative is an
internal selection obligation. Source: `paper/main.tex:948–963`. -/
theorem ae_normalizedCanonicalScalar_translation
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 1 ≤ R)
    (u : FieldPair d → Vec d → ℝ)
    (hu : IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d)
      R hR 0 (fun ω x => u ω x.ofLp))
    (huc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (u ω)) (y : Vec d) :
    (fun ω => u (translate y ω) (-y)) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => u ω 0 + ∫ z, (Calculus.unitMassScaledMollifier d R z -
        Calculus.unitMassScaledMollifier d R (z - y)) * u ω z) := by
  have hpres : MeasurePreserving (translate y)
      (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
    ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
  have hn := normalizedCanonicalScalar_mollifierCenterMean_eq_zero Q i hR u hu
  filter_upwards [hu.2, hpres.quasiMeasurePreserving.ae hu.2, huc, hpres.quasiMeasurePreserving.ae huc, hn, hpres.quasiMeasurePreserving.ae hn]
    with ω hw hv hcw hcv hnw hnv
  obtain ⟨_, hwu, _⟩ := hw
  obtain ⟨_, hwv, _⟩ := hv
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  apply normalized_weakPotential_translation hd (zero_lt_one.trans_le hR) y
    (u ω) (u (translate y ω)) _ hwu
  · simpa only [StationarySpatialRealization.spatialRealization, translate_add,
      add_comm] using hwv
  · exact hcw
  · exact hcv
  · exact mollifier_mean_eq_zero_of_centerMean (zero_lt_one.trans_le hR) _ hnw
  · exact mollifier_mean_eq_zero_of_centerMean (zero_lt_one.trans_le hR) _ hnv

end EinsteinRelation.Correctors
