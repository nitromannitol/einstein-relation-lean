import EinsteinRelation.Correctors.ConditionalSpatialMollifierMoment
import EinsteinRelation.Correctors.LocalMollifierSourceTransport
import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport

/-! # The normalized scalar has zero mollifier mean

Source: `paper/main.tex:762–764,913–925`. The quotient normalization in the
source-facing scalar predicate implies the literal coordinate integral is
zero almost surely. No pointwise representative choice is required.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport
open NormalizedScalarPhysicalLawTransportSupport

/-- Quotient normalization implies the literal zero mean used in the
source-moment bound. Source: `paper/main.tex:762–764,913–925`. -/
theorem normalizedCanonicalScalar_mollifierCenterMean_eq_zero
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 1 ≤ R)
    (u : FieldPair d → Vec d → ℝ)
    (hu : IsNormalizedCanonicalScalarCorrector Q i (canonicalSourceMollifier d)
      R hR 0 (fun ω x => u ω x.ofLp)) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (∫ y, u ω (-y) ∂mollifierCenterMeasure d R) = 0 := by
  filter_upwards [hu.2] with ω hω
  obtain ⟨hLI, _, hnorm⟩ := hω
  let f : ScalarSpatialPotential d := ⟨fun x => u ω x.ofLp, hLI⟩
  have hae : (mollifierCenteredRepresentative
      (sourceScaledSpatialKernel (canonicalSourceMollifier d) R 0 hR) f).value
      =ᵐ[volume] f.value := Quotient.exact hnorm
  have hz : (∫ x : Point d, sourceScaledMollifierKernel
      (canonicalSourceMollifier d) R 0 x * u ω x.ofLp ∂volume) = 0 := by
    calc
      _ = ∫ x : Point d, sourceScaledMollifierKernel
          (canonicalSourceMollifier d) R 0 x *
          (mollifierCenteredRepresentative
            (sourceScaledSpatialKernel (canonicalSourceMollifier d) R 0 hR) f).value x
          ∂volume := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        exact congrArg (fun a : ℝ =>
          sourceScaledMollifierKernel (canonicalSourceMollifier d) R 0 x * a) hx.symm
      _ = 0 := integral_sourceMollifierCenteredRepresentative_eq_zero
        (canonicalSourceMollifier d) R hR 0 f
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  rw [integral_mollifierCenterMeasure hR0]
  have hneg : (∫ y : Vec d, Calculus.unitMassScaledMollifier d R (-y) * u ω (-y)) =
      ∫ x : Vec d, Calculus.unitMassScaledMollifier d R x * u ω x := by
    exact (Measure.measurePreserving_neg volume).integral_comp
      (Homeomorph.neg (Vec d)).measurableEmbedding
      (fun x => Calculus.unitMassScaledMollifier d R x * u ω x)
  rw [hneg]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have ht := hmp.integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).toMeasurableEquiv.measurableEmbedding
    (fun x => Calculus.unitMassScaledMollifier d R x * u ω x)
  rw [← ht]
  convert hz using 1
  congr 1
  funext x
  have hk := canonicalSourceKernel_eq_coordinateMollifier R (0 : Vec d) x.ofLp
  simpa only [WithLp.toLp_zero, WithLp.toLp_ofLp, sub_zero] using
    congrArg (fun a : ℝ => a * u ω x.ofLp) hk.symm

end EinsteinRelation.Correctors
