import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
import EinsteinRelation.Correctors.WeakGradientCentering
import Mathlib.MeasureTheory.Integral.Prod

/-! Source: `paper/main.tex:694-704,762-766`. An actual jointly
measurable continuous weak potential can be normalized by the prescribed
source mollifier, preserving its gradient and spatial continuity. -/

open MeasureTheory

noncomputable section
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- Subtract the prescribed mollifier mean of the actual weak potential. -/
def normalizedScalarSelection {d : ℕ} {Ω : Type*}
    (f : Ω → Vec d → ℝ) (ζ : SourceMollifier d) (R : ℝ)
    (hR : 1 ≤ R) (y : Point d) (ω : Ω) (x : Point d) : ℝ :=
  f ω x.ofLp - ∫ z : Point d,
    (sourceScaledSpatialKernel ζ R y hR).density z * f ω z.ofLp

/-- Mollifier centering preserves joint measurability. -/
theorem measurable_normalizedScalarSelection {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Vec d → ℝ)
    (hf : Measurable (fun p : Vec d × Ω => f p.2 p.1))
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    Measurable (fun p : Vec d × Ω =>
      normalizedScalarSelection f ζ R hR y p.2 (WithLp.toLp 2 p.1)) := by
  have hm : Measurable (fun p : Ω × Point d =>
      (sourceScaledSpatialKernel ζ R y hR).density p.2 * f p.1 p.2.ofLp) := by
    exact ((sourceScaledSpatialKernel ζ R y hR).density.continuous.measurable.comp
      measurable_snd).mul (hf.comp (((PiLp.continuous_ofLp (p := 2)
        (β := fun _ : Fin d => ℝ)).measurable.comp measurable_snd).prodMk measurable_fst))
  have hi : Measurable (fun ω : Ω => ∫ z : Point d,
      (sourceScaledSpatialKernel ζ R y hR).density z * f ω z.ofLp) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  simpa only [normalizedScalarSelection, WithLp.ofLp_toLp] using hf.sub (hi.comp measurable_snd)

/-- A jointly measurable continuous potential with the canonical weak
gradient produces the literal normalized scalar predicate. -/
theorem normalizedScalarSelection_isNormalizedCanonicalScalarCorrector
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (f : FieldPair d → Vec d → ℝ)
    (hf : Measurable (fun p : Vec d × FieldPair d => f p.2 p.1))
    (hw : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (f ω) ∧
      HasWeakGradient Set.univ (f ω) (fun x =>
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x ω)).ofLp))
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    IsNormalizedCanonicalScalarCorrector Q i ζ R hR y
      (normalizedScalarSelection f ζ R hR y) ∧
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (normalizedScalarSelection f ζ R hR y ω) := by
  have hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      Continuous (normalizedScalarSelection f ζ R hR y ω) := by
    filter_upwards [hw] with ω hω
    exact (hω.1.comp (PiLp.continuous_ofLp (p := 2)
      (β := fun _ : Fin d => ℝ))).sub continuous_const
  refine ⟨⟨measurable_normalizedScalarSelection f hf ζ R hR y, ?_⟩, hc⟩
  filter_upwards [hw, hc] with ω hω hcω
  let w := sourceScaledSpatialKernel ζ R y hR
  have hfc : Continuous (fun x : Point d => f ω x.ofLp) :=
    hω.1.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ))
  let ψ : ScalarSpatialPotential d := ⟨fun x => f ω x.ofLp, hfc.locallyIntegrable⟩
  let ψ' : ScalarSpatialPotential d :=
    ⟨normalizedScalarSelection f ζ R hR y ω, hcω.locallyIntegrable⟩
  refine ⟨hcω.locallyIntegrable, ?_, ?_⟩
  · simpa only [normalizedScalarSelection, WithLp.ofLp_toLp] using
      hasWeakGradient_sub_const Set.univ hω.2
        (∫ z : Point d, w.density z * f ω z.ofLp)
  · have hg : Quotient.mk (spatialGaugeSetoid d ℝ) ψ' =
        Quotient.mk (spatialGaugeSetoid d ℝ) ψ := by
      apply Quotient.sound
      refine ⟨-(mollifierMean w ψ), ae_of_all _ (fun x => ?_)⟩
      change f ω x.ofLp - mollifierMean w ψ = f ω x.ofLp + -mollifierMean w ψ
      ring
    change sourceMollifierNormalize ζ R hR y
      (Quotient.mk (spatialGaugeSetoid d ℝ) ψ') =
      Quotient.mk (spatialAESetoid d ℝ) ψ'
    rw [hg]
    rfl

end EinsteinRelation.Correctors
