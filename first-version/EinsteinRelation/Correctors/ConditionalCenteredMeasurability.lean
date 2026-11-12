import EinsteinRelation.Correctors.CorrectorConditionalStatement
import Mathlib.MeasureTheory.Integral.Prod

/-! Literal centered observables retain joint measurability.
Source: `paper/main.tex:770–772,886–894`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- Joint measurability of the actual fields gives measurability of both
centered source observables. Source: `paper/main.tex:770–772,886–894`. -/
theorem measurable_conditionalCentered_of_joint {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (y : Point d)
    (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d)
    (hφ : Measurable (fun z : Vec d × FieldPair d => φ z.2 (WithLp.toLp 2 z.1)))
    (hσ : ∀ a b, Measurable (fun z : FieldPair d × Vec d => σ z.1 z.2 a b)) :
    Measurable (conditionalCenteredScalar ζ R y φ) ∧
      Measurable (conditionalCenteredSkew ζ R y σ) := by
  have hcoord : Measurable (WithLp.ofLp : Point d → Vec d) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable
  have hu : Measurable (fun z : FieldPair d × Point d => φ z.1 z.2) := by
    simpa only [WithLp.toLp_ofLp] using
      hφ.comp ((hcoord.comp measurable_snd).prodMk measurable_fst)
  have hw : Measurable (sourceScaledMollifierKernel ζ R y) :=
    (continuous_sourceScaledMollifierKernel ζ R y).measurable
  constructor
  · exact (hu.comp (measurable_id.prodMk measurable_const)).sub
      (((hw.comp measurable_snd).mul hu).stronglyMeasurable.integral_prod_right'.measurable)
  · have he (a b : Fin d) : Measurable (fun ω => conditionalCenteredSkew ζ R y σ ω a b) := by
      have hentry : Measurable (fun z : FieldPair d × Point d => σ z.1 z.2.ofLp a b) :=
        (hσ a b).comp (measurable_fst.prodMk (hcoord.comp measurable_snd))
      exact ((hσ a b).comp (measurable_id.prodMk measurable_const)).sub
        (((hw.comp measurable_snd).mul hentry).stronglyMeasurable.integral_prod_right'.measurable)
    have hpi : @Measurable _ (Fin d → Fin d → ℝ) _ MeasurableSpace.pi
        (conditionalCenteredSkew ζ R y σ) :=
      measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => he a b
    exact hpi.mono le_rfl (OpensMeasurableSpace.borel_le (α := Fin d → Fin d → ℝ))
end EinsteinRelation.Correctors
