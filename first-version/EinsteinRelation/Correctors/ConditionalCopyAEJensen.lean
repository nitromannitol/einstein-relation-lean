import EinsteinRelation.Correctors.CorrectorConditionalFromCopyBounds

/-! # Conditional-copy comparison for almost-everywhere representatives

Source: `paper/main.tex:886–894`. Changes on a null set of environments
preserve both the conditional error and the literal copy difference.
Consequently the comparison requires only almost-everywhere measurability
of the centered observables.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance aeJensenRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Both actual conditional copies preserve a marginal a.e. equality.
Source: `paper/main.tex:886–894`. -/
theorem reducedConditionalCopy_ae_pair_congr {d : ℕ} {E : Type*}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U : Set (Vec d)) (hU : IsOpen U) {f g : FieldPair d → E}
    (hfg : f =ᵐ[μ] g) :
    ∀ᵐ z ∂reducedConditionalCopyLaw μ U,
      f z.2.1 = g z.2.1 ∧ f z.2.2 = g z.2.2 := by
  obtain ⟨_, h₁, h₂, _⟩ := reducedConditionalCopy_properties μ U hU
  have hfirst : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.1)
      (reducedConditionalCopyLaw μ U) μ := ⟨measurable_fst.comp measurable_snd, h₁⟩
  have hsecond : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.2)
      (reducedConditionalCopyLaw μ U) μ := ⟨measurable_snd.comp measurable_snd, h₂⟩
  exact (hfirst.quasiMeasurePreserving.ae hfg).and
    (hsecond.quasiMeasurePreserving.ae hfg)

/-- Scalar conditional-copy Jensen is invariant under a.e. replacement.
Source: `paper/main.tex:886–894`. -/
theorem eLpNorm_reduced_conditional_error_le_copy_difference_ae {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U : Set (Vec d)) (hU : IsOpen U) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : FieldPair d → ℝ} (hfm : AEStronglyMeasurable f μ) (hfi : Integrable f μ) :
    eLpNorm (f - condExp (Carriers.reducedCoefficientObservationSigma U) μ f) p μ ≤
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
        f z.2.1 - f z.2.2) p (reducedConditionalCopyLaw μ U) := by
  have he := hfm.ae_eq_mk
  have hc := condExp_congr_ae (m := Carriers.reducedCoefficientObservationSigma U) he
  have hl := eLpNorm_congr_ae (p := p) (he.sub hc)
  have hr := eLpNorm_congr_ae (p := p)
    ((reducedConditionalCopy_ae_pair_congr μ U hU he).mono fun z hz =>
      congrArg₂ (· - ·) hz.1 hz.2)
  rw [hl, hr]
  exact eLpNorm_reduced_conditional_error_le_copy_difference μ U hU hp hpt
    hfm.measurable_mk (hfi.congr he)

/-- The Frobenius comparison also needs only an a.e. measurable tensor.
Source: `paper/main.tex:886–894`. -/
theorem eLpNorm_reduced_conditional_frobenius_le_copy_difference_ae {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (U : Set (Vec d)) (hU : IsOpen U) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {f : FieldPair d → Mat d} (hfm : AEStronglyMeasurable f μ)
    (hfi : ∀ a b, Integrable (fun ω => f ω a b) μ) :
    eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun a b => f ω a b -
      condExp (Carriers.reducedCoefficientObservationSigma U) μ
        (fun ω' => f ω' a b) ω))) p μ ≤
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
        frobeniusNorm (f z.2.1 - f z.2.2)) p (reducedConditionalCopyLaw μ U) := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  have he := hfm.ae_eq_mk
  have hec (a b : Fin d) : (fun ω => f ω a b) =ᵐ[μ]
      fun ω => hfm.mk f ω a b := he.mono fun ω hω => congrFun (congrFun hω a) b
  have hc (a b : Fin d) := condExp_congr_ae
    (m := Carriers.reducedCoefficientObservationSigma U) (hec a b)
  have hl : eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun a b => f ω a b -
      condExp (Carriers.reducedCoefficientObservationSigma U) μ
        (fun ω' => f ω' a b) ω))) p μ =
      eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun a b => hfm.mk f ω a b -
      condExp (Carriers.reducedCoefficientObservationSigma U) μ
        (fun ω' => hfm.mk f ω' a b) ω))) p μ := by
    apply eLpNorm_congr_ae
    filter_upwards [he, ae_all_iff.mpr fun a => ae_all_iff.mpr (hc a)] with ω hω hcond
    simp only [hω, hcond]
  have hr : eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
      frobeniusNorm (f z.2.1 - f z.2.2)) p (reducedConditionalCopyLaw μ U) =
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
      frobeniusNorm (hfm.mk f z.2.1 - hfm.mk f z.2.2)) p
        (reducedConditionalCopyLaw μ U) := by
    apply eLpNorm_congr_ae
    filter_upwards [reducedConditionalCopy_ae_pair_congr μ U hU he] with z hz
    rw [hz.1, hz.2]
  rw [hl, hr]
  exact eLpNorm_reduced_conditional_frobenius_le_copy_difference μ U hU hp hpt
    hfm.measurable_mk (fun a b => (hfi a b).congr (hec a b))

end EinsteinRelation.Correctors
