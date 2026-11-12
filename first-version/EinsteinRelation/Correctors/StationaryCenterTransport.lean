import EinsteinRelation.Correctors.StationaryWeightedOrbit

/-! # Translating almost-sure local versions jointly with their centers

Source: `paper/main.tex:913–938`. Translation preserves the stationary
law jointly with a center variable. In particular a single almost-sure
center-zero PDE event transports to an actual product-almost-sure event;
no measurability assumption on an uncountable family of PDE tests is needed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

private def centerTranslateEquiv {d : ℕ} :
    (Vec d × FieldPair d) ≃ᵐ (Vec d × FieldPair d) where
  toFun p := (p.1, translate p.1 p.2)
  invFun p := (p.1, translate (-p.1) p.2)
  left_inv p := by
    dsimp only
    rw [translate_add, neg_add_cancel, translate_zero]
  right_inv p := by
    dsimp only
    rw [translate_add, add_neg_cancel, translate_zero]
  measurable_toFun := measurable_fst.prodMk Probability.continuous_translate.measurable
  measurable_invFun := measurable_fst.prodMk
    (Probability.continuous_translate.measurable.comp
      (measurable_fst.neg.prodMk measurable_snd))

/-- Keeping the center and translating the environment preserves their
product law. Source: `paper/main.tex:913–938`. -/
theorem measurePreserving_centerTranslate {d : ℕ}
    (ν : Measure (Vec d)) [SFinite ν]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q) :
    MeasurePreserving (fun p : Vec d × FieldPair d =>
      (p.1, translate p.1 p.2)) (ν.prod Q) (ν.prod Q) := by
  exact (MeasurePreserving.id ν).skew_product
    Probability.continuous_translate.measurable
    (Filter.Eventually.of_forall fun y => (measurePreserving_translate Q hQ y).map_eq)

/-- Any actual almost-sure event transports jointly in the center and
stationary environment, even when the event itself is not stated as a
measurable predicate. Source: `paper/main.tex:913–938`. -/
theorem ae_joint_translate {d : ℕ} (ν : Measure (Vec d))
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {P : FieldPair d → Prop} (hP : ∀ᵐ ω ∂Q, P ω) :
    ∀ᵐ z : Vec d × FieldPair d ∂ν.prod Q, P (translate z.1 z.2) := by
  exact (QuasiMeasurePreserving.prod_of_right
    Probability.continuous_translate.measurable
    (Filter.Eventually.of_forall fun y =>
      (measurePreserving_translate Q hQ y).quasiMeasurePreserving)).ae hP

/-- Product integrability of a local field survives translating its
center-zero environmental version. Source: `paper/main.tex:913–938`. -/
theorem integrable_centerTranslate {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure (Vec d)) [SFinite ν]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    {F : Vec d × FieldPair d → E} (hF : Integrable F (ν.prod Q)) :
    Integrable (fun z => F (z.1, translate z.1 z.2)) (ν.prod Q) :=
  (measurePreserving_centerTranslate ν Q hQ).integrable_comp_of_integrable hF

/-- Center translation preserves the actual Bochner integral, including
its representative-independent total-integral convention.
Source: `paper/main.tex:913–938`. -/
theorem integral_centerTranslate {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure (Vec d)) [SFinite ν]
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (F : Vec d × FieldPair d → E) :
    (∫ z, F (z.1, translate z.1 z.2) ∂ν.prod Q) = ∫ z, F z ∂ν.prod Q :=
  (measurePreserving_centerTranslate ν Q hQ).integral_comp
    centerTranslateEquiv.measurableEmbedding F

end EinsteinRelation.Correctors
