import EinsteinRelation.Environment.Reduction

/-! # Conditioning on the reduced coefficient alone

The physical environment carries `(a₀,V)`. Corrector conditioning observes
`a = exp(-2V) a₀`, while the occupation estimates use the joint environment.
These are different restriction σ-algebras on the same probability space.
-/

namespace EinsteinRelation

/-- Canonical continuous matrix fields, with the compact-open Borel structure. -/
abbrev CoefficientField (d : ℕ) := C(Vec d, Mat d)

instance (d : ℕ) : MeasurableSpace (CoefficientField d) := borel (CoefficientField d)
instance (d : ℕ) : BorelSpace (CoefficientField d) := ⟨rfl⟩

/-- The actual reduced matrix field of a physical environment. -/
noncomputable def reducedMatrixField {d : ℕ} (ω : FieldPair d) : CoefficientField d :=
  (reduce ω).1

@[simp] theorem reducedMatrixField_apply {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    reducedMatrixField ω x = reducedCoefficient ω x := rfl

/-- Restriction of the reduced coefficient to the observed set. -/
noncomputable def coefficientRestriction {d : ℕ} (U : Set (Vec d)) (ω : FieldPair d) :
    C(U, Mat d) :=
  ⟨fun x => reducedCoefficient ω x,
    (reducedMatrixField ω).continuous.comp continuous_subtype_val⟩

@[simp] theorem coefficientRestriction_apply {d : ℕ} (U : Set (Vec d))
    (ω : FieldPair d) (x : U) : coefficientRestriction U ω x = reducedCoefficient ω x := rfl

/-- The coefficient-only σ-algebra `F(U)` in the conditional corrector argument. -/
noncomputable def coefficientSigma {d : ℕ} (U : Set (Vec d)) : MeasurableSpace (FieldPair d) :=
  ⨆ x : U, MeasurableSpace.comap
    (fun ω : FieldPair d => reducedCoefficient ω x) inferInstance

theorem coefficientSigma_mono {d : ℕ} {U W : Set (Vec d)} (hUW : U ⊆ W) :
    coefficientSigma U ≤ coefficientSigma W := by
  unfold coefficientSigma
  apply iSup_le
  intro x
  exact le_iSup_of_le ⟨x.1, hUW x.2⟩ le_rfl

/-- Observing the physical pair locally determines its reduced coefficient. -/
theorem coefficientSigma_le_localSigma {d : ℕ} (U : Set (Vec d)) :
    coefficientSigma U ≤ localSigma U := by
  unfold coefficientSigma localSigma
  apply iSup_mono
  intro x
  let g : Mat d × ℝ → Mat d := fun p => Real.exp (-2 * p.2) • p.1
  have hg : Measurable g :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul
      continuous_fst).measurable
  have hfactor : (fun ω : FieldPair d => reducedCoefficient ω x) =
      g ∘ (fun ω : FieldPair d => (ω.1 x, ω.2 x)) := rfl
  rw [hfactor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

theorem continuous_reducedMatrixField {d : ℕ} :
    Continuous (reducedMatrixField (d := d)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_fst.snd.eval continuous_snd))).smul
      (continuous_fst.fst.eval continuous_snd)

theorem measurable_reducedMatrixField {d : ℕ} :
    Measurable (reducedMatrixField (d := d)) := continuous_reducedMatrixField.measurable

/-- The concrete coefficient law to which the corrector literature applies. -/
noncomputable def coefficientLaw {d : ℕ} (Q : MeasureTheory.Measure (FieldPair d)) :
    MeasureTheory.Measure (CoefficientField d) := Q.map reducedMatrixField

end EinsteinRelation
