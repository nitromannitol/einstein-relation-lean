import EinsteinRelation.Environment.Bounds
import EinsteinRelation.Environment.ReductionEmbedding
import EinsteinRelation.Sharpness.PhysicalRegularityMeasurability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory

noncomputable section

namespace EinsteinRelation.ReductionImageV3

/-- Physical fields satisfying the source regularity bound. -/
abbrev PhysicalField (d : ℕ) (L : ℝ) := {ω : FieldPair d // IsRegular L ω}

/-- The actual image of physical regular fields under the source reduction. -/
def physicalReducedRange {d : ℕ} (L : ℝ) : Set (FieldPair d) :=
  reduce '' {ω : FieldPair d | IsRegular L ω}

/-- Reduced fields are represented only when they come from a physical regular field. -/
abbrev ReducedPhysicalField (d : ℕ) (L : ℝ) :=
  {ρ : FieldPair d // ρ ∈ physicalReducedRange L}

theorem reducedClock_pos {d : ℕ} {L : ℝ} (ρ : ReducedPhysicalField d L)
    (x : Vec d) : 0 < ρ.1.2 x := by
  rcases ρ.2 with ⟨ω, hω, hρ⟩
  have hρx : ρ.1.2 x = (reduce ω).2 x := by rw [hρ]
  rw [hρx]
  exact clockDensity_pos ω x

theorem reducedClock_lower_bound {d : ℕ} {L : ℝ} (ρ : ReducedPhysicalField d L)
    (x : Vec d) : Real.exp (-2 * L) ≤ ρ.1.2 x := by
  rcases ρ.2 with ⟨ω, hω, hρ⟩
  have hρx : ρ.1.2 x = (reduce ω).2 x := by rw [hρ]
  rw [hρx]
  exact (clockDensity_bounds ω x L (hω.2.1 x)).1

/-- The actual reduction map into its physical image. -/
def reducePhysical {d : ℕ} {L : ℝ} (ω : PhysicalField d L) : ReducedPhysicalField d L :=
  ⟨reduce ω.1, ⟨ω.1, ω.2, rfl⟩⟩

/-- Literal inverse formula on the actual image: `a₀ = a/μ`, `V = -(1/2) log μ`. -/
def inversePhysicalFormula {d : ℕ} {L : ℝ} (ρ : ReducedPhysicalField d L) : FieldPair d :=
  (⟨fun x => (ρ.1.2 x)⁻¹ • ρ.1.1 x, by
      have hμ : Continuous (fun x : Vec d => (ρ.1.2 x)⁻¹) := by
        rw [continuous_iff_continuousAt]
        intro x
        exact (continuousAt_inv₀ (ne_of_gt (reducedClock_pos ρ x))).comp
          ρ.1.2.continuous.continuousAt
      exact hμ.smul ρ.1.1.continuous⟩,
   ⟨fun x => -(1 / 2 : ℝ) * Real.log (ρ.1.2 x), by
      have hμ : Continuous (fun x : Vec d => Real.log (ρ.1.2 x)) := by
        rw [continuous_iff_continuousAt]
        intro x
        exact (Real.continuousAt_log (ne_of_gt (reducedClock_pos ρ x))).comp
          ρ.1.2.continuous.continuousAt
      exact continuous_const.mul hμ⟩)

theorem inversePhysicalFormula_reducePhysical {d : ℕ} {L : ℝ}
    (ω : PhysicalField d L) : inversePhysicalFormula (reducePhysical ω) = ω.1 := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro x
    change (clockDensity ω.1 x)⁻¹ • (clockDensity ω.1 x • ω.1.1 x) = ω.1.1 x
    exact inv_smul_smul₀ (clockDensity_pos ω.1 x).ne' _
  · apply ContinuousMap.ext
    intro x
    change -(1 / 2 : ℝ) * Real.log (Real.exp (-2 * ω.1.2 x)) = ω.1.2 x
    rw [Real.log_exp]
    ring

/-- The inverse formula lands in the physical subtype, by its exact inverse identity. -/
def inverseReducePhysical {d : ℕ} {L : ℝ} (ρ : ReducedPhysicalField d L) : PhysicalField d L :=
  ⟨inversePhysicalFormula ρ, by
    rcases ρ.2 with ⟨ω, hω, hρ⟩
    have hsub : (⟨reduce ω, ⟨ω, hω, rfl⟩⟩ : ReducedPhysicalField d L) = ρ :=
      Subtype.ext hρ
    have hInv : inversePhysicalFormula ρ = ω := by
      rw [← hsub]
      change inversePhysicalFormula (reducePhysical ⟨ω, hω⟩) = ω
      exact inversePhysicalFormula_reducePhysical ⟨ω, hω⟩
    rw [hInv]
    exact hω⟩

theorem inverseReduce_reducePhysical {d : ℕ} {L : ℝ} (ω : PhysicalField d L) :
    inverseReducePhysical (reducePhysical ω) = ω := by
  apply Subtype.ext
  exact inversePhysicalFormula_reducePhysical ω

theorem reducePhysical_inverseReduce {d : ℕ} {L : ℝ}
    (ρ : ReducedPhysicalField d L) : reducePhysical (inverseReducePhysical ρ) = ρ := by
  apply Subtype.ext
  rcases ρ.2 with ⟨ω, hω, hρ⟩
  have hsub : (⟨reduce ω, ⟨ω, hω, rfl⟩⟩ : ReducedPhysicalField d L) = ρ :=
    Subtype.ext hρ
  have hInv : inversePhysicalFormula ρ = ω := by
    rw [← hsub]
    change inversePhysicalFormula (reducePhysical ⟨ω, hω⟩) = ω
    exact inversePhysicalFormula_reducePhysical ⟨ω, hω⟩
  change reduce (inversePhysicalFormula ρ) = ρ.1
  rw [hInv, hρ]

/-- The literal inverse formula is continuous in the locally uniform topology on the image. -/
theorem continuous_inversePhysicalFormula {d : ℕ} {L : ℝ} :
    Continuous (inversePhysicalFormula (d := d) (L := L)) := by
  have hpair : Continuous (fun p : ReducedPhysicalField d L × Vec d => (p.1 : FieldPair d)) :=
    continuous_subtype_val.comp continuous_fst
  have hμ : Continuous (fun p : ReducedPhysicalField d L × Vec d => p.1.1.2 p.2) :=
    hpair.snd.eval continuous_snd
  have ha : Continuous (fun p : ReducedPhysicalField d L × Vec d => p.1.1.1 p.2) :=
    hpair.fst.eval continuous_snd
  have hpos : ∀ p : ReducedPhysicalField d L × Vec d, 0 < p.1.1.2 p.2 :=
    fun p => reducedClock_pos p.1 p.2
  have hinv : Continuous (fun p : ReducedPhysicalField d L × Vec d => (p.1.1.2 p.2)⁻¹) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (hμ.continuousAt (x := p)).inv₀ (ne_of_gt (hpos p))
  have hlog : Continuous (fun p : ReducedPhysicalField d L × Vec d => Real.log (p.1.1.2 p.2)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (hμ.continuousAt (x := p)).log (ne_of_gt (hpos p))
  have hmat : Continuous (fun ρ : ReducedPhysicalField d L =>
      (⟨fun x => (ρ.1.2 x)⁻¹ • ρ.1.1 x,
        (by
          have hμx : Continuous (fun x : Vec d => (ρ.1.2 x)⁻¹) := by
            rw [continuous_iff_continuousAt]
            intro x
            exact (ρ.1.2.continuous.continuousAt (x := x)).inv₀
              (ne_of_gt (reducedClock_pos ρ x))
          exact hμx.smul ρ.1.1.continuous)⟩ : CoefficientField d)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hinv.smul ha
  have hpot : Continuous (fun ρ : ReducedPhysicalField d L =>
      (⟨fun x => -(1 / 2 : ℝ) * Real.log (ρ.1.2 x),
        (by
          have hμx : Continuous (fun x : Vec d => Real.log (ρ.1.2 x)) := by
            rw [continuous_iff_continuousAt]
            intro x
            exact (ρ.1.2.continuous.continuousAt (x := x)).log
              (ne_of_gt (reducedClock_pos ρ x))
          exact continuous_const.mul hμx)⟩ : C(Vec d, ℝ))) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_const.mul hlog
  exact hmat.prodMk hpot

/-- The map identifies the two carriers with their subspace topologies. -/
def physicalReduceHomeomorph {d : ℕ} {L : ℝ} :
    PhysicalField d L ≃ₜ ReducedPhysicalField d L where
  toFun := reducePhysical
  invFun := inverseReducePhysical
  left_inv := inverseReduce_reducePhysical
  right_inv := reducePhysical_inverseReduce
  continuous_toFun := by
    exact (Probability.continuous_reduce.comp continuous_subtype_val).subtype_mk
      (fun ω => ⟨ω.1, ω.2, rfl⟩)
  continuous_invFun := by
    exact continuous_inversePhysicalFormula.subtype_mk
      (fun ρ => inverseReducePhysical ρ |>.property)

theorem continuous_reducePhysical {d : ℕ} {L : ℝ} :
    Continuous (reducePhysical (d := d) (L := L)) :=
  (Probability.continuous_reduce.comp continuous_subtype_val).subtype_mk
    (fun ω => ⟨ω.1, ω.2, rfl⟩)

theorem fieldPair_standardBorel (d : ℕ) : StandardBorelSpace (FieldPair d) := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  infer_instance

theorem measurableSet_physicalReducedRange {d : ℕ} (L : ℝ) :
    MeasurableSet (physicalReducedRange (d := d) L) := by
  letI : StandardBorelSpace (FieldPair d) := fieldPair_standardBorel d
  exact ((Probability.measurableEmbedding_reduce d).measurableSet_image).mpr
    (Sharpness.measurableSet_isRegular_fieldPair (d := d) L)

instance reducedPhysicalFieldStandardBorel {d : ℕ} (L : ℝ) :
    StandardBorelSpace (ReducedPhysicalField d L) := by
  letI : StandardBorelSpace (FieldPair d) := fieldPair_standardBorel d
  exact (measurableSet_physicalReducedRange L).standardBorel

instance reducedPhysicalFieldBorelSpace {d : ℕ} (L : ℝ) :
    BorelSpace (ReducedPhysicalField d L) := by
  let h : MeasurableEmbedding (Subtype.val : ReducedPhysicalField d L → FieldPair d) :=
    MeasurableEmbedding.subtype_coe (measurableSet_physicalReducedRange (d := d) L)
  exact h.borelSpace Topology.IsInducing.subtypeVal

instance physicalFieldBorelSpace {d : ℕ} (L : ℝ) :
    BorelSpace (PhysicalField d L) := by
  let h : MeasurableEmbedding (Subtype.val : PhysicalField d L → FieldPair d) :=
    MeasurableEmbedding.subtype_coe
      (Sharpness.measurableSet_isRegular_fieldPair (d := d) L)
  exact h.borelSpace Topology.IsInducing.subtypeVal

instance physicalFieldStandardBorel {d : ℕ} (L : ℝ) :
    StandardBorelSpace (PhysicalField d L) := by
  letI : StandardBorelSpace (FieldPair d) := fieldPair_standardBorel d
  exact (Sharpness.measurableSet_isRegular_fieldPair (d := d) L).standardBorel

theorem measurableEmbedding_reducePhysical {d : ℕ} {L : ℝ} :
    MeasurableEmbedding (reducePhysical (d := d) (L := L)) :=
  (physicalReduceHomeomorph (d := d) (L := L)).toMeasurableEquiv.measurableEmbedding

theorem injective_reducePhysical {d : ℕ} {L : ℝ} :
    Function.Injective (reducePhysical (d := d) (L := L)) :=
  (physicalReduceHomeomorph (d := d) (L := L)).injective

noncomputable def physicalReferenceLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) : Measure (PhysicalField d L) :=
  Q.measure.comap (Subtype.val : PhysicalField d L → FieldPair d)

theorem physicalReferenceLaw_probability {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) : IsProbabilityMeasure (physicalReferenceLaw Q) := by
  let hEmb : MeasurableEmbedding (Subtype.val : PhysicalField d L → FieldPair d) :=
    MeasurableEmbedding.subtype_coe
      (Sharpness.measurableSet_isRegular_fieldPair (d := d) L)
  have hae : ∀ᵐ ω ∂Q.measure,
      ω ∈ Set.range (Subtype.val : PhysicalField d L → FieldPair d) := by
    filter_upwards [Q.regular] with ω hω
    exact ⟨⟨ω, hω⟩, rfl⟩
  exact hEmb.isProbabilityMeasure_comap hae

theorem physicalReferenceLaw_forget {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    (physicalReferenceLaw Q).map
      (Subtype.val : PhysicalField d L → FieldPair d) = Q.measure := by
  let hEmb : MeasurableEmbedding (Subtype.val : PhysicalField d L → FieldPair d) :=
    MeasurableEmbedding.subtype_coe
      (Sharpness.measurableSet_isRegular_fieldPair (d := d) L)
  rw [physicalReferenceLaw, hEmb.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  filter_upwards [Q.regular] with ω hω
  exact ⟨⟨ω, hω⟩, rfl⟩

noncomputable def actualReducedLaw {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) : Measure (ReducedPhysicalField d L) :=
  (physicalReferenceLaw Q).map reducePhysical

theorem actualReducedLaw_probability {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) : IsProbabilityMeasure (actualReducedLaw Q) := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  unfold actualReducedLaw
  infer_instance

theorem actualReducedLaw_forget {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    (actualReducedLaw Q).map (Subtype.val : ReducedPhysicalField d L → FieldPair d) =
      Q.measure.map reduce := by
  rw [actualReducedLaw, Measure.map_map measurable_subtype_coe
    continuous_reducePhysical.measurable]
  change (physicalReferenceLaw Q).map
    (reduce ∘ (Subtype.val : PhysicalField d L → FieldPair d)) = _
  rw [← Measure.map_map Probability.measurable_reduce measurable_subtype_coe,
    physicalReferenceLaw_forget]

theorem ae_map_reduce_mem_physicalImage {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ρ ∂Q.measure.map reduce, ρ ∈ physicalReducedRange L := by
  apply (MeasureTheory.ae_map_iff Probability.measurable_reduce.aemeasurable
    (measurableSet_physicalReducedRange (d := d) L)).2
  filter_upwards [Q.regular] with ω hω
  exact ⟨ω, hω, rfl⟩

end EinsteinRelation.ReductionImageV3

#print axioms EinsteinRelation.ReductionImageV3.physicalReduceHomeomorph
#print axioms EinsteinRelation.ReductionImageV3.measurableSet_physicalReducedRange
#print axioms EinsteinRelation.ReductionImageV3.reducedClock_lower_bound
#print axioms EinsteinRelation.ReductionImageV3.inversePhysicalFormula_reducePhysical
#print axioms EinsteinRelation.ReductionImageV3.inverseReduce_reducePhysical
#print axioms EinsteinRelation.ReductionImageV3.reducePhysical_inverseReduce
#print axioms EinsteinRelation.ReductionImageV3.measurableEmbedding_reducePhysical
#print axioms EinsteinRelation.ReductionImageV3.injective_reducePhysical
#print axioms EinsteinRelation.ReductionImageV3.actualReducedLaw_probability
#print axioms EinsteinRelation.ReductionImageV3.actualReducedLaw_forget
#print axioms EinsteinRelation.ReductionImageV3.ae_map_reduce_mem_physicalImage
