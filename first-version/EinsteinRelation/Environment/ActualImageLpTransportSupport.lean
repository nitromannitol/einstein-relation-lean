import EinsteinRelation.Environment.ReductionImageSupport
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Reduced environment laws on the actual image

The reduced coefficient pair is the image of the physical environment under `reduce`. The
definitions here retain that image as a subtype and compare its law with the ambient pushforward
law used by the stationary corrector space.
-/

open MeasureTheory

namespace EinsteinRelation.ActualImageLpStateTransport

noncomputable section

private theorem translated_difference {d : ℕ} (z x y : Vec d) :
    (z + x) - (z + y) = x - y := by
  ext i
  dsimp
  ring

theorem isRegular_translate_iff {d : ℕ} {L : ℝ} (z : Vec d) (ω : FieldPair d) :
    IsRegular L (translate z ω) ↔ IsRegular L ω := by
  constructor
  · intro h
    rcases h with ⟨hEll, hBound, hMatrixLip, hPotentialLip⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      simpa [IsElliptic, translate, add_sub_cancel_left] using hEll (y - z)
    · intro y
      simpa [translate, add_sub_cancel_left] using hBound (y - z)
    · intro x y ξ
      simpa [IsOperatorLipschitz, translate, add_sub_cancel_left,
        translated_difference] using hMatrixLip (x - z) (y - z) ξ
    · intro x y
      simpa [translate, add_sub_cancel_left, translated_difference] using
        hPotentialLip (x - z) (y - z)
  · intro h
    rcases h with ⟨hEll, hBound, hMatrixLip, hPotentialLip⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y
      simpa [IsElliptic, translate] using hEll (z + y)
    · intro y
      simpa [translate] using hBound (z + y)
    · intro x y ξ
      simpa [IsOperatorLipschitz, translate, translated_difference] using
        hMatrixLip (z + x) (z + y) ξ
    · intro x y
      simpa [translate, translated_difference] using hPotentialLip (z + x) (z + y)

theorem translate_mem_physicalReducedRange {d : ℕ} {L : ℝ} (z : Vec d)
    {ρ : FieldPair d} (hρ : ρ ∈ ReductionImageV3.physicalReducedRange L) :
    translate z ρ ∈ ReductionImageV3.physicalReducedRange L := by
  rcases hρ with ⟨ω, hω, rfl⟩
  refine ⟨translate z ω, (isRegular_translate_iff z ω).2 hω, ?_⟩
  exact (reduce_translate ω z).symm

def reducedTranslate {d : ℕ} {L : ℝ} (z : Vec d) (ρ : ReductionImageV3.ReducedPhysicalField d L) : ReductionImageV3.ReducedPhysicalField d L :=
  ⟨translate z ρ.1, translate_mem_physicalReducedRange z ρ.2⟩

@[simp]
theorem reducedTranslate_val {d : ℕ} {L : ℝ} (z : Vec d) (ρ : ReductionImageV3.ReducedPhysicalField d L) :
    (reducedTranslate z ρ).1 = translate z ρ.1 := rfl

def reducedTranslationMeasurableEquiv {d : ℕ} {L : ℝ} (z : Vec d) :
    ReductionImageV3.ReducedPhysicalField d L ≃ᵐ ReductionImageV3.ReducedPhysicalField d L where
  toEquiv :=
    { toFun := reducedTranslate z
      invFun := reducedTranslate (-z)
      left_inv := by
        intro ρ
        apply Subtype.ext
        change translate (-z) (translate z ρ.1) = ρ.1
        rw [translate_add, neg_add_cancel, translate_zero]
      right_inv := by
        intro ρ
        apply Subtype.ext
        change translate z (translate (-z) ρ.1) = ρ.1
        rw [translate_add, add_neg_cancel, translate_zero] }
  measurable_toFun := ((Probability.measurable_translate z).comp measurable_subtype_coe).subtype_mk
    (h := fun ρ : ReductionImageV3.ReducedPhysicalField d L => translate_mem_physicalReducedRange z ρ.2)
  measurable_invFun := ((Probability.measurable_translate (-z)).comp measurable_subtype_coe).subtype_mk
    (h := fun ρ : ReductionImageV3.ReducedPhysicalField d L => translate_mem_physicalReducedRange (-z) ρ.2)

theorem reduce_equivariant_translate {d : ℕ} (ω : FieldPair d) (z : Vec d) :
    reduce (translate z ω) = translate z (reduce ω) := reduce_translate ω z

theorem ae_reducedEnvironmentLaw_mem_image {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂Correctors.reducedEnvironmentLaw Q,
      ω ∈ ReductionImageV3.physicalReducedRange L := by
  rw [Correctors.reducedEnvironmentLaw]
  exact ReductionImageV3.ae_map_reduce_mem_physicalImage Q

theorem actualReducedLaw_measurePreserving {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
      (ReductionImageV3.actualReducedLaw Q) (Correctors.reducedEnvironmentLaw Q) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  rw [ReductionImageV3.actualReducedLaw_forget, Correctors.reducedEnvironmentLaw]

theorem actualReducedLaw_map_physicalReduceHomeomorph {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    Measure.map (ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L))
      (ReductionImageV3.physicalReferenceLaw Q) = ReductionImageV3.actualReducedLaw Q := rfl

theorem physicalReduceHomeomorph_measurePreserving {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving (ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L))
      (ReductionImageV3.physicalReferenceLaw Q) (ReductionImageV3.actualReducedLaw Q) := by
  refine ⟨(ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L)).measurable, ?_⟩
  exact actualReducedLaw_map_physicalReduceHomeomorph Q

theorem inversePhysicalReduceHomeomorph_measurePreserving {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving
      (ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L)).symm
      (ReductionImageV3.actualReducedLaw Q) (ReductionImageV3.physicalReferenceLaw Q) := by
  let e := ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L)
  have hfwd := physicalReduceHomeomorph_measurePreserving Q
  refine ⟨e.symm.measurable, ?_⟩
  calc
    Measure.map e.symm (ReductionImageV3.actualReducedLaw Q) =
        Measure.map e.symm (Measure.map e (ReductionImageV3.physicalReferenceLaw Q)) := by
          rw [← hfwd.map_eq]
    _ = Measure.map (e.symm ∘ e) (ReductionImageV3.physicalReferenceLaw Q) := by
          rw [Measure.map_map e.symm.measurable e.measurable]
    _ = Measure.map id (ReductionImageV3.physicalReferenceLaw Q) := by
          apply Measure.map_congr
          filter_upwards [] with ω
          exact e.left_inv ω
    _ = ReductionImageV3.physicalReferenceLaw Q := Measure.map_id

theorem actualPhysicalLpIsometry_surjective {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Function.Surjective
      (Lp.compMeasurePreserving
        (ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L))
        (physicalReduceHomeomorph_measurePreserving Q) :
        Lp E 2 (ReductionImageV3.actualReducedLaw Q) →
          Lp E 2 (ReductionImageV3.physicalReferenceLaw Q)) := by
  let e := ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L)
  let hfwd := physicalReduceHomeomorph_measurePreserving Q
  let hinv := inversePhysicalReduceHomeomorph_measurePreserving Q
  intro F
  refine ⟨Lp.compMeasurePreserving e.symm hinv F, ?_⟩
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving e.symm hinv F) hfwd
  have hcompInv := Lp.coeFn_compMeasurePreserving F hinv
  have hcompInv' := hfwd.quasiMeasurePreserving.ae hcompInv
  filter_upwards [hcomp, hcompInv'] with ω hcomp hcompInv
  calc
    Lp.compMeasurePreserving e hfwd (Lp.compMeasurePreserving e.symm hinv F) ω =
        Lp.compMeasurePreserving e.symm hinv F (e ω) := hcomp
    _ = F (e.symm (e ω)) := hcompInv
    _ = F ω := congrArg F (e.left_inv ω)

noncomputable def actualPhysicalLpIsometryEquiv {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 (ReductionImageV3.actualReducedLaw Q) ≃ₗᵢ[ℝ]
      Lp E 2 (ReductionImageV3.physicalReferenceLaw Q) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℝ
      (ReductionImageV3.physicalReduceHomeomorph (d := d) (L := L))
      (physicalReduceHomeomorph_measurePreserving Q))
    (actualPhysicalLpIsometry_surjective Q E)

noncomputable def actualPhysicalScalarL2Equiv {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    Lp ℝ 2 (ReductionImageV3.actualReducedLaw Q) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (ReductionImageV3.physicalReferenceLaw Q) :=
  actualPhysicalLpIsometryEquiv Q ℝ

noncomputable def actualPhysicalVectorL2Equiv {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (ReductionImageV3.actualReducedLaw Q) ≃ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (ReductionImageV3.physicalReferenceLaw Q) :=
  actualPhysicalLpIsometryEquiv Q (EuclideanSpace ℝ (Fin d))

theorem actualImageMeasurableEmbedding {d : ℕ} {L : ℝ} :
    MeasurableEmbedding (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d) :=
  MeasurableEmbedding.subtype_coe
    (ReductionImageV3.measurableSet_physicalReducedRange (d := d) L)

private theorem map_injective_of_measurableEmbedding {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) :
    Function.Injective (fun μ : Measure α => Measure.map f μ) := by
  intro μ ν h
  apply Measure.ext
  intro s hs
  calc
    μ s = μ (f ⁻¹' (f '' s)) := by rw [hf.injective.preimage_image]
    _ = Measure.map f μ (f '' s) := by rw [hf.map_apply]
    _ = Measure.map f ν (f '' s) := by
      exact congrArg (fun m : Measure β => m (f '' s)) h
    _ = ν (f ⁻¹' (f '' s)) := by rw [hf.map_apply]
    _ = ν s := by rw [hf.injective.preimage_image]

theorem actualReducedLaw_translation_invariant {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (z : Vec d) :
    Measure.map (reducedTranslate z) (ReductionImageV3.actualReducedLaw Q) =
      ReductionImageV3.actualReducedLaw Q := by
  apply map_injective_of_measurableEmbedding actualImageMeasurableEmbedding
  calc
    Measure.map (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
        (Measure.map (reducedTranslate z) (ReductionImageV3.actualReducedLaw Q)) =
      Measure.map (translate z)
        ((ReductionImageV3.actualReducedLaw Q).map
          (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)) := by
        change Measure.map (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
          (Measure.map (reducedTranslationMeasurableEquiv z)
            (ReductionImageV3.actualReducedLaw Q)) = _
        rw [Measure.map_map measurable_subtype_coe
          (reducedTranslationMeasurableEquiv z).measurable]
        rw [Measure.map_map (Probability.measurable_translate z) measurable_subtype_coe]
        congr 1
    _ = (ReductionImageV3.actualReducedLaw Q).map
        (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d) := by
        rw [(actualReducedLaw_measurePreserving Q).map_eq,
          (Correctors.reducedEnvironmentLaw_stationary Q) z,
          ← (actualReducedLaw_measurePreserving Q).map_eq]

theorem actualReducedLaw_reducedTranslation_measurePreserving {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (z : Vec d) :
    MeasurePreserving (reducedTranslate z) (ReductionImageV3.actualReducedLaw Q)
      (ReductionImageV3.actualReducedLaw Q) :=
  ⟨(reducedTranslationMeasurableEquiv z).measurable,
    actualReducedLaw_translation_invariant Q z⟩

theorem ae_actualImage_iff_ambient {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (P : FieldPair d → Prop) (hP : MeasurableSet {ω | P ω}) :
    (∀ᵐ ρ ∂ReductionImageV3.actualReducedLaw Q, P ρ.1) ↔
      ∀ᵐ ω ∂Correctors.reducedEnvironmentLaw Q, P ω := by
  rw [← (actualReducedLaw_measurePreserving Q).map_eq]
  exact (MeasureTheory.ae_map_iff
    (actualReducedLaw_measurePreserving Q).aemeasurable hP).symm

def actualImageLpIsometry {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 (Correctors.reducedEnvironmentLaw Q) →ₗᵢ[ℝ]
      Lp E 2 (ReductionImageV3.actualReducedLaw Q) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact Lp.compMeasurePreservingₗᵢ ℝ (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
    (actualReducedLaw_measurePreserving Q)

theorem actualImageLp_coeFn {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Lp E 2 (Correctors.reducedEnvironmentLaw Q)) :
    actualImageLpIsometry Q E F =ᵐ[ReductionImageV3.actualReducedLaw Q]
      fun ρ => F ρ.1 := by
  change Lp.compMeasurePreserving (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
    (actualReducedLaw_measurePreserving Q) F =ᵐ[
      ReductionImageV3.actualReducedLaw Q] fun ρ => F ρ.1
  exact Lp.coeFn_compMeasurePreserving F (actualReducedLaw_measurePreserving Q)

theorem actualImageLp_norm {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Lp E 2 (Correctors.reducedEnvironmentLaw Q)) :
    ‖actualImageLpIsometry Q E F‖ = ‖F‖ := by
  exact Lp.norm_compMeasurePreserving F (actualReducedLaw_measurePreserving Q)

theorem actualImageLpIsometry_commutes_translate {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (z : Vec d)
    (F : Lp E 2 (Correctors.reducedEnvironmentLaw Q)) :
    actualImageLpIsometry Q E
        (Lp.compMeasurePreserving (translate z)
          ⟨Probability.measurable_translate z,
            Correctors.reducedEnvironmentLaw_stationary Q z⟩ F) =
      Lp.compMeasurePreserving (reducedTranslate z)
        (actualReducedLaw_reducedTranslation_measurePreserving Q z)
        (actualImageLpIsometry Q E F) := by
  let μ : Measure (FieldPair d) := Correctors.reducedEnvironmentLaw Q
  let ν : Measure (ReductionImageV3.ReducedPhysicalField d L) :=
    ReductionImageV3.actualReducedLaw Q
  have hμ : MeasurePreserving (translate z) μ μ :=
    ⟨Probability.measurable_translate z, Correctors.reducedEnvironmentLaw_stationary Q z⟩
  have hν : MeasurePreserving (reducedTranslate z) ν ν :=
    actualReducedLaw_reducedTranslation_measurePreserving Q z
  have hforget : MeasurePreserving
      (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
      ν μ := actualReducedLaw_measurePreserving Q
  have hleft := Lp.coeFn_compMeasurePreserving F hμ
  have hright := Lp.coeFn_compMeasurePreserving (actualImageLpIsometry Q E F) hν
  have himage := actualImageLp_coeFn Q E
    (Lp.compMeasurePreserving (translate z) hμ F)
  have hambient := actualImageLp_coeFn Q E F
  have hleft_on_image := hforget.quasiMeasurePreserving.ae hleft
  have hambient_after_translate := hν.quasiMeasurePreserving.ae hambient
  apply Lp.ext
  filter_upwards [himage, hright, hleft_on_image,
    hambient_after_translate] with ρ himage hright hleft hambient_shift
  calc
    actualImageLpIsometry Q E (Lp.compMeasurePreserving (translate z) hμ F) ρ =
        (Lp.compMeasurePreserving (translate z) hμ F) ρ.1 := himage
    _ = F (translate z ρ.1) := hleft
    _ = F (reducedTranslate z ρ).1 := by rfl
    _ = actualImageLpIsometry Q E F (reducedTranslate z ρ) :=
      hambient_shift.symm
    _ = Lp.compMeasurePreserving (reducedTranslate z) hν
          (actualImageLpIsometry Q E F) ρ := hright.symm

def actualImageScalarLpIsometry {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) :
    Lp ℝ 2 (Correctors.reducedEnvironmentLaw Q) →ₗᵢ[ℝ]
      Lp ℝ 2 (ReductionImageV3.actualReducedLaw Q) :=
  actualImageLpIsometry Q ℝ

def actualImageVectorLpIsometry {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q) →ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (ReductionImageV3.actualReducedLaw Q) :=
  actualImageLpIsometry Q (EuclideanSpace ℝ (Fin d))

def actualImageMatrixLpIsometry {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) :
    Lp (EuclideanSpace ℝ (Fin d × Fin d)) 2 (Correctors.reducedEnvironmentLaw Q) →ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin d × Fin d)) 2 (ReductionImageV3.actualReducedLaw Q) :=
  actualImageLpIsometry Q (EuclideanSpace ℝ (Fin d × Fin d))

def reducedMatrixAtOriginEuclidean {d : ℕ} (ρ : FieldPair d) : EuclideanSpace ℝ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij => ρ.1 0 ij.1 ij.2)

instance actualReducedLaw_isProbabilityMeasure {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    IsProbabilityMeasure (ReductionImageV3.actualReducedLaw Q) :=
  ReductionImageV3.actualReducedLaw_probability Q

noncomputable def actualImageL2Expectation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    Lp ℝ 2 (ReductionImageV3.actualReducedLaw Q) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing (ReductionImageV3.actualReducedLaw Q) 2 2
    (MemLp.toLp (fun _ : ReductionImageV3.ReducedPhysicalField d L => (1 : ℝ))
      (memLp_const (1 : ℝ) :
        MemLp (fun _ : ReductionImageV3.ReducedPhysicalField d L => (1 : ℝ)) 2
          (ReductionImageV3.actualReducedLaw Q)))

theorem actualImageL2Expectation_apply {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (F : Lp ℝ 2 (ReductionImageV3.actualReducedLaw Q)) :
    actualImageL2Expectation Q F =
      ∫ ρ, F ρ ∂ReductionImageV3.actualReducedLaw Q := by
  have hconst : MemLp (fun _ : ReductionImageV3.ReducedPhysicalField d L => (1 : ℝ)) 2
      (ReductionImageV3.actualReducedLaw Q) := memLp_const (1 : ℝ)
  unfold actualImageL2Expectation
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hconst] with ρ hρ
  simp

noncomputable def actualImageEuclideanCoordinateMean {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (ReductionImageV3.actualReducedLaw Q) →L[ℝ] ℝ :=
  (actualImageL2Expectation Q).comp
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2
      (ReductionImageV3.actualReducedLaw Q))

theorem actualImageEuclideanCoordinateMean_comp {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
    (i : Fin d) :
    actualImageEuclideanCoordinateMean Q i (actualImageVectorLpIsometry Q G) =
      Correctors.euclideanCoordinateMean (Correctors.reducedEnvironmentLaw Q) i G := by
  letI : IsProbabilityMeasure (ReductionImageV3.actualReducedLaw Q) :=
    ReductionImageV3.actualReducedLaw_probability Q
  rw [actualImageEuclideanCoordinateMean, Correctors.euclideanCoordinateMean,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    actualImageL2Expectation_apply, EinsteinRelation.l2Expectation_apply]
  let π := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i
  have himage :
      (fun ρ : ReductionImageV3.ReducedPhysicalField d L =>
        ((π.compLpL 2 (ReductionImageV3.actualReducedLaw Q))
          (actualImageVectorLpIsometry Q G)) ρ) =ᵐ[
            ReductionImageV3.actualReducedLaw Q] fun ρ => G ρ.1 i := by
    filter_upwards [
      ContinuousLinearMap.coeFn_compLpL π (actualImageVectorLpIsometry Q G)
        (p := 2) (μ := ReductionImageV3.actualReducedLaw Q),
      actualImageLp_coeFn Q (EuclideanSpace ℝ (Fin d)) G] with ρ hπ hG
    calc
      ((π.compLpL 2 (ReductionImageV3.actualReducedLaw Q))
          (actualImageVectorLpIsometry Q G)) ρ = π (actualImageVectorLpIsometry Q G ρ) := by
            simpa only [ContinuousLinearMap.coeFn_compLpL] using hπ
      _ = G ρ.1 i := by
            change actualImageVectorLpIsometry Q G ρ = G ρ.1 at hG
            rw [hG]
            simp [π, PiLp.proj_apply]
  have hambient :
      (fun ω : FieldPair d =>
        ((π.compLpL 2 (Correctors.reducedEnvironmentLaw Q)) G) ω) =ᵐ[
          Correctors.reducedEnvironmentLaw Q] fun ω => G ω i := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL π G
      (p := 2) (μ := Correctors.reducedEnvironmentLaw Q)] with ω hπ
    simpa [π, PiLp.proj_apply] using hπ
  calc
    ∫ ρ, ((π.compLpL 2 (ReductionImageV3.actualReducedLaw Q))
        (actualImageVectorLpIsometry Q G)) ρ ∂ReductionImageV3.actualReducedLaw Q =
      ∫ ρ, G ρ.1 i ∂ReductionImageV3.actualReducedLaw Q := integral_congr_ae himage
    _ = ∫ ω, G ω i ∂Correctors.reducedEnvironmentLaw Q :=
      (actualReducedLaw_measurePreserving Q).integral_comp
        (MeasurableEmbedding.subtype_coe
          (ReductionImageV3.measurableSet_physicalReducedRange L)) (fun ω => G ω i)
    _ = ∫ ω, ((π.compLpL 2 (Correctors.reducedEnvironmentLaw Q)) G) ω ∂
        Correctors.reducedEnvironmentLaw Q := (integral_congr_ae hambient).symm

theorem actualImage_ambientPotentialDomain_mean_zero {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (Correctors.reducedEnvironmentLaw Q))
    (hG : G ∈ Correctors.correctorPotentialDomain Q) (i : Fin d) :
    actualImageEuclideanCoordinateMean Q i (actualImageVectorLpIsometry Q G) = 0 := by
  rw [actualImageEuclideanCoordinateMean_comp]
  exact Correctors.correctorPotentialDomain_mean_zero Q G hG i

end

end EinsteinRelation.ActualImageLpStateTransport
