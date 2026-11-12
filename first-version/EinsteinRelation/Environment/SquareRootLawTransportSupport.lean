import EinsteinRelation.Environment.RegularSquareRootFieldSupport
import EinsteinRelation.Environment.AKMTestIntegralSupport
import EinsteinRelation.Environment.SquareRootFieldMapSupport
import EinsteinRelation.Environment.TranslationErgodicitySupport

open MeasureTheory
open scoped MatrixOrder

namespace EinsteinRelation

/-- The observation sigma algebra of a field-valued map on an arbitrary source space. -/
def observedSigma {α : Type*} [MeasurableSpace α] {d : ℕ}
    (observe : α → FieldPair d) (U : Set (Vec d)) : MeasurableSpace α :=
  (localSigma U).comap observe

/-- Translation invariance for a law on a carrier with its own translation action. -/
def IsStationaryUnder {α : Type*} [MeasurableSpace α] {d : ℕ}
    (shift : Vec d → α → α) (μ : Measure α) : Prop :=
  ∀ z, Measure.map (shift z) μ = μ

/-- The zero-one event formulation of ergodicity for a translation action. -/
def IsErgodicUnder {α : Type*} [MeasurableSpace α] {d : ℕ}
    (shift : Vec d → α → α) (μ : Measure α) : Prop :=
  ∀ A, MeasurableSet A →
    (∀ z, ∀ᵐ x ∂μ, (shift z x ∈ A ↔ x ∈ A)) → μ A = 0 ∨ μ A = 1

/-- Joint finite range for observations of a law on an arbitrary source carrier. -/
def HasFiniteRangeUnder {α : Type*} [MeasurableSpace α] {d : ℕ}
    (r₀ : ℝ) (observe : α → FieldPair d) (μ : Measure α) : Prop :=
  ∀ U W : Set (Vec d), MeasurableSet U → MeasurableSet W →
    (∃ s : ℝ, r₀ < s ∧ ∀ x ∈ U, ∀ y ∈ W,
      s ≤ euclideanNorm (x - y)) →
    ProbabilityTheory.Indep (observedSigma observe U) (observedSigma observe W) μ

/-- An equivariant measurable image of a stationary law remains stationary. -/
theorem isStationary_map_of_equivariant {α : Type*} [MeasurableSpace α] {d : ℕ}
    (shift : Vec d → α → α) (μ : Measure α) (T : α → FieldPair d)
    (hT : Measurable T) (hshift : ∀ z, Measurable (shift z))
    (hsource : IsStationaryUnder shift μ)
    (hequiv : ∀ z x, T (shift z x) = translate z (T x)) :
    IsStationary (μ.map T) := by
  intro z
  rw [Measure.map_map (Probability.measurable_translate z) hT]
  have hcomp : translate z ∘ T = T ∘ shift z := funext fun x => (hequiv z x).symm
  rw [hcomp, ← Measure.map_map hT (hshift z), hsource z]

/-- A measurable equivariant factor of an ergodic law is ergodic. -/
theorem isErgodic_map_of_equivariant {α : Type*} [MeasurableSpace α] {d : ℕ}
    (shift : Vec d → α → α) (μ : Measure α) (T : α → FieldPair d)
    (hT : Measurable T) (hsource : IsErgodicUnder shift μ)
    (hequiv : ∀ z x, T (shift z x) = translate z (T x)) :
    IsErgodicUnder translate (μ.map T) := by
  intro A hA hInv
  let B : Set α := T ⁻¹' A
  have hB : MeasurableSet B := hA.preimage hT
  have hBinv : ∀ z, ∀ᵐ x ∂μ, (shift z x ∈ B ↔ x ∈ B) := by
    intro z
    have hInv' : ∀ᵐ x ∂μ, (translate z (T x) ∈ A ↔ T x ∈ A) :=
      ae_of_ae_map hT.aemeasurable (hInv z)
    filter_upwards [hInv'] with x hx
    simpa only [B, Set.mem_preimage, hequiv z x] using hx
  have hmass : (μ.map T) A = μ B := by
    rw [Measure.map_apply hT hA]
  rcases hsource B hB hBinv with hzero | hone
  · rw [hmass]
    exact Or.inl hzero
  · rw [hmass]
    exact Or.inr hone

/-- Local observables of an equivariant image preserve joint finite range. -/
theorem hasFiniteRange_map_of_local {α : Type*} [MeasurableSpace α] {d : ℕ}
    (r₀ : ℝ) (observe : α → FieldPair d) (μ : Measure α) (T : α → FieldPair d)
    (hT : Measurable T)
    (hsource : HasFiniteRangeUnder r₀ observe μ)
    (hlocal : ∀ U, (localSigma U).comap T ≤ observedSigma observe U) :
    HasFiniteRange r₀ (μ.map T) := by
  intro U W hU hW hgap
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hsB : MeasurableSet s := Probability.localSigma_le_borel U s hs
  have htB : MeasurableSet t := Probability.localSigma_le_borel W t ht
  have hTlocalU : @Measurable α (FieldPair d)
      (observedSigma observe U) (localSigma U) T :=
    Measurable.of_comap_le (hlocal U)
  have hTlocalW : @Measurable α (FieldPair d)
      (observedSigma observe W) (localSigma W) T :=
    Measurable.of_comap_le (hlocal W)
  have hsPre : MeasurableSet[observedSigma observe U] (T ⁻¹' s) := hTlocalU hs
  have htPre : MeasurableSet[observedSigma observe W] (T ⁻¹' t) := hTlocalW ht
  have hind := (ProbabilityTheory.Indep_iff _ _ _).1
    (hsource U W hU hW hgap) (T ⁻¹' s) (T ⁻¹' t) hsPre htPre
  rw [Measure.map_apply hT (hsB.inter htB),
    Measure.map_apply hT hsB, Measure.map_apply hT htB, Set.preimage_inter]
  exact hind

local instance matrixSeminormedAddCommGroup (d : ℕ) : SeminormedAddCommGroup (Mat d) :=
  Matrix.seminormedAddCommGroup

private abbrev EllipticMatrix (d : ℕ) (Λ : ℝ) :=
  {A : Mat d // IsElliptic Λ (fun _ : Vec d => A)}

private noncomputable def ellipticMatrixSquareRoot {d : ℕ} {Λ : ℝ}
    (A : EllipticMatrix d Λ) : Mat d := CFC.sqrt A.1

private theorem continuous_ellipticMatrixSquareRoot {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) :
    Continuous (ellipticMatrixSquareRoot (d := d) (Λ := Λ)) := by
  apply (LipschitzWith.of_dist_le' (K := Real.sqrt (Λ / 4) * (d : ℝ)) (by
    intro A B
    rw [dist_eq_norm]
    simpa [ellipticMatrixSquareRoot, dist_eq_norm] using
      cfcSqrt_matrix_norm_lipschitz_of_ellipticity hΛ A.1 B.1 A.2 B.2)).continuous

private theorem measurable_regularSquareRootObservation {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (U : Set (Vec d)) {x : Vec d} (hx : x ∈ U) :
    @Measurable (ReductionImageV3.PhysicalField d Λ) (Mat d × ℝ)
      (observedSigma (Subtype.val : ReductionImageV3.PhysicalField d Λ → FieldPair d) U)
      inferInstance
      (fun ω => ((regularSquareRootFieldMap hΛ ω).1 x,
        (regularSquareRootFieldMap hΛ ω).2 x)) := by
  letI : MeasurableSpace (EllipticMatrix d Λ) := MeasurableSpace.comap Subtype.val inferInstance
  letI : MeasurableSpace (EllipticMatrix d Λ × ℝ) := inferInstance
  let σ := observedSigma (Subtype.val : ReductionImageV3.PhysicalField d Λ → FieldPair d) U
  have hEval : @Measurable (FieldPair d) (Mat d × ℝ) (localSigma U) inferInstance
      (fun ω => (ω.1 x, ω.2 x)) := by
    apply Measurable.of_comap_le
    unfold localSigma
    exact le_iSup_of_le ⟨x, hx⟩ le_rfl
  have hval : @Measurable (ReductionImageV3.PhysicalField d Λ) (FieldPair d) σ
      (localSigma U) Subtype.val := by
    exact Measurable.of_comap_le le_rfl
  have hEval' : @Measurable (ReductionImageV3.PhysicalField d Λ) (Mat d × ℝ) σ inferInstance
      (fun ω => (ω.1.1 x, ω.1.2 x)) := by
    exact hEval.comp hval
  let coeff : ReductionImageV3.PhysicalField d Λ → EllipticMatrix d Λ :=
    fun ω => ⟨ω.1.1 x, fun _ => ω.2.1 x⟩
  let pot : ReductionImageV3.PhysicalField d Λ → ℝ := fun ω => ω.1.2 x
  have hcoeff : @Measurable (ReductionImageV3.PhysicalField d Λ) (EllipticMatrix d Λ)
      σ _ coeff := by
    have hfirst : @Measurable (ReductionImageV3.PhysicalField d Λ) (Mat d) σ inferInstance
        (fun ω => ω.1.1 x) := Measurable.comp measurable_fst hEval'
    exact hfirst.subtype_mk (h := fun ω => fun _ => ω.2.1 x)
  have hpot : @Measurable (ReductionImageV3.PhysicalField d Λ) ℝ σ inferInstance pot := by
    have hsnd : @Measurable (ReductionImageV3.PhysicalField d Λ) ℝ σ inferInstance
        (fun ω => ω.1.2 x) := Measurable.comp measurable_snd hEval'
    exact hsnd
  have hroot : Measurable (ellipticMatrixSquareRoot (d := d) (Λ := Λ)) :=
    (continuous_ellipticMatrixSquareRoot hΛ).measurable
  have hpair : @Measurable (EllipticMatrix d Λ × ℝ) (Mat d × ℝ)
      inferInstance inferInstance (fun p => (ellipticMatrixSquareRoot p.1, p.2)) :=
    hroot.comp measurable_fst |>.prodMk (measurable_snd)
  have hfactor : @Measurable (ReductionImageV3.PhysicalField d Λ) (EllipticMatrix d Λ × ℝ)
      σ inferInstance (fun ω => (coeff ω, pot ω)) := hcoeff.prodMk hpot
  have hobs := hpair.comp hfactor
  have hfactor_eq : (fun ω => ((regularSquareRootFieldMap hΛ ω).1 x,
      (regularSquareRootFieldMap hΛ ω).2 x)) =
      (fun ω => (ellipticMatrixSquareRoot (coeff ω), pot ω)) := by
    funext ω
    simp [coeff, pot, ellipticMatrixSquareRoot, regularSquareRootFieldMap_coefficient_apply,
      regularSquareRootFieldMap_potential_apply]
  rw [hfactor_eq]
  exact hobs

/-- The actual square-root map is local in its literal coefficient and potential observations. -/
theorem regularSquareRootFieldMap_localSigma {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (U : Set (Vec d)) :
    (localSigma U).comap (regularSquareRootFieldMap hΛ) ≤
      observedSigma (Subtype.val : ReductionImageV3.PhysicalField d Λ → FieldPair d) U := by
  rw [show localSigma U = ⨆ x : U,
      MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 x.1, ω.2 x.1)) inferInstance from rfl]
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro x
  rw [MeasurableSpace.comap_comp]
  have hobs := measurable_regularSquareRootObservation hΛ U x.2
  exact hobs.comap_le

/-- Equality of coefficient and potential observations on `U` is preserved by the
actual CFC square-root map on the regular-field carrier. -/
theorem regularSquareRootFieldMap_eq_on_of_eq_on {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω η : ReductionImageV3.PhysicalField d Λ) (U : Set (Vec d))
    (hcoeff : ∀ x ∈ U, ω.1.1 x = η.1.1 x)
    (hpotential : ∀ x ∈ U, ω.1.2 x = η.1.2 x) :
    ∀ x ∈ U, (regularSquareRootFieldMap hΛ ω).1 x =
        (regularSquareRootFieldMap hΛ η).1 x ∧
      (regularSquareRootFieldMap hΛ ω).2 x = (regularSquareRootFieldMap hΛ η).2 x := by
  intro x hx
  exact ⟨regularCoefficientSquareRoot_locality ω η U hcoeff x hx, hpotential x hx⟩

private theorem physicalReferenceLaw_ergodic {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (hd : 2 ≤ d) :
    IsErgodicUnder
      (Environment.AKMTestIntegralSupport.physicalTranslate (d := d) (L := Λ))
      (ReductionImageV3.physicalReferenceLaw Q) := by
  let val : ReductionImageV3.PhysicalField d Λ → FieldPair d := Subtype.val
  let embedding : MeasurableEmbedding val := MeasurableEmbedding.subtype_coe
    (Sharpness.measurableSet_isRegular_fieldPair (d := d) Λ)
  intro A hA hInv
  let B : Set (FieldPair d) := val '' A
  have hB : MeasurableSet B := embedding.measurableSet_image.mpr hA
  have hpre : val ⁻¹' B = A := by
    ext ω
    constructor
    · rintro ⟨η, hη, hηω⟩
      have hEq : η = ω := Subtype.ext hηω
      simpa [hEq] using hη
    · intro hω
      exact ⟨ω, hω, rfl⟩
  have hBiff (ω : ReductionImageV3.PhysicalField d Λ) :
      (ω.1 ∈ B ↔ ω ∈ A) := by
    change ω ∈ val ⁻¹' B ↔ ω ∈ A
    rw [hpre]
  have hsourceInv : ∀ z, ∀ᵐ ω ∂(ReductionImageV3.physicalReferenceLaw Q),
      (translate z ω.1 ∈ B ↔ ω.1 ∈ B) := by
    intro z
    filter_upwards [hInv z] with ω hω
    have hleft := hBiff (Environment.AKMTestIntegralSupport.physicalTranslate z ω)
    have hright := hBiff ω
    simpa [Environment.AKMTestIntegralSupport.physicalTranslate] using
      hleft.trans (hω.trans hright.symm)
  have htargetInv : ∀ z, ∀ᵐ ω ∂Q.measure,
      (translate z ω ∈ B ↔ ω ∈ B) := by
    intro z
    have hset : MeasurableSet {ω : FieldPair d | translate z ω ∈ B ↔ ω ∈ B} :=
      (hB.preimage (Probability.measurable_translate z)).iff hB
    rw [← ReductionImageV3.physicalReferenceLaw_forget Q]
    exact (ae_map_iff embedding.measurable.aemeasurable hset).2 (hsourceInv z)
  have hambient := Localization.environmentLaw_translation_ergodic Q hd B hB htargetInv
  have hmass : (ReductionImageV3.physicalReferenceLaw Q) A = Q.measure B := by
    rw [← ReductionImageV3.physicalReferenceLaw_forget Q,
      Measure.map_apply embedding.measurable hB, hpre]
  rcases hambient with hzero | hone
  · left
    rw [hmass]
    exact hzero
  · right
    rw [hmass]
    exact hone

/-- The source subtype measure is the restriction of the actual environment law to
its almost-everywhere regularity event. -/
theorem physicalReferenceLaw_hasFiniteRangeUnder {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) :
    HasFiniteRangeUnder r₀
      (Subtype.val : ReductionImageV3.PhysicalField d Λ → FieldPair d)
      (ReductionImageV3.physicalReferenceLaw Q) := by
  intro U W hU hW hgap
  exact Environment.AKMTestIntegralSupport.physicalReferenceLaw_indep_local Q U W hU hW hgap

/-- The law of the square-root field map on the actual regular subtype. -/
noncomputable def actualSquareRootLaw {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) : Measure (FieldPair d) :=
  (ReductionImageV3.physicalReferenceLaw Q).map
    (regularSquareRootFieldMap Q.ellipticity_parameter)

/-- The actual square-root map commutes with physical translations. -/
theorem regularSquareRootFieldMap_physicalTranslate {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (z : Vec d) (ω : ReductionImageV3.PhysicalField d Λ) :
    regularSquareRootFieldMap hΛ
        (Environment.AKMTestIntegralSupport.physicalTranslate z ω) =
      translate z (regularSquareRootFieldMap hΛ ω) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro x
    simp [Environment.AKMTestIntegralSupport.physicalTranslate,
      regularSquareRootFieldMap_coefficient_apply, translate_matrix]
  · apply ContinuousMap.ext
    intro x
    simp [Environment.AKMTestIntegralSupport.physicalTranslate,
      regularSquareRootFieldMap_potential_apply, translate_scalar]

/-- The square-root image of the actual law is stationary. -/
theorem actualSquareRootLaw_stationary {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) : IsStationary (actualSquareRootLaw Q) := by
  apply isStationary_map_of_equivariant
    (Environment.AKMTestIntegralSupport.physicalTranslate (d := d) (L := Λ))
    (ReductionImageV3.physicalReferenceLaw Q)
    (regularSquareRootFieldMap Q.ellipticity_parameter)
    (measurable_regularSquareRootFieldMap Q.ellipticity_parameter)
    (Environment.AKMTestIntegralSupport.measurable_physicalTranslate (d := d) (L := Λ))
    (fun z => Environment.AKMTestIntegralSupport.physicalReferenceLaw_translation_invariant Q z)
  intro z ω
  exact regularSquareRootFieldMap_physicalTranslate Q.ellipticity_parameter z ω

/-- The actual square-root image inherits translation ergodicity on the same
regular-subtype carrier used to define its law. -/
theorem actualSquareRootLaw_ergodic {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (hd : 2 ≤ d) :
    IsErgodicUnder translate (actualSquareRootLaw Q) := by
  apply isErgodic_map_of_equivariant
    (Environment.AKMTestIntegralSupport.physicalTranslate (d := d) (L := Λ))
    (ReductionImageV3.physicalReferenceLaw Q)
    (regularSquareRootFieldMap Q.ellipticity_parameter)
    (measurable_regularSquareRootFieldMap Q.ellipticity_parameter)
    (physicalReferenceLaw_ergodic Q hd)
  intro z ω
  exact regularSquareRootFieldMap_physicalTranslate Q.ellipticity_parameter z ω

/-- Joint finite range of the square-root image follows from the actual joint
finite-range law and observation locality. This is not a regularity claim about
the image fields. -/
theorem actualSquareRootLaw_finiteRange {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) : HasFiniteRange r₀ (actualSquareRootLaw Q) := by
  apply hasFiniteRange_map_of_local r₀
    (Subtype.val : ReductionImageV3.PhysicalField d Λ → FieldPair d)
    (ReductionImageV3.physicalReferenceLaw Q)
    (regularSquareRootFieldMap Q.ellipticity_parameter)
    (measurable_regularSquareRootFieldMap Q.ellipticity_parameter)
    (physicalReferenceLaw_hasFiniteRangeUnder Q)
  exact regularSquareRootFieldMap_localSigma Q.ellipticity_parameter

/-- The actual square-root image remains a probability law. -/
theorem actualSquareRootLaw_probability {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) : IsProbabilityMeasure (actualSquareRootLaw Q) := by
  letI : IsProbabilityMeasure (ReductionImageV3.physicalReferenceLaw Q) :=
    ReductionImageV3.physicalReferenceLaw_probability Q
  exact Measure.isProbabilityMeasure_map
    (measurable_regularSquareRootFieldMap Q.ellipticity_parameter).aemeasurable

end EinsteinRelation
