import EinsteinRelation.Environment.ActualImageHorizontalH1Support

open MeasureTheory

namespace EinsteinRelation.ActualImageVariationalSupport

noncomputable section

open ActualImageHorizontalH1Transport

abbrev ImageLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :=
  ReductionImageV3.actualReducedLaw Q

abbrev AmbientLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :=
  Correctors.reducedEnvironmentLaw Q

private theorem actualImageLpIsometry_surjective {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Function.Surjective (ActualImageLpStateTransport.actualImageLpIsometry Q E) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  intro F
  let hF := Lp.aestronglyMeasurable F
  let f₀ := hF.mk F
  have hf₀sm : StronglyMeasurable f₀ := hF.stronglyMeasurable_mk
  obtain ⟨g, hgsm, hgcomp⟩ :=
    ActualImageLpStateTransport.actualImageMeasurableEmbedding.exists_stronglyMeasurable_extend
      hf₀sm (fun _ : FieldPair d => ⟨(0 : E)⟩)
  have hgmem : MemLp g 2 (Correctors.reducedEnvironmentLaw Q) := by
    rw [show Correctors.reducedEnvironmentLaw Q =
      Measure.map (Subtype.val : ReductionImageV3.ReducedPhysicalField d Λ₀ → FieldPair d)
        (ReductionImageV3.actualReducedLaw Q) by
          exact (ActualImageLpStateTransport.actualReducedLaw_measurePreserving Q).map_eq.symm]
    rw [ActualImageLpStateTransport.actualImageMeasurableEmbedding.memLp_map_measure_iff]
    change MemLp (g ∘ (Subtype.val : ReductionImageV3.ReducedPhysicalField d Λ₀ → FieldPair d))
      2 (ReductionImageV3.actualReducedLaw Q)
    rw [hgcomp]
    exact (memLp_congr_ae hF.ae_eq_mk).mp (Lp.memLp F)
  refine ⟨hgmem.toLp g, ?_⟩
  apply Lp.ext
  have hmap :=
    (ActualImageLpStateTransport.actualReducedLaw_measurePreserving Q).quasiMeasurePreserving.ae
      hgmem.coeFn_toLp
  have hcomp : (fun ρ : ReductionImageV3.ReducedPhysicalField d Λ₀ => g ρ.1) =ᵐ[
      ReductionImageV3.actualReducedLaw Q] f₀ := by
    filter_upwards [] with ρ
    exact congrFun hgcomp ρ
  have hF0 : F =ᵐ[ReductionImageV3.actualReducedLaw Q] f₀ := hF.ae_eq_mk
  have hpull : (fun ρ : ReductionImageV3.ReducedPhysicalField d Λ₀ =>
      (hgmem.toLp g) ρ.1) =ᵐ[ReductionImageV3.actualReducedLaw Q] F := by
    filter_upwards [hmap, hcomp, hF0] with ρ hmap hcomp hF0
    calc
      (hgmem.toLp g) ρ.1 = g ρ.1 := hmap
      _ = f₀ ρ := hcomp
      _ = F ρ := hF0.symm
  filter_upwards [ActualImageLpStateTransport.actualImageLp_coeFn Q E (hgmem.toLp g), hpull]
    with ρ hI hp
  exact hI.trans hp

private noncomputable def actualImageLpIsometryEquiv {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 (Correctors.reducedEnvironmentLaw Q) ≃ₗᵢ[ℝ]
      Lp E 2 (ReductionImageV3.actualReducedLaw Q) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact LinearIsometryEquiv.ofSurjective
    (ActualImageLpStateTransport.actualImageLpIsometry Q E)
    (actualImageLpIsometry_surjective Q E)

def vectorLpEquiv {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (AmbientLaw Q) ≃ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q) :=
  actualImageLpIsometryEquiv Q
    (EuclideanSpace ℝ (Fin d))

noncomputable def imageHorizontalGradientMap {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    imageHorizontalH1 Q →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q) :=
  (vectorLpEquiv Q).toLinearEquiv.toLinearMap.comp
    ((Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q)).comp
      ((imageHorizontalH1Equiv Q).symm.toLinearMap))

theorem imageHorizontalGradientMap_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : imageHorizontalH1 Q) :
    imageHorizontalGradientMap Q f = imageHorizontalEuclideanGradient Q f := by
  simp [imageHorizontalGradientMap, imageHorizontalEuclideanGradient,
    vectorLpEquiv, Correctors.horizontalEuclideanGradientMap,
    actualImageLpIsometryEquiv,
    ActualImageLpStateTransport.actualImageVectorLpIsometry]

def imagePotentialGradientSubmodule {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)) :=
  (LinearMap.range (imageHorizontalGradientMap Q)).topologicalClosure

abbrev imagePotentialGradientDomain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) := imagePotentialGradientSubmodule Q

theorem imageHorizontalGradientMap_range {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    LinearMap.range (imageHorizontalGradientMap Q) =
      (LinearMap.range (Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q))).map
          (vectorLpEquiv Q).toLinearEquiv.toLinearMap := by
  ext u
  constructor
  · intro hu
    rcases LinearMap.mem_range.mp hu with ⟨f, rfl⟩
    exact Submodule.mem_map.mpr ⟨
      Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q)
        ((imageHorizontalH1Equiv Q).symm f),
      LinearMap.mem_range_self _ _, (imageHorizontalGradientMap_apply Q f).symm⟩
  · intro hu
    have hu' : (vectorLpEquiv Q).symm u ∈
        LinearMap.range (Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q)) :=
      (Submodule.mem_map_equiv
        (LinearMap.range (Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q)))).mp hu
    rcases LinearMap.mem_range.mp hu' with ⟨f, hf⟩
    refine LinearMap.mem_range.mpr ⟨(imageHorizontalH1Equiv Q) f, ?_⟩
    rw [imageHorizontalGradientMap_apply]
    calc
      imageHorizontalEuclideanGradient Q ((imageHorizontalH1Equiv Q) f) =
          (vectorLpEquiv Q) (Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
            (Correctors.reducedEnvironmentLaw_stationary Q)
            ((imageHorizontalH1Equiv Q).symm ((imageHorizontalH1Equiv Q) f))) :=
        (imageHorizontalGradientMap_apply Q _).symm
      _ = (vectorLpEquiv Q)
          (Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
            (Correctors.reducedEnvironmentLaw_stationary Q) f) := by simp
      _ = (vectorLpEquiv Q) ((vectorLpEquiv Q).symm u) := congrArg (vectorLpEquiv Q) hf
      _ = u := (vectorLpEquiv Q).apply_symm_apply u

private theorem topologicalClosure_map_vectorLpEquiv {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (S : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 (AmbientLaw Q))) :
    S.topologicalClosure.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap =
      (S.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap).topologicalClosure := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_map
      (vectorLpEquiv Q).toLinearIsometry.toContinuousLinearMap S
  · intro x hx
    have hback := Submodule.topologicalClosure_map
      (vectorLpEquiv Q).symm.toLinearIsometry.toContinuousLinearMap
      (S.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap)
    have hxback : (vectorLpEquiv Q).symm x ∈
        ((S.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap).topologicalClosure).map
          (vectorLpEquiv Q).symm.toLinearEquiv.toLinearMap := by
      exact ⟨x, hx, rfl⟩
    have hmem := hback hxback
    have hmap :
        (S.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap).map
          (vectorLpEquiv Q).symm.toLinearIsometry.toContinuousLinearMap.toLinearMap = S := by
      change ((S.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap).map
        (vectorLpEquiv Q).symm.toLinearEquiv.toLinearMap) = S
      exact (Submodule.map_symm_eq_iff (vectorLpEquiv Q).toLinearEquiv).2 rfl
    change (vectorLpEquiv Q).symm x ∈
      ((S.map (vectorLpEquiv Q).toLinearEquiv.toLinearMap).map
        (vectorLpEquiv Q).symm.toLinearIsometry.toContinuousLinearMap.toLinearMap).topologicalClosure
      at hmem
    rw [hmap] at hmem
    exact (Submodule.mem_map_equiv S.topologicalClosure).2 hmem

theorem imagePotentialGradientSubmodule_eq_map {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    imagePotentialGradientSubmodule Q =
      (Correctors.correctorPotentialDomain Q).map
        (vectorLpEquiv Q).toLinearEquiv.toLinearMap := by
  change (LinearMap.range (imageHorizontalGradientMap Q)).topologicalClosure = _
  rw [imageHorizontalGradientMap_range]
  exact (topologicalClosure_map_vectorLpEquiv Q
    (LinearMap.range (Correctors.horizontalEuclideanGradientMap (AmbientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q)))).symm

noncomputable def imagePotentialGradientEquiv {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Correctors.correctorPotentialDomain Q ≃ₗ[ℝ] imagePotentialGradientDomain Q := by
  let e := Submodule.equivMapOfInjective
    (vectorLpEquiv Q).toLinearEquiv.toLinearMap
    (vectorLpEquiv Q).injective (Correctors.correctorPotentialDomain Q)
  exact e.trans (LinearEquiv.ofEq _ _
    (imagePotentialGradientSubmodule_eq_map Q).symm)

theorem imagePotentialGradientEquiv_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G : Correctors.correctorPotentialDomain Q) :
    (imagePotentialGradientEquiv Q G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)) =
      vectorLpEquiv Q (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (AmbientLaw Q)) := rfl

theorem imagePotentialGradientEquiv_symm_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (G : imagePotentialGradientDomain Q) :
    (vectorLpEquiv Q).symm
        (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)) =
      ((imagePotentialGradientEquiv Q).symm G :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (AmbientLaw Q)) := by
  have h := congrArg Subtype.val ((imagePotentialGradientEquiv Q).apply_symm_apply G)
  rw [imagePotentialGradientEquiv_apply] at h
  have hb := congrArg (vectorLpEquiv Q).symm h
  simpa using hb.symm

theorem imagePotentialGradient_mean_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q))
    (hG : G ∈ imagePotentialGradientDomain Q) (i : Fin d) :
    ActualImageLpStateTransport.actualImageEuclideanCoordinateMean Q i G = 0 := by
  change G ∈ imagePotentialGradientSubmodule Q at hG
  rw [imagePotentialGradientSubmodule_eq_map Q] at hG
  have hG₀ : (vectorLpEquiv Q).symm G ∈ Correctors.correctorPotentialDomain Q :=
    (Submodule.mem_map_equiv (Correctors.correctorPotentialDomain Q)).1 hG
  have hbridge := ActualImageLpStateTransport.actualImageEuclideanCoordinateMean_comp
    Q ((vectorLpEquiv Q).symm G) i
  change ActualImageLpStateTransport.actualImageEuclideanCoordinateMean Q i
      ((vectorLpEquiv Q) ((vectorLpEquiv Q).symm G)) =
        Correctors.euclideanCoordinateMean (AmbientLaw Q) i
          ((vectorLpEquiv Q).symm G) at hbridge
  rw [(vectorLpEquiv Q).apply_symm_apply G] at hbridge
  rw [hbridge]
  exact Correctors.correctorPotentialDomain_mean_zero Q
    ((vectorLpEquiv Q).symm G) hG₀ i

/-- The actual-image coefficient action is transported from multiplication by the reduced
coefficient at the physical origin. -/
noncomputable def imageOriginCoefficientAction {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q) :=
  (ActualImageLpStateTransport.actualImageVectorLpIsometry Q).toContinuousLinearMap.comp
    ((Correctors.reducedOriginCoefficientAction Q).comp
      (vectorLpEquiv Q).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem imageOriginCoefficientAction_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)) :
    imageOriginCoefficientAction Q u =
      ActualImageLpStateTransport.actualImageVectorLpIsometry Q
        (Correctors.reducedOriginCoefficientAction Q
        ((vectorLpEquiv Q).symm u)) := by
  rfl

noncomputable def imageCorrectorAffineField {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q) :=
  vectorLpEquiv Q (Correctors.correctorAffineField Q i)

noncomputable def imageCorrectorFluxOfGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : imagePotentialGradientDomain Q) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q) :=
  imageOriginCoefficientAction Q
    (imageCorrectorAffineField Q i + (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)))

theorem imageCorrectorFluxOfGradient_eq_transport {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : imagePotentialGradientDomain Q) :
    imageCorrectorFluxOfGradient Q i G =
      ActualImageLpStateTransport.actualImageVectorLpIsometry Q
        (Correctors.correctorFluxOfGradient Q i
        ((vectorLpEquiv Q).symm (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)))) := by
  change imageOriginCoefficientAction Q
      (vectorLpEquiv Q (Correctors.correctorAffineField Q i) + G) =
    ActualImageLpStateTransport.actualImageVectorLpIsometry Q
      (Correctors.reducedOriginCoefficientAction Q
      (Correctors.correctorAffineField Q i +
        (vectorLpEquiv Q).symm (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q))))
  rw [imageOriginCoefficientAction_apply, map_add,
    (vectorLpEquiv Q).symm_apply_apply]

noncomputable def imageCanonicalCorrectorGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) : imagePotentialGradientDomain Q :=
  imagePotentialGradientEquiv Q (Correctors.canonicalCorrectorGradient Q i)

theorem imageCanonicalCorrectorGradient_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    (imageCanonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)) =
      vectorLpEquiv Q (Correctors.canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (AmbientLaw Q)) := rfl

theorem imageCanonicalCorrectorGradient_variational_horizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f : imageHorizontalH1 Q) :
    inner ℝ (imageHorizontalEuclideanGradient Q f)
      (imageCorrectorFluxOfGradient Q i (imageCanonicalCorrectorGradient Q i)) = 0 := by
  rw [imageHorizontalEuclideanGradient, imageCorrectorFluxOfGradient_eq_transport,
    imageCanonicalCorrectorGradient_apply]
  simp only [(vectorLpEquiv Q).symm_apply_apply]
  rw [LinearIsometry.inner_map_map]
  exact Correctors.canonicalCorrectorGradient_variational_horizontalH1 Q i
    ((imageHorizontalH1Equiv Q).symm f)

theorem imageCorrectorGradient_eq_canonical_of_horizontal_variational
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : imagePotentialGradientDomain Q)
    (hG : ∀ f : imageHorizontalH1 Q,
      inner ℝ (imageHorizontalEuclideanGradient Q f)
        (imageCorrectorFluxOfGradient Q i G) = 0) :
    G = imageCanonicalCorrectorGradient Q i := by
  have hambient : (imagePotentialGradientEquiv Q).symm G =
      Correctors.canonicalCorrectorGradient Q i := by
    apply Correctors.correctorGradient_eq_canonical_of_horizontal_variational Q i
    intro f
    have hactual := hG (imageHorizontalH1Equiv Q f)
    rw [imageHorizontalEuclideanGradient, imageCorrectorFluxOfGradient_eq_transport] at hactual
    rw [LinearIsometry.inner_map_map] at hactual
    rw [(imageHorizontalH1Equiv Q).symm_apply_apply,
      imagePotentialGradientEquiv_symm_apply] at hactual
    exact hactual
  have heq := congrArg (imagePotentialGradientEquiv Q) hambient
  simpa [imageCanonicalCorrectorGradient] using heq

theorem existsUnique_imageCanonicalCorrectorGradient_horizontalH1
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∃! G : imagePotentialGradientDomain Q,
      ∀ f : imageHorizontalH1 Q,
        inner ℝ (imageHorizontalEuclideanGradient Q f)
          (imageCorrectorFluxOfGradient Q i G) = 0 := by
  refine ⟨imageCanonicalCorrectorGradient Q i, ?_, ?_⟩
  · intro f
    exact imageCanonicalCorrectorGradient_variational_horizontalH1 Q i f
  · intro G hG
    exact imageCorrectorGradient_eq_canonical_of_horizontal_variational Q i G hG

theorem imageCanonicalCorrectorGradient_flux_coordinate_mean {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) :
    ActualImageLpStateTransport.actualImageEuclideanCoordinateMean Q j
      (imageCorrectorFluxOfGradient Q i (imageCanonicalCorrectorGradient Q i)) =
    Correctors.euclideanCoordinateMean (AmbientLaw Q) j
      (Correctors.canonicalCorrectorFlux Q i) := by
  rw [imageCorrectorFluxOfGradient_eq_transport]
  have hcan : (vectorLpEquiv Q).symm
      (imageCanonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (ImageLaw Q)) =
      Correctors.canonicalCorrectorGradient Q i := by
    rw [imageCanonicalCorrectorGradient_apply]
    exact (vectorLpEquiv Q).symm_apply_apply _
  rw [hcan, Correctors.canonicalCorrectorFlux, Correctors.correctorFluxOfGradient]
  exact ActualImageLpStateTransport.actualImageEuclideanCoordinateMean_comp Q
    (Correctors.canonicalCorrectorFlux Q i) j

end

end EinsteinRelation.ActualImageVariationalSupport
