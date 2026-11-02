import EinsteinRelation.Environment.ActualImageLpTransportSupport
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Calculus.HorizontalSobolev
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory Filter
open EinsteinRelation.ActualImageLpStateTransport
open scoped Topology

namespace EinsteinRelation.ActualImageHorizontalH1Transport

noncomputable section

private theorem actualImageLpIsometry_surjective {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Function.Surjective (ActualImageLpStateTransport.actualImageLpIsometry Q E) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  intro F
  let hF := Lp.aestronglyMeasurable F
  let f₀ := hF.mk F
  have hf₀sm : StronglyMeasurable f₀ := hF.stronglyMeasurable_mk
  obtain ⟨g, hgsm, hgcomp⟩ :=
    actualImageMeasurableEmbedding.exists_stronglyMeasurable_extend hf₀sm
      (fun _ : FieldPair d => ⟨(0 : E)⟩)
  have hgmem : MemLp g 2 (Correctors.reducedEnvironmentLaw Q) := by
    rw [show Correctors.reducedEnvironmentLaw Q =
      Measure.map (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d)
        (ReductionImageV3.actualReducedLaw Q) by
          exact (actualReducedLaw_measurePreserving Q).map_eq.symm]
    rw [actualImageMeasurableEmbedding.memLp_map_measure_iff]
    change MemLp (g ∘ (Subtype.val : ReductionImageV3.ReducedPhysicalField d L → FieldPair d))
      2 (ReductionImageV3.actualReducedLaw Q)
    rw [hgcomp]
    exact (memLp_congr_ae hF.ae_eq_mk).mp (Lp.memLp F)
  refine ⟨hgmem.toLp g, ?_⟩
  apply Lp.ext
  have hmap :=
    (actualReducedLaw_measurePreserving Q).quasiMeasurePreserving.ae hgmem.coeFn_toLp
  have hcomp : (fun ρ : ReductionImageV3.ReducedPhysicalField d L => g ρ.1) =ᵐ[
      ReductionImageV3.actualReducedLaw Q] f₀ := by
    filter_upwards [] with ρ
    exact congrFun hgcomp ρ
  have hF0 : F =ᵐ[ReductionImageV3.actualReducedLaw Q] f₀ := hF.ae_eq_mk
  have hpull : (fun ρ : ReductionImageV3.ReducedPhysicalField d L =>
      (hgmem.toLp g) ρ.1) =ᵐ[ReductionImageV3.actualReducedLaw Q] F := by
    filter_upwards [hmap, hcomp, hF0] with ρ hmap hcomp hF0
    calc
      (hgmem.toLp g) ρ.1 = g ρ.1 := hmap
      _ = f₀ ρ := hcomp
      _ = F ρ := hF0.symm
  filter_upwards [actualImageLp_coeFn Q E (hgmem.toLp g), hpull] with ρ hI hp
  exact hI.trans hp

private noncomputable def ambientImageLpEquiv {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp E 2 (Correctors.reducedEnvironmentLaw Q) ≃ₗᵢ[ℝ]
      Lp E 2 (ReductionImageV3.actualReducedLaw Q) := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  exact LinearIsometryEquiv.ofSurjective
    (ActualImageLpStateTransport.actualImageLpIsometry Q E)
    (actualImageLpIsometry_surjective Q E)

abbrev imageLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :=
  ReductionImageV3.actualReducedLaw Q

abbrev ambientLaw {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :=
  Correctors.reducedEnvironmentLaw Q

private theorem imageLaw_stationary {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d) :
    Measure.map (ActualImageLpStateTransport.reducedTranslate z)
      (imageLaw Q) = imageLaw Q :=
  ActualImageLpStateTransport.actualReducedLaw_translation_invariant Q z

/-- Translation of scalar L² classes on the actual reduced image probability law. -/
def imageTranslationLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d) :
    Lp ℝ 2 (imageLaw Q) →ₗᵢ[ℝ] Lp ℝ 2 (imageLaw Q) :=
  Lp.compMeasurePreservingₗᵢ ℝ (ActualImageLpStateTransport.reducedTranslate z)
    (ActualImageLpStateTransport.actualReducedLaw_reducedTranslation_measurePreserving Q z)

theorem coeFn_imageTranslationLp {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d) (f : Lp ℝ 2 (imageLaw Q)) :
    imageTranslationLp Q z f =ᵐ[imageLaw Q]
      fun ρ => f (ActualImageLpStateTransport.reducedTranslate z ρ) :=
  Lp.coeFn_compMeasurePreserving f
    (ActualImageLpStateTransport.actualReducedLaw_reducedTranslation_measurePreserving Q z)

/-- The ambient and actual-image L² translation actions commute with the concrete image
isometry induced by the subtype inclusion. -/
theorem scalarLpIsometry_intertwines_translation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d)
    (f : Lp ℝ 2 (ambientLaw Q)) :
    ActualImageLpStateTransport.actualImageScalarLpIsometry Q
        (EinsteinRelation.translationLp (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) z f) =
      imageTranslationLp Q z
        (ActualImageLpStateTransport.actualImageScalarLpIsometry Q f) := by
  let I := ActualImageLpStateTransport.actualImageScalarLpIsometry Q
  have hleft : I (EinsteinRelation.translationLp (ambientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q) z f) =ᵐ[imageLaw Q]
      fun ρ => EinsteinRelation.translationLp (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) z f ρ.1 :=
    ActualImageLpStateTransport.actualImageLp_coeFn Q ℝ _
  have hambient : (fun ρ => EinsteinRelation.translationLp (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) z f ρ.1) =ᵐ[imageLaw Q]
      fun ρ => f (translate z ρ.1) :=
    (ActualImageLpStateTransport.actualReducedLaw_measurePreserving Q).quasiMeasurePreserving.ae
      (EinsteinRelation.coeFn_translationLp (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) z f)
  have hI : (fun ρ => I f (ActualImageLpStateTransport.reducedTranslate z ρ)) =ᵐ[imageLaw Q]
      fun ρ => f (ActualImageLpStateTransport.reducedTranslate z ρ).1 :=
    (ActualImageLpStateTransport.actualReducedLaw_reducedTranslation_measurePreserving Q z).quasiMeasurePreserving.ae
      (ActualImageLpStateTransport.actualImageLp_coeFn Q ℝ f)
  have hright : imageTranslationLp Q z (I f) =ᵐ[imageLaw Q]
      fun ρ => I f (ActualImageLpStateTransport.reducedTranslate z ρ) :=
    coeFn_imageTranslationLp Q z (I f)
  apply Lp.ext
  filter_upwards [hleft, hambient, hI, hright] with ρ hleft hambient hI hright
  calc
    I (EinsteinRelation.translationLp (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) z f) ρ =
      EinsteinRelation.translationLp (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) z f ρ.1 := hleft
    _ = f (translate z ρ.1) := hambient
    _ = f (ActualImageLpStateTransport.reducedTranslate z ρ).1 := by
      rw [ActualImageLpStateTransport.reducedTranslate_val]
    _ = I f (ActualImageLpStateTransport.reducedTranslate z ρ) := hI.symm
    _ = imageTranslationLp Q z (I f) ρ := hright.symm

theorem scalarLpEquiv_intertwines_translation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : Vec d)
    (f : Lp ℝ 2 (ambientLaw Q)) :
    ambientImageLpEquiv Q ℝ
        (EinsteinRelation.translationLp (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) z f) =
      imageTranslationLp Q z
        (ambientImageLpEquiv Q ℝ f) := by
  simpa [ambientImageLpEquiv] using!
      scalarLpIsometry_intertwines_translation Q z f

/-- The horizontal derivative on the actual reduced image law is the two-sided strong
generator limit of its induced translation action. -/
def HasImageHorizontalLpDerivative {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f g : Lp ℝ 2 (imageLaw Q)) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => t⁻¹ • (imageTranslationLp Q (t • unitVector i) f - f))
    (𝓝[≠] (0 : ℝ)) (nhds g)

theorem HasImageHorizontalLpDerivative_unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g h : Lp ℝ 2 (imageLaw Q)}
    (hg : HasImageHorizontalLpDerivative Q i f g)
    (hh : HasImageHorizontalLpDerivative Q i f h) : g = h :=
  tendsto_nhds_unique hg hh

theorem HasImageHorizontalLpDerivative_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    HasImageHorizontalLpDerivative Q i 0 0 := by
  unfold HasImageHorizontalLpDerivative
  simpa only [map_zero, sub_self, smul_zero] using!
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : Lp ℝ 2 (imageLaw Q)))
      (nhdsWithin 0 {t : ℝ | t ≠ 0}) (nhds 0))

theorem HasImageHorizontalLpDerivative_add {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g f' g' : Lp ℝ 2 (imageLaw Q)}
    (hf : HasImageHorizontalLpDerivative Q i f f')
    (hg : HasImageHorizontalLpDerivative Q i g g') :
    HasImageHorizontalLpDerivative Q i (f + g) (f' + g') := by
  unfold HasImageHorizontalLpDerivative at *
  simpa only [map_add, add_sub_add_comm, smul_add] using hf.add hg

theorem HasImageHorizontalLpDerivative_smul {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℝ 2 (imageLaw Q)}
    (hf : HasImageHorizontalLpDerivative Q i f g) (c : ℝ) :
    HasImageHorizontalLpDerivative Q i (c • f) (c • g) := by
  unfold HasImageHorizontalLpDerivative at *
  have heq : (fun t : ℝ => t⁻¹ •
      (imageTranslationLp Q (t • unitVector i) (c • f) - c • f)) =
      (fun t : ℝ => c • (t⁻¹ •
        (imageTranslationLp Q (t • unitVector i) f - f))) := by
    funext t
    rw [map_smul, ← smul_sub, smul_comm t⁻¹ c]
  rw [heq]
  exact hf.const_smul c

/-- The actual reduced-image H¹ domain: every coordinate translation generator has a strong
L² limit under the same image law. -/
def imageHorizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Submodule ℝ (Lp ℝ 2 (imageLaw Q)) where
  carrier := {f | ∃ g : Fin d → Lp ℝ 2 (imageLaw Q),
    ∀ i, HasImageHorizontalLpDerivative Q i f (g i)}
  zero_mem' := ⟨fun _ => 0, HasImageHorizontalLpDerivative_zero Q⟩
  add_mem' := fun {f g} hf hg => by
    change ∃ df : Fin d → Lp ℝ 2 (imageLaw Q),
      ∀ i, HasImageHorizontalLpDerivative Q i f (df i) at hf
    change ∃ dg : Fin d → Lp ℝ 2 (imageLaw Q),
      ∀ i, HasImageHorizontalLpDerivative Q i g (dg i) at hg
    rcases hf with ⟨df, hdf⟩
    rcases hg with ⟨dg, hdg⟩
    exact ⟨fun i => df i + dg i, fun i =>
      HasImageHorizontalLpDerivative_add (Q := Q) (i := i) (hdf i) (hdg i)⟩
  smul_mem' := fun c {f} hf => by
    change ∃ df : Fin d → Lp ℝ 2 (imageLaw Q),
      ∀ i, HasImageHorizontalLpDerivative Q i f (df i) at hf
    rcases hf with ⟨df, hdf⟩
    exact ⟨fun i => c • df i, fun i =>
      HasImageHorizontalLpDerivative_smul (Q := Q) (i := i) (hdf i) c⟩

theorem mem_imageHorizontalH1 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : Lp ℝ 2 (imageLaw Q)) :
    f ∈ imageHorizontalH1 Q ↔
      ∃ g : Fin d → Lp ℝ 2 (imageLaw Q),
        ∀ i, HasImageHorizontalLpDerivative Q i f (g i) := Iff.rfl

theorem hasImageHorizontalLpDerivative_iff_intertwined {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f g : Lp ℝ 2 (ambientLaw Q)) :
    EinsteinRelation.HasHorizontalLpDerivative (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) i f g ↔
      HasImageHorizontalLpDerivative Q i
        (ambientImageLpEquiv Q ℝ f)
        (ambientImageLpEquiv Q ℝ g) := by
  let I := ambientImageLpEquiv Q ℝ
  have hquotient (t : ℝ) :
      I (t⁻¹ • (EinsteinRelation.translationLp (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) (t • unitVector i) f - f)) =
        t⁻¹ • (imageTranslationLp Q (t • unitVector i) (I f) - I f) := by
    rw [map_smul, map_sub, scalarLpEquiv_intertwines_translation]
  constructor
  · intro hf
    unfold EinsteinRelation.HasHorizontalLpDerivative at hf
    unfold HasImageHorizontalLpDerivative
    have heq : (fun t : ℝ => t⁻¹ •
        (imageTranslationLp Q (t • unitVector i) (I f) - I f)) =
        (fun t : ℝ => I (t⁻¹ • (EinsteinRelation.translationLp (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) (t • unitVector i) f - f))) := by
      funext t
      exact (hquotient t).symm
    rw [heq]
    exact (I.continuous.tendsto g).comp hf
  · intro hf
    unfold HasImageHorizontalLpDerivative at hf
    unfold EinsteinRelation.HasHorizontalLpDerivative
    have heq : (fun t : ℝ => I.symm (t⁻¹ •
        (imageTranslationLp Q (t • unitVector i) (I f) - I f))) =
        (fun t : ℝ => t⁻¹ • (EinsteinRelation.translationLp (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) (t • unitVector i) f - f)) := by
      funext t
      apply I.injective
      simpa only [I.apply_symm_apply] using (hquotient t).symm
    have hlim := (I.symm.continuous.tendsto (I g)).comp hf
    have hlim' : Tendsto (fun t : ℝ => I.symm (t⁻¹ •
        (imageTranslationLp Q (t • unitVector i) (I f) - I f)))
        (𝓝[≠] (0 : ℝ)) (nhds g) := by
      simpa only [Function.comp_def, I.symm_apply_apply] using! hlim
    rw [← heq]
    exact hlim'

/-- The source H¹ domain and its actual-image counterpart are linearly equivalent by the
concrete L² isometry. -/
def imageHorizontalH1Equiv {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    EinsteinRelation.horizontalH1 (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) ≃ₗ[ℝ] imageHorizontalH1 Q where
  toFun f := by
    refine ⟨ambientImageLpEquiv Q ℝ f,
      (mem_imageHorizontalH1 Q _).2 ?_⟩
    refine ⟨fun i => ambientImageLpEquiv Q ℝ
      (EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f i), ?_⟩
    intro i
    exact (hasImageHorizontalLpDerivative_iff_intertwined Q i f
      (EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f i)).mp
      (EinsteinRelation.hasHorizontalLpDerivative_horizontalH1Gradient
        (ambientLaw Q) (Correctors.reducedEnvironmentLaw_stationary Q) f i)
  invFun f := by
    have hactual := (mem_imageHorizontalH1 Q f).1 f.property
    refine ⟨(ambientImageLpEquiv Q ℝ).symm f, ?_⟩
    change ∃ g : Fin d → Lp ℝ 2 (ambientLaw Q), ∀ i,
      EinsteinRelation.HasHorizontalLpDerivative (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) i
        ((ambientImageLpEquiv Q ℝ).symm f) (g i)
    obtain ⟨g, hg⟩ := hactual
    refine ⟨fun i => (ambientImageLpEquiv Q ℝ).symm (g i), ?_⟩
    intro i
    exact (hasImageHorizontalLpDerivative_iff_intertwined Q i
      ((ambientImageLpEquiv Q ℝ).symm f)
      ((ambientImageLpEquiv Q ℝ).symm (g i))).mpr
      (by simpa using hg i)
  left_inv f := by
    apply Subtype.ext
    exact (ambientImageLpEquiv Q ℝ).symm_apply_apply f
  right_inv f := by
    apply Subtype.ext
    exact (ambientImageLpEquiv Q ℝ).apply_symm_apply f
  map_add' f g := by
    apply Subtype.ext
    exact map_add (ambientImageLpEquiv Q ℝ)
      (f : Lp ℝ 2 (ambientLaw Q)) (g : Lp ℝ 2 (ambientLaw Q))
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (ambientImageLpEquiv Q ℝ) c
      (f : Lp ℝ 2 (ambientLaw Q))

/-- The actual-image horizontal derivative coordinates, transported from the source generator
by the proven translation intertwining. -/
theorem imageHorizontalH1Gradient_coordinate_derivative {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : imageHorizontalH1 Q) (i : Fin d) :
    HasImageHorizontalLpDerivative Q i (f : Lp ℝ 2 (imageLaw Q))
      (ambientImageLpEquiv Q ℝ
        (EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q)
          ((imageHorizontalH1Equiv Q).symm f) i)) := by
  let x := (imageHorizontalH1Equiv Q).symm f
  have hsrc := EinsteinRelation.hasHorizontalLpDerivative_horizontalH1Gradient
    (ambientLaw Q) (Correctors.reducedEnvironmentLaw_stationary Q) x i
  have htrans := (hasImageHorizontalLpDerivative_iff_intertwined Q i x
      (EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) x i)).mp hsrc
  have hx : ambientImageLpEquiv Q ℝ x = f := by
    exact congrArg Subtype.val ((imageHorizontalH1Equiv Q).apply_symm_apply f)
  rw [← hx]
  exact htrans

/-- The Euclidean horizontal gradient on the actual image is transported by the actual vector
L² isometry, preserving the paper's Euclidean-valued gradient. -/
noncomputable def imageHorizontalEuclideanGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : imageHorizontalH1 Q) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (imageLaw Q) :=
  ActualImageLpStateTransport.actualImageVectorLpIsometry Q
    (Correctors.horizontalEuclideanGradient (ambientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q) ((imageHorizontalH1Equiv Q).symm f))

theorem imageVectorLpIsometry_coordinate {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ambientLaw Q)) :
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2
        (imageLaw Q))
      (ActualImageLpStateTransport.actualImageVectorLpIsometry Q G) =
    ActualImageLpStateTransport.actualImageScalarLpIsometry Q
      (((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2
        (ambientLaw Q)) G) := by
  let π := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i
  have hπa :=
    (ActualImageLpStateTransport.actualReducedLaw_measurePreserving Q).quasiMeasurePreserving.ae
      (ContinuousLinearMap.coeFn_compLpL π G
        (p := 2) (μ := ambientLaw Q))
  apply Lp.ext
  filter_upwards [
    ContinuousLinearMap.coeFn_compLpL π
      (ActualImageLpStateTransport.actualImageVectorLpIsometry Q G)
      (p := 2) (μ := imageLaw Q),
    ActualImageLpStateTransport.actualImageLp_coeFn Q
      (EuclideanSpace ℝ (Fin d)) G,
    ActualImageLpStateTransport.actualImageLp_coeFn Q ℝ
      ((π.compLpL 2 (ambientLaw Q)) G),
    hπa] with ρ hπv hV hS hπa
  calc
    ((π.compLpL 2 (imageLaw Q))
        (ActualImageLpStateTransport.actualImageVectorLpIsometry Q G)) ρ =
      π (ActualImageLpStateTransport.actualImageVectorLpIsometry Q G ρ) := by
        simpa only [ContinuousLinearMap.coeFn_compLpL] using hπv
    _ = π (G ρ.1) := by
      rw [ActualImageLpStateTransport.actualImageVectorLpIsometry, hV]
    _ = ((π.compLpL 2 (ambientLaw Q)) G) ρ.1 := by
      simpa only [ContinuousLinearMap.coeFn_compLpL] using hπa.symm
    _ = ActualImageLpStateTransport.actualImageScalarLpIsometry Q
        ((π.compLpL 2 (ambientLaw Q)) G) ρ := hS.symm

theorem ambientEuclideanGradient_coordinate_projection {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : EinsteinRelation.horizontalH1 (ambientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q)) (i : Fin d) :
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2
        (ambientLaw Q))
      (Correctors.horizontalEuclideanGradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f) =
    EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q) f i := by
  let π := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i
  apply Lp.ext
  filter_upwards [
    ContinuousLinearMap.coeFn_compLpL π
      (Correctors.horizontalEuclideanGradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f)
      (p := 2) (μ := ambientLaw Q),
    Correctors.horizontalEuclideanGradient_coordinates (ambientLaw Q)
      (Correctors.reducedEnvironmentLaw_stationary Q) f i] with ω hπ hcoord
  calc
    ((π.compLpL 2 (ambientLaw Q))
        (Correctors.horizontalEuclideanGradient (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q) f)) ω =
      π (Correctors.horizontalEuclideanGradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f ω) := by
          simpa only [ContinuousLinearMap.coeFn_compLpL] using hπ
    _ = Correctors.horizontalEuclideanGradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f ω i := by
          simp [π, PiLp.proj_apply]
    _ = EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q) f i ω := hcoord

theorem imageHorizontalEuclideanGradient_coordinate {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : imageHorizontalH1 Q) (i : Fin d) :
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2
        (imageLaw Q)) (imageHorizontalEuclideanGradient Q f) =
      ambientImageLpEquiv Q ℝ
        (EinsteinRelation.horizontalH1Gradient (ambientLaw Q)
          (Correctors.reducedEnvironmentLaw_stationary Q)
          ((imageHorizontalH1Equiv Q).symm f) i) := by
  rw [imageHorizontalEuclideanGradient,
    imageVectorLpIsometry_coordinate,
    ambientEuclideanGradient_coordinate_projection]
  simp [ambientImageLpEquiv]
  rfl

theorem imageHorizontalEuclideanGradient_norm {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : imageHorizontalH1 Q) :
    ‖imageHorizontalEuclideanGradient Q f‖ =
      ‖Correctors.horizontalEuclideanGradient (ambientLaw Q)
        (Correctors.reducedEnvironmentLaw_stationary Q)
        ((imageHorizontalH1Equiv Q).symm f)‖ := by
  exact (ActualImageLpStateTransport.actualImageVectorLpIsometry Q).norm_map _

/-- Actual-image expectation for the transferred canonical variational equation, consumed at a
genuine actual-image H¹ observable. -/
theorem canonicalVariational_orthogonal_imageHorizontalGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f : imageHorizontalH1 Q) :
    inner ℝ (imageHorizontalEuclideanGradient Q f)
      (ActualImageLpStateTransport.actualImageVectorLpIsometry Q
        (Correctors.canonicalCorrectorFlux Q i)) = 0 := by
  rw [imageHorizontalEuclideanGradient]
  rw [LinearIsometry.inner_map_map]
  exact Correctors.canonicalCorrectorGradient_variational_horizontalH1 Q i
    ((imageHorizontalH1Equiv Q).symm f)

end

end EinsteinRelation.ActualImageHorizontalH1Transport
