import EinsteinFull.Calculus.C8GMPRealizationExists
import EinsteinFull.Calculus.C8FoundationGMPAssociation
import EinsteinFull.Calculus.C16ReducedGeneratorAE
import EinsteinFull.Blueprint.G1.Proofs.SbxS4RemainderMoment
import MarkovProcess.Semigroup.ResolventGeneration
import MarkovProcess.Kernel.PositiveC0Resolvent

open MeasureTheory Filter Set
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open EinsteinRelation.SpatialDirichlet
open MarkovProcess.Semigroup
open scoped NNReal ENNReal Topology BigOperators Pointwise Convolution

noncomputable section
namespace EinsteinFull
open Blueprint

/-- Bounded data for the regular-field physical resolvent have a continuous
representative; the local normalized equation needs no smooth-field hypothesis. -/
theorem u2_regular_physical_resolvent_continuousRepresentative
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ M : ℝ, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ M) :
    ∃ u : Vec d → ℝ, Continuous u ∧
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  obtain ⟨M, hM⟩ := hf
  have hC : 0 < |M| + 1 := by positivity
  have hfC : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, |f y| ≤ |M| + 1 :=
    hM.mono fun _ hy => hy.trans (by linarith [le_abs_self M])
  have hloc : ∀ x : Vec d, ∃ (U : Set (Vec d)) (v : Vec d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContinuousOn v U ∧
      v =ᵐ[volume.restrict U]
        (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value := by
    intro x
    let k := Λ / sourcePhysicalDensity ω hd lam x
    let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
    let e := PDE.ellipticNormalizerContinuousLinearEquiv
      (gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x)
    let T := PDE.ellipticNormalizer A0
    let a := fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
      ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T
    obtain ⟨r, hr, u, F, hvalue, hEll, hu, hF, hSmall⟩ :=
      gmpPhysicalResolvent_localNormalizedSchauderData hd ω lam Λ hΛ hω α hα f hC hfC x
    have ha : Continuous a := by
      have hc := (gmpPhysicalCoefficient_continuous hd ω lam).comp e.symm.continuous
      exact (((hc.const_smul k).sub continuous_const).const_mul T).mul_const
        (PDE.matTranspose T)
    have hδ : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
        d (1 / 2) := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold_nonneg
        d (by norm_num)
    obtain ⟨U, v, hU, hx, _, hv, heq⟩ :=
      gmpMatrixSmallContrast_ballLocalContinuousRepresentative hd ha hr hEll hδ le_rfl hSmall hu hF
    let W := e ⁻¹' U
    have hW : IsOpen W := hU.preimage e.continuous
    have hq : Measure.QuasiMeasurePreserving e (volume.restrict W) (volume.restrict U) := by
      refine ⟨e.continuous.measurable, ?_⟩
      rw [PDE.map_linearEquiv_volumeOn,
        show e '' W = U from Set.image_preimage_eq U e.surjective]
      exact Measure.smul_absolutelyContinuous
    refine ⟨W, (fun y => v (e y)), hW, hx,
      hv.comp e.continuous.continuousOn (fun _ hy => hy), ?_⟩
    filter_upwards [hq.ae heq] with y hy
    change v (e y) = _ at hy
    rw [hvalue] at hy
    change v (e y) = (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value
      (e.symm (e y)) at hy
    simpa only [e.symm_apply_apply] using hy
  obtain ⟨u, hu, heq⟩ := gmpContinuousRepresentative_of_local hloc
  refine ⟨u, hu, (gmpPhysical_ae_iff_volume hd ω lam _).mpr ?_⟩
  exact heq.trans (gmpPhysicalResolventGraph_value_ae hd ω lam Λ hΛ hω α hα f)


/-- The regular-field resolvent admits its unique C₀ representative for bounded compact data. -/
theorem u2_regular_physical_resolvent_exists_unique_zeroAtInfty
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    {R : ℝ} (hR : 0 ≤ R)
    (hcompact : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      R ≤ euclideanNorm x → f x = 0) :
    ∃! u : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (u : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  obtain ⟨u, hu, heq⟩ :=
    u2_regular_physical_resolvent_continuousRepresentative hd ω lam Λ hΛ hω α hα f ⟨C, hf⟩
  have hbound : ∀ x, |u x| ≤ C / α :=
    gmpPhysicalResolvent_continuousRepresentative_abs_le hd ω lam Λ hΛ hω α hα f hC hf hu heq
  obtain ⟨k, hk, hbarrier⟩ :=
    gmpPhysicalResolvent_radialBarrier_abs_le_and_tendsto_zero hd ω lam Λ hΛ hω α hα
  have hzero : Tendsto u (Filter.cocompact (Vec d)) (𝓝 0) :=
    (hbarrier f (div_nonneg hC.le hα.le) R hR u hu hbound heq hcompact).2
  let U : ZeroAtInftyContinuousMap (Vec d) ℝ :=
    { toFun := u, continuous_toFun := hu, zero_at_infty' := hzero }
  refine ⟨U, heq, ?_⟩
  intro v hv
  apply DFunLike.coe_injective
  exact gmpPhysical_continuousRepresentative_unique hd ω lam v.continuous U.continuous
    (hv.trans heq.symm)



theorem u2_regular_compact_resolvent_exists_unique
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Vec d → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ∃! u : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (u : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.bddAbove_image
    (EinsteinRelation.Entropy.continuous_euclideanNorm' (d := d)).continuousOn
  let C := max B 0 + 1
  let r := max R 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hb : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |F x| ≤ C := by
    filter_upwards [hF] with x hx
    rw [hx]
    calc
      |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
      _ ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hsupport : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      r ≤ euclideanNorm x → F x = 0 := by
    filter_upwards [hF] with x hx hxr
    rw [hx]
    by_contra hne
    have hxs : x ∈ Function.support f := hne
    have ht : x ∈ tsupport f := subset_closure hxs
    have hbound := hR (Set.mem_image_of_mem _ ht)
    dsimp [r] at hxr
    linarith [le_max_left R 0]
  exact u2_regular_physical_resolvent_exists_unique_zeroAtInfty hd ω lam Λ hΛ hω
    α hα F hC hb hr hsupport


/-- The C₀ representative of the physical resolvent on compactly supported data. -/
noncomputable def u2RegularCompactResolvent {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d) : ZeroAtInftyContinuousMap (Vec d) ℝ :=
  Classical.choose (u2_regular_compact_resolvent_exists_unique
    hd ω lam Λ hΛ hω α hα f.1 f.1.continuous f.2
    (gmpPhysicalC0CompactToLp hd ω lam f) (gmpPhysicalC0CompactToLp_ae hd ω lam f))

/-- The compact-data C₀ resolvent represents the actual physical L² resolvent. -/
theorem u2_regular_compact_resolvent_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d) :
    (u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα (gmpPhysicalC0CompactToLp hd ω lam f) :=
  (Classical.choose_spec (u2_regular_compact_resolvent_exists_unique
    hd ω lam Λ hΛ hω α hα f.1 f.1.continuous f.2
    (gmpPhysicalC0CompactToLp hd ω lam f) (gmpPhysicalC0CompactToLp_ae hd ω lam f))).1


/-- The compact-data resolvent is independent of the chosen L² representative. -/
theorem u2_regular_compact_resolvent_ae_of_rep {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f.1) :
    (u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  have hclass : gmpPhysicalC0CompactToLp hd ω lam f = F :=
    Lp.ext ((gmpPhysicalC0CompactToLp_ae hd ω lam f).trans hF.symm)
  simpa only [hclass] using
    u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα f



/-- The compact-data physical resolvent as a linear map into C₀. -/
noncomputable def u2RegularCompactResolventLinear {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    gmpC0CompactSubmodule d →ₗ[ℝ] ZeroAtInftyContinuousMap (Vec d) ℝ where
  toFun := u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα
  map_add' f g := by
    let U := u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα
    let R := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
    let F := gmpPhysicalC0CompactToLpLinear hd ω lam
    have hae : (U (f + g) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        (U f + U g : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
      have hsum := u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα (f + g)
      change (U (f + g) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] R (F (f + g)) at hsum
      rw [map_add, map_add] at hsum
      filter_upwards [hsum,
        u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα f,
        u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα g,
        Lp.coeFn_add (R (F f)) (R (F g))] with x hs hf hg hadd
      change U (f + g) x = (R (F f) + R (F g)) x at hs
      change U f x = R (F f) x at hf
      change U g x = R (F g) x at hg
      change (R (F f) + R (F g)) x = R (F f) x + R (F g) x at hadd
      change U (f + g) x = U f x + U g x
      rw [hs, hadd, hf, hg]
    ext x
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (U (f + g)).continuous (U f + U g).continuous hae) x
  map_smul' c f := by
    let U := u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα
    let R := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
    let F := gmpPhysicalC0CompactToLpLinear hd ω lam
    have hae : (U (c • f) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        (c • U f : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
      have hsmul := u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα (c • f)
      change (U (c • f) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] R (F (c • f)) at hsmul
      rw [map_smul, map_smul] at hsmul
      filter_upwards [hsmul,
        u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα f,
        Lp.coeFn_smul c (R (F f))] with x hs hf hcoeff
      change U (c • f) x = (c • R (F f)) x at hs
      change U f x = R (F f) x at hf
      change (c • R (F f)) x = c * R (F f) x at hcoeff
      change U (c • f) x = c * U f x
      rw [hs, hcoeff, hf]
    ext x
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (U (c • f)).continuous (c • U f).continuous hae) x


/-- The compact-data physical resolvent obeys the supremum norm bound. -/
theorem u2_regular_compact_resolvent_norm_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d) :
    ‖u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα f‖ ≤
      α⁻¹ * ‖f.1‖ := by
  let U := u2RegularCompactResolvent hd ω lam Λ hΛ hω α hα f
  have hbound : ∀ x, |U x| ≤ α⁻¹ * ‖f.1‖ := by
    intro x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hC : 0 < ‖f.1‖ + ε * α := by positivity
    have hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        |gmpPhysicalC0CompactToLp hd ω lam f x| ≤ ‖f.1‖ + ε * α := by
      filter_upwards [gmpPhysicalC0CompactToLp_ae hd ω lam f] with y hy
      rw [hy]
      have hb := BoundedContinuousFunction.norm_coe_le_norm f.1.toBCF y
      change ‖f.1 y‖ ≤ ‖f.1‖ at hb
      rw [Real.norm_eq_abs] at hb
      linarith [mul_pos hε hα]
    have h := gmpPhysicalResolvent_continuousRepresentative_abs_le hd ω lam Λ hΛ hω
      α hα (gmpPhysicalC0CompactToLp hd ω lam f) hC hf U.continuous
      (u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα f) x
    have hαne : α ≠ 0 := ne_of_gt hα
    convert h using 1
    field_simp
  change ‖U.toBCF‖ ≤ α⁻¹ * ‖f.1‖
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (inv_nonneg.mpr (le_of_lt hα))
    (norm_nonneg _))).2
  intro x
  change ‖U x‖ ≤ α⁻¹ * ‖f.1‖
  simpa only [Real.norm_eq_abs] using hbound x




/-- The C₀ space inherits its seminormed additive group structure. -/
local instance instU2C0SeminormedAddCommGroup (d : ℕ) :
    SeminormedAddCommGroup (ZeroAtInftyContinuousMap (Vec d) ℝ) := inferInstance
/-- The compactly supported C₀ submodule inherits its seminormed group structure. -/
local instance instU2CompactC0SeminormedAddCommGroup (d : ℕ) :
    SeminormedAddCommGroup (gmpC0CompactSubmodule d) := inferInstance

/-- The physical L² resolvent has a unique bounded C₀ extension for regular fields. -/
theorem u2_regular_c0_resolvent_existsUnique
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ∃! U : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ]
        ZeroAtInftyContinuousMap (Vec d) ℝ,
      ‖U‖ ≤ α⁻¹ ∧
      ∀ (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
        HasCompactSupport (f : Vec d → ℝ) →
        ∀ (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
          (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (f : Vec d → ℝ) →
          (U f : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
            gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  let e := (gmpC0CompactSubmodule d).subtype
  let T := u2RegularCompactResolventLinear hd ω lam Λ hΛ hω α hα
  have hden : DenseRange e := by
    exact denseRange_subtype_val.mpr (gmpC0CompactSubmodule_dense d)
  have hb : ∀ f, ‖T f‖ ≤ α⁻¹ * ‖e f‖ := by
    intro f
    exact u2_regular_compact_resolvent_norm_le hd ω lam Λ hΛ hω α hα f
  let U := T.extendOfNorm e
  have hU : ∀ f, U (e f) = T f :=
    T.extendOfNorm_eq hden ⟨α⁻¹, hb⟩
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hden (inv_nonneg.mpr (le_of_lt hα)) hb
  · intro f hf F hF
    have heq := u2_regular_compact_resolvent_ae_of_rep hd ω lam Λ hΛ hω
      α hα ⟨f, hf⟩ F hF
    change (T ⟨f, hf⟩ : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] _ at heq
    rw [← hU ⟨f, hf⟩] at heq
    exact heq
  · intro V hV
    symm
    apply LinearMap.extendOfNorm_unique hden α⁻¹ hb V
    ext f x
    have hVf := hV.2 f.1 f.2 (gmpPhysicalC0CompactToLp hd ω lam f)
      (gmpPhysicalC0CompactToLp_ae hd ω lam f)
    have hTf := u2_regular_compact_resolvent_ae hd ω lam Λ hΛ hω α hα f
    have heq : (V f.1 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] T f :=
      hVf.trans hTf.symm
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (V f.1).continuous (T f).continuous heq) x



/-- The unique C₀ extension of the actual physical resolvent. -/
noncomputable def u2RegularC0Resolvent {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ZeroAtInftyContinuousMap (Vec d) ℝ :=
  Classical.choose (u2_regular_c0_resolvent_existsUnique hd ω lam Λ hΛ hω α hα)

/-- The C₀ physical resolvent has the inverse-parameter operator bound. -/
theorem u2RegularC0Resolvent_norm_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ‖u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα‖ ≤ α⁻¹ :=
  (Classical.choose_spec (u2_regular_c0_resolvent_existsUnique
    hd ω lam Λ hΛ hω α hα)).1.1

/-- The C₀ physical resolvent agrees with the physical L² resolvent on compact data. -/
theorem u2_regular_c0_resolvent_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (hf : HasCompactSupport (f : Vec d → ℝ))
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (f : Vec d → ℝ)) :
    (u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F :=
  (Classical.choose_spec (u2_regular_c0_resolvent_existsUnique
    hd ω lam Λ hΛ hω α hα)).1.2 f hf F hF


/-- Simultaneous C₀ and L² approximation transfers physical resolvent agreement. -/
theorem u2_regular_c0_resolvent_ae_of_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ)
    (Fn : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hcompact : ∀ n, HasCompactSupport (fn n : Vec d → ℝ))
    (hae : ∀ n, (Fn n : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] fn n)
    (hf : Tendsto fn atTop (𝓝 f)) (hF : Tendsto Fn atTop (𝓝 F)) :
    (u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  let U := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hG : Tendsto (fun n => G (Fn n)) atTop (𝓝 (G F)) := G.continuous.tendsto F |>.comp hF
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hU : Tendsto (fun n => U (fn n)) atTop (𝓝 (U f)) := U.continuous.tendsto f |>.comp hf
  have hpoint (x : Vec d) : Tendsto (fun n => (U (fn (ns n))) x) atTop (𝓝 ((U f) x)) := by
    have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
      (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
    exact (heval.tendsto (U f)).comp (hU.comp hns.tendsto_atTop)
  have heq : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∀ n, (U (fn (ns n))) x = (G (Fn (ns n))) x := by
    apply ae_all_iff.mpr
    intro n
    exact u2_regular_c0_resolvent_ae hd ω lam Λ hΛ hω α hα
      (fn (ns n)) (hcompact (ns n)) (Fn (ns n)) (hae (ns n))
  filter_upwards [hlim, heq] with x hx he
  apply tendsto_nhds_unique (hpoint x)
  simpa only [he] using hx


/-- The actual C₀ and physical L² resolvents agree on every common input. -/
theorem u2_regular_c0_resolvent_ae_of_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    (u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  have hf : MemLp (f : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam) := (Lp.memLp F).ae_eq hae
  have hF : hf.toLp (f : Vec d → ℝ) = F := by
    rw [MemLp.toLp_congr hf (Lp.memLp F) hae.symm, Lp.toLp_coeFn]
  obtain ⟨fn, hfn, hc, hconv, hL2⟩ := gmpPhysicalC0_compact_approximation hd ω lam f hf
  apply u2_regular_c0_resolvent_ae_of_approximation hd ω lam Λ hΛ hω α hα
    f F fn (fun n => (hfn n).toLp (fn n : Vec d → ℝ)) hc
    (fun n => (hfn n).coeFn_toLp) hconv
  simpa only [hF] using hL2

/-- The actual C₀ resolvents satisfy the two-parameter resolvent identity. -/
theorem u2_regular_c0_resolvent_identity {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f -
        u2RegularC0Resolvent hd ω lam Λ hΛ hω β hβ f =
      (β - α) • u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
        (u2RegularC0Resolvent hd ω lam Λ hΛ hω β hβ f) := by
  let U := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  let V := u2RegularC0Resolvent hd ω lam Λ hΛ hω β hβ
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  let H := gmpPhysicalResolvent hd ω lam Λ hΛ hω β hβ
  have hcompact : ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      HasCompactSupport (f : Vec d → ℝ) → U f - V f = (β - α) • U (V f) := by
    intro f hf
    have hm := gmpPhysical_compactContinuous_memLp hd ω lam (f : Vec d → ℝ) f.continuous hf
    let F := hm.toLp (f : Vec d → ℝ)
    have hFa : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f := hm.coeFn_toLp
    have hu := u2_regular_c0_resolvent_ae_of_memLp hd ω lam Λ hΛ hω α hα f F hFa
    have hv := u2_regular_c0_resolvent_ae_of_memLp hd ω lam Λ hΛ hω β hβ f F hFa
    have huv := u2_regular_c0_resolvent_ae_of_memLp hd ω lam Λ hΛ hω α hα (V f) (H F) hv.symm
    have hres := gmpPhysicalResolvent_identity hd ω lam Λ hΛ hω α β hα hβ F
    have hae : ((U f - V f : ZeroAtInftyContinuousMap (Vec d) ℝ) : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam] ((β - α) • U (V f) : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
      filter_upwards [hu, hv, huv, Lp.coeFn_sub (G F) (H F),
        Lp.coeFn_smul (β - α) (G (H F))] with x hux hvx huvx hsub hsmul
      have hx := congrArg (fun v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => v x) hres
      change (U f) x - (V f) x = (β - α) * (U (V f)) x
      change (G F - H F) x = ((β - α) • G (H F)) x at hx
      rw [hsub, hsmul] at hx
      change (G F) x - (H F) x = (β - α) * (G (H F)) x at hx
      rw [hux, hvx, huvx]
      exact hx
    ext x
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (U f - V f).continuous ((β - α) • U (V f)).continuous hae) x
  have heq : (fun f => U f - V f) = (fun f => (β - α) • U (V f)) := by
    apply Continuous.ext_on (gmpC0CompactSubmodule_dense d)
      (show Continuous (fun f => U f - V f) from U.continuous.sub V.continuous)
      (show Continuous (fun f => (β - α) • U (V f)) from
        ((U.continuous.comp V.continuous).const_smul (β - α)))
    intro f hf
    exact hcompact f hf
  exact congrFun heq f



/-- The scaled regular-field C₀ resolvent preserves the unit interval. -/
theorem u2_regular_c0_resolvent_submarkov {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ α * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ∧
      α * u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x ≤ 1 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose g hgc hgb hgK hga using fun n : ℕ =>
    gmpC0_exists_bounded_compact_cutoff f ∅ isCompact_empty (hε n)
  let fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ := fun n => f * g n
  have hc (n : ℕ) : HasCompactSupport (fn n : Vec d → ℝ) :=
    HasCompactSupport.mul_left (hgc n)
  have hfn (n : ℕ) : MemLp (fn n : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam) :=
    gmpPhysical_compactContinuous_memLp hd ω lam (fn n) (fn n).continuous (hc n)
  have hb (n : ℕ) : ‖fn n - f‖ ≤ ε n := by
    change ‖(fn n - f).toBCF‖ ≤ ε n
    apply (BoundedContinuousFunction.norm_le (le_of_lt (hε n))).2
    intro x
    change ‖(f * g n) x - f x‖ ≤ ε n
    simpa only [Real.norm_eq_abs] using hga n x
  have hconv : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb hεlim
  let U := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  have hpoint (n : ℕ) (x : Vec d) : 0 ≤ α * U (fn n) x ∧ α * U (fn n) x ≤ 1 := by
    let F := (hfn n).toLp (fn n : Vec d → ℝ)
    have hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] fn n :=
      (hfn n).coeFn_toLp
    have hF0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] F := by
      filter_upwards [hF] with y hy
      rw [hy]
      change 0 ≤ f y * g n y
      exact mul_nonneg (hf y).1 (hgb n y).1
    have hF1 : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, F y ≤ 1 := by
      filter_upwards [hF] with y hy
      rw [hy]
      change f y * g n y ≤ 1
      nlinarith [(hf y).1, (hf y).2, (hgb n y).1, (hgb n y).2,
        mul_nonneg (sub_nonneg.mpr (hf y).2) (hgb n y).1]
    have hae := u2_regular_c0_resolvent_ae hd ω lam Λ hΛ hω α hα (fn n) (hc n) F hF
    have hs := gmpPhysicalResolvent_submarkov hd ω lam Λ hΛ hω α hα hF0 hF1
    have hvol : ∀ᵐ y ∂volume, 0 ≤ α * U (fn n) y ∧ α * U (fn n) y ≤ 1 :=
      (gmpPhysical_ae_iff_volume hd ω lam _).mp (by
        filter_upwards [hae, hs] with y hy hsy
        rw [← hy] at hsy
        exact hsy)
    have hclosed : IsClosed {y : Vec d | 0 ≤ α * U (fn n) y ∧ α * U (fn n) y ≤ 1} :=
      (isClosed_le continuous_const ((U (fn n)).continuous.const_mul α)).inter
        (isClosed_le ((U (fn n)).continuous.const_mul α) continuous_const)
    have hall : {y : Vec d | 0 ≤ α * U (fn n) y ∧ α * U (fn n) y ≤ 1} = Set.univ :=
      (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hvol)
    have hx : x ∈ {y : Vec d | 0 ≤ α * U (fn n) y ∧ α * U (fn n) y ≤ 1} := by
      rw [hall]; exact Set.mem_univ x
    exact hx
  intro x
  have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
    (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hlim : Tendsto (fun n => α * U (fn n) x) atTop (𝓝 (α * U f x)) :=
    ((heval.tendsto (U f)).comp ((U.continuous.tendsto f).comp hconv)).const_mul α
  exact ⟨ge_of_tendsto' hlim (fun n => (hpoint n x).1),
    le_of_tendsto' hlim (fun n => (hpoint n x).2)⟩

/-- The physical resolvent inverts its actual generator on every compact smooth test. -/
theorem u2_regular_physical_resolvent_compactTest {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (α • gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
        sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc) =
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) := by
  symm
  apply gmpPhysicalResolvent_unique hd ω lam Λ hΛ hω α hα
  · exact (gmpPhysicalH1Value_range_iff hd ω lam Λ hω _).mp ⟨_, rfl⟩
  · rintro v ⟨w, rfl⟩
    change α * inner ℝ
      (gmpPhysicalH1Value hd ω lam Λ hω (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc))
      (gmpPhysicalH1Value hd ω lam Λ hω w) + gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc))
      (gmpPhysicalH1Value hd ω lam Λ hω w) = inner ℝ _ (gmpPhysicalH1Value hd ω lam Λ hω w)
    rw [gmpPhysicalH1Form_value, gmpPhysicalH1Energy_symm,
      gmpPhysicalH1Energy_eq_source,
      sbxS4_compactTest_fullDomain_generatorInner hd Λ ω hω lam (lt_of_lt_of_le zero_lt_one hΛ)]
    change α * inner ℝ
      (gmpPhysicalH1Value hd ω lam Λ hω (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc))
      (gmpPhysicalH1Value hd ω lam Λ hω w) - inner ℝ (gmpPhysicalH1Value hd ω lam Λ hω w)
      (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc) =
      inner ℝ _ (gmpPhysicalH1Value hd ω lam Λ hω w)
    rw [inner_sub_left, real_inner_smul_left,
      real_inner_comm (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc)
        (gmpPhysicalH1Value hd ω lam Λ hω w)]


/-- Compact smooth tests belong to the actual weighted L² generator domain
for every regular coefficient field. -/
theorem u2_regular_semigroup_compactTest_mem_generatorDomain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) ∈
        (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  change _ ∈ (R.generatedSemigroup.generatorDomain :
    Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
  rw [R.generatorDomain_eq_range α]
  exact ⟨_, u2_regular_physical_resolvent_compactTest hd ω lam Λ hΛ hω
    α α.property φ hφ hc⟩

/-- The weighted L² generator on compact tests is the actual physical generator,
including when the coefficients are only regular. -/
theorem u2_regular_semigroup_generator_compactTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator
      ⟨gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc),
        u2_regular_semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω φ hφ hc⟩ =
      sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  calc
    _ = (α : ℝ) • gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
        ((α : ℝ) • gmpPhysicalH1Value hd ω lam Λ hω
          (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
          sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc) :=
      R.generator_apply_of_operator_eq α
        (u2_regular_semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω φ hφ hc)
        (u2_regular_physical_resolvent_compactTest hd ω lam Λ hΛ hω
          α α.property φ hφ hc)
    _ = _ := sub_sub_cancel _ _

/-- The regular physical semigroup satisfies the compact-test evolution formula
as an identity in the actual weighted L² space. -/
theorem u2_regular_semigroup_compactTest_evolution {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (t : ℝ≥0) :
    gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
        (gmpPhysicalH1Value hd ω lam Λ hω
          (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) -
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) =
      ∫ s in (0 : ℝ)..(t : ℝ),
        gmpPhysicalSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s)
          (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc) := by
  have h := (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).operator_sub_eq_integral
    ⟨gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc),
      u2_regular_semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω φ hφ hc⟩ t
  rw [u2_regular_semigroup_generator_compactTest] at h
  exact h


/-- The scaled physical resolvent differs from a compact test by its resolved generator. -/
theorem u2_regular_physical_resolvent_compactTest_sub {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    α • gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) -
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) =
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc) := by
  have h := u2_regular_physical_resolvent_compactTest hd ω lam Λ hΛ hω α hα φ hφ hc
  rw [map_sub, map_smul] at h
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

/-- Compact smooth tests are approximated uniformly almost everywhere at rate `C / α`. -/
theorem u2_regular_physical_resolvent_compactTest_approximation {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α),
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        |α * gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
          (gmpPhysicalH1Value hd ω lam Λ hω
            (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) x - φ x| ≤ C / α := by
  obtain ⟨B, _hB, hboundB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hφ hc
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun α hα => ?_⟩
  let u := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  let f := sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam φ hφ hc
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hfC : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C := by
    filter_upwards [(sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hφ hc).coeFn_toLp] with x hx
    change f x = physicalGenerator (firstCoordinateIndex hd) ω lam φ x at hx
    rw [hx]
    calc
      |physicalGenerator (firstCoordinateIndex hd) ω lam φ x| ≤ B := hboundB x
      _ ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hb := gmpPhysicalResolvent_abs_le hd ω lam Λ hΛ hω α hα hC hfC
  have hid : α • G u - u = G f :=
    u2_regular_physical_resolvent_compactTest_sub hd ω lam Λ hΛ hω α hα φ hφ hc
  have hid' : (α • G u - u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =ᵐ[
      physicalReversibleMeasure ω hd lam] G f := Filter.EventuallyEq.of_eq
    (congrArg (fun z : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => (z : Vec d → ℝ)) hid)
  filter_upwards [hb, hid', Lp.coeFn_sub (α • G u) u, Lp.coeFn_smul α (G u),
    gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc] with x hx he hs hm hu
  change |α * G u x - φ x| ≤ C / α
  change |G f x| ≤ C / α at hx
  change (α • G u - u) x = G f x at he
  rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu] at he
  exact he.symm ▸ hx


/-- Continuous representatives of scaled resolvents approximate smooth compact
support tests uniformly, with a constant independent of the resolvent parameter. -/
theorem u2_regular_physical_resolvent_compactTest_pointwise_approximation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α)
      (u : Vec d → ℝ), Continuous u →
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
          (gmpPhysicalH1Value hd ω lam Λ hω
            (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) →
      ∀ x, |α * u x - φ x| ≤ C / α := by
  obtain ⟨C, hC, hbound⟩ :=
    u2_regular_physical_resolvent_compactTest_approximation hd ω lam Λ hΛ hω φ hφ hc
  refine ⟨C, hC, ?_⟩
  intro α hα u hu heq
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |α * u x - φ x| ≤ C / α := by
    filter_upwards [heq, hbound α hα] with x hx hb
    simpa only [hx] using hb
  have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hclosed : IsClosed {x : Vec d | |α * u x - φ x| ≤ C / α} :=
    isClosed_le (((continuous_const.mul hu).sub hφ.continuous).abs) continuous_const
  have hfull : {x : Vec d | |α * u x - φ x| ≤ C / α} = Set.univ :=
    (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
  intro x
  have : x ∈ {x : Vec d | |α * u x - φ x| ≤ C / α} := by
    rw [hfull]
    exact Set.mem_univ x
  exact this


/-- Scaled physical resolvents approximate smooth compactly supported C₀ inputs. -/
theorem u2_regular_c0_resolvent_compactTest_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f : Vec d → ℝ))
    (hc : HasCompactSupport (f : Vec d → ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α),
      ‖α • u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f - f‖ ≤ C / α := by
  obtain ⟨C, hC, hbound⟩ := u2_regular_physical_resolvent_compactTest_pointwise_approximation
    hd ω lam Λ hΛ hω (f : Vec d → ℝ) hf hc
  refine ⟨C, hC, ?_⟩
  intro α hα
  let u := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f
  have hu := u2_regular_c0_resolvent_ae hd ω lam Λ hΛ hω α hα f hc
    (gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam (f : Vec d → ℝ) hf hc))
    (gmpPhysicalH1Value_compactTest hd ω lam Λ hω (f : Vec d → ℝ) hf hc)
  have hp := hbound α hα u u.continuous hu
  change ‖(α • u - f).toBCF‖ ≤ C / α
  apply (BoundedContinuousFunction.norm_le (div_nonneg hC.le hα.le)).2
  intro x
  change ‖α * u x - f x‖ ≤ C / α
  simpa only [Real.norm_eq_abs] using hp x


/-- Scaled physical C₀ resolvents approximate every C₀ function uniformly. -/
theorem u2_regular_c0_resolvent_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (α : ℝ) (hα : 0 < α), A < α →
      ‖α • u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f - f‖ < ε := by
  obtain ⟨g, hg, hgs, hgc⟩ := Metric.dense_iff.mp (gmpC0_smoothCompact_dense d)
    f (ε / 4) (by positivity)
  change dist g f < ε / 4 at hg
  have hdist : ‖f - g‖ < ε / 4 := by simpa [dist_eq_norm, norm_sub_rev] using hg
  obtain ⟨C, hC, hbound⟩ := u2_regular_c0_resolvent_compactTest_approximation
    hd ω lam Λ hΛ hω g hgs hgc
  refine ⟨max 1 (4 * C / ε), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α hα hlarge
  have hCα : C / α < ε / 4 := by
    have h : 4 * C / ε < α := lt_of_le_of_lt (le_max_right _ _) hlarge
    have h' : 4 * C < α * ε := (div_lt_iff₀ hε).mp h
    apply (div_lt_iff₀ hα).2
    nlinarith
  let U := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  have hU : ‖α • U (f - g)‖ ≤ ‖f - g‖ := by
    calc
      ‖α • U (f - g)‖ = α * ‖U (f - g)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
      _ ≤ α * (α⁻¹ * ‖f - g‖) := by
        gcongr
        exact (U.le_opNorm (f - g)).trans (mul_le_mul_of_nonneg_right
          (u2RegularC0Resolvent_norm_le hd ω lam Λ hΛ hω α hα) (norm_nonneg _))
      _ = ‖f - g‖ := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
  have heq : α • U f - f = α • U (f - g) + (α • U g - g) + (g - f) := by
    rw [map_sub, smul_sub]
    abel
  rw [heq]
  have ht := norm_add_le (α • U (f - g) + (α • U g - g)) (g - f)
  have ht' := norm_add_le (α • U (f - g)) (α • U g - g)
  have hb := hbound α hα
  rw [norm_sub_rev] at ht
  linarith

/-- The union of the physical C₀ resolvent ranges is dense. -/
theorem u2_regular_c0_resolvent_ranges_dense {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    :
    Dense {u : ZeroAtInftyContinuousMap (Vec d) ℝ |
      ∃ (α : ℝ) (hα : 0 < α) (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u = u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f} := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨A, hA, happrox⟩ := u2_regular_c0_resolvent_approximation
    hd ω lam Λ hΛ hω f ε hε
  let α := A + 1
  have hα : 0 < α := by dsimp [α]; linarith
  have hAα : A < α := by dsimp [α]; linarith
  refine ⟨α • u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f, ?_, ?_⟩
  · change dist (α • u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f) f < ε
    simpa [dist_eq_norm] using happrox α hα hAα
  · refine ⟨α, hα, α • f, ?_⟩
    exact (map_smul _ _ _).symm

/-- The physical C₀ resolvent approximates the identity along positive parameters. -/
theorem u2_regular_c0_resolvent_approx_identity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    Filter.Tendsto
      (fun α : {a : ℝ // 0 < a} => (α : ℝ) •
        u2RegularC0Resolvent hd ω lam Λ hΛ hω α α.property f)
      Filter.atTop (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, hA, hbound⟩ := u2_regular_c0_resolvent_approximation
    hd ω lam Λ hΛ hω f ε hε
  let B : {a : ℝ // 0 < a} := ⟨A + 1, by linarith⟩
  filter_upwards [eventually_ge_atTop B] with α hα
  have hlarge : A < (α : ℝ) := by
    have h : (B : ℝ) ≤ α := hα
    dsimp [B] at h
    linarith
  simpa only [dist_eq_norm] using hbound α α.property hlarge


/-- Each actual physical C₀ resolvent has dense range. -/
theorem u2_regular_c0_resolvent_denseRange {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (β : ℝ) (hβ : 0 < β) :
    DenseRange (u2RegularC0Resolvent hd ω lam Λ hΛ hω β hβ) := by
  let V := u2RegularC0Resolvent hd ω lam Λ hΛ hω β hβ
  apply (u2_regular_c0_resolvent_ranges_dense hd ω lam Λ hΛ hω).mono
  intro u hu
  obtain ⟨α, hα, f, rfl⟩ := hu
  let U := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  refine ⟨f + (β - α) • U f, ?_⟩
  have hi := u2_regular_c0_resolvent_identity hd ω lam Λ hΛ hω β α hβ hα f
  change V f - U f = (α - β) • V (U f) at hi
  have hs : (α - β) • V (U f) = -((β - α) • V (U f)) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hs] at hi
  change V (f + (β - α) • U f) = U f
  rw [map_add, map_smul]
  calc
    V f + (β - α) • V (U f) = (V f - U f) + (β - α) • V (U f) + U f := by abel
    _ = U f := by rw [hi]; abel

open MarkovProcess.Semigroup

/-- The actual regular-field physical C₀ resolvents form a contractive family. -/
def u2RegularC0ContractiveResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ContractiveResolvent (ZeroAtInftyContinuousMap (Vec d) ℝ) where
  operator α := u2RegularC0Resolvent hd ω lam Λ hΛ hω α α.property
  resolvent_identity α β := by
    apply ContinuousLinearMap.ext
    intro f
    exact u2_regular_c0_resolvent_identity hd ω lam Λ hΛ hω
      α β α.property β.property f
  opNorm_le_inv α := u2RegularC0Resolvent_norm_le hd ω lam Λ hΛ hω α α.property
  denseRange α := u2_regular_c0_resolvent_denseRange hd ω lam Λ hΛ hω α α.property

/-- The C₀ evolution generated by the regular-field physical resolvent. -/
def u2RegularC0Semigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    StronglyContinuousContractionSemigroup (ZeroAtInftyContinuousMap (Vec d) ℝ) :=
  (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).generatedSemigroup

/-- The generated C₀ evolution retains the actual physical resolvent. -/
theorem u2_regular_c0_semigroup_resolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : PositiveShift) :
    (u2RegularC0Semigroup hd ω lam Λ hΛ hω).resolvent α =
      u2RegularC0Resolvent hd ω lam Λ hΛ hω α α.property :=
  (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).resolvent_generatedSemigroup α

/-- The physical C₀ resolvent preserves pointwise nonnegativity. -/
theorem u2_regular_c0_resolvent_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f x := by
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα
  have hcompact (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
      (hg : HasCompactSupport (g : Vec d → ℝ)) (hgp : ∀ x, 0 ≤ g x) :
      ∀ x, 0 ≤ R g x := by
    have hm := gmpPhysical_compactContinuous_memLp hd ω lam (g : Vec d → ℝ) g.continuous hg
    let G := hm.toLp (g : Vec d → ℝ)
    have hG : (G : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g := hm.coeFn_toLp
    have hp : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] G := by
      filter_upwards [hG] with x hx
      simpa only [hx, Pi.zero_apply] using hgp x
    have he := u2_regular_c0_resolvent_ae_of_memLp hd ω lam Λ hΛ hω α hα g G hG
    have hpos := gmpPhysicalResolvent_positive hd ω lam Λ hΛ hω α hα hp
    have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ R g x := by
      filter_upwards [he, hpos] with x hx hxpos
      change R g x = _ at hx
      rw [hx]
      exact hxpos
    have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
    have hc : IsClosed {x : Vec d | 0 ≤ R g x} :=
      isClosed_le continuous_const (R g).continuous
    have hfull : {x : Vec d | 0 ≤ R g x} = Set.univ :=
      (hc.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
    intro x
    have hx : x ∈ {x : Vec d | 0 ≤ R g x} := by rw [hfull]; exact Set.mem_univ x
    exact hx
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose g hgc hgb hgK hga using fun n : ℕ =>
    gmpC0_exists_bounded_compact_cutoff f ∅ isCompact_empty (hε n)
  let fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ := fun n => f * g n
  have hb (n : ℕ) : ‖fn n - f‖ ≤ ε n := by
    change ‖(fn n - f).toBCF‖ ≤ ε n
    apply (BoundedContinuousFunction.norm_le (le_of_lt (hε n))).2
    intro x
    change ‖(f * g n) x - f x‖ ≤ ε n
    simpa only [Real.norm_eq_abs] using hga n x
  have hconv : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb hεlim
  intro x
  have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
    (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hlim : Tendsto (fun n => R (fn n) x) atTop (𝓝 (R f x)) :=
    (heval.tendsto (R f)).comp (R.continuous.tendsto f |>.comp hconv)
  apply ge_of_tendsto' hlim
  intro n
  apply hcompact (fn n) (HasCompactSupport.mul_left (hgc n))
  intro y
  change 0 ≤ f y * g n y
  exact mul_nonneg (hf y) (hgb n y).1

/-- The physical C₀ evolution preserves pointwise nonnegativity. -/
theorem u2_regular_c0_semigroup_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ (u2RegularC0Semigroup hd ω lam Λ hΛ hω) t f x := by
  let R := u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω
  let C : Set (ZeroAtInftyContinuousMap (Vec d) ℝ) := {f | ∀ x, 0 ≤ f x}
  have hc : IsClosed C := by
    have heq : C = ⋂ x : Vec d, {f : ZeroAtInftyContinuousMap (Vec d) ℝ | 0 ≤ f x} := by
      ext u
      simp only [C, Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const
      ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab x
    change 0 ≤ a * u x + b * v x
    exact add_nonneg (mul_nonneg ha (hu x)) (mul_nonneg hb (hv x))
  have hz : (0 : ZeroAtInftyContinuousMap (Vec d) ℝ) ∈ C := by
    intro x
    exact le_rfl
  have hQ (α : PositiveShift) : PreservesSet (R.scaledOperator α) C C := by
    intro u hu x
    change 0 ≤ (α : ℝ) * u2RegularC0Resolvent hd ω lam Λ hΛ hω α α.property u x
    exact mul_nonneg α.property.le
      (u2_regular_c0_resolvent_positive hd ω lam Λ hΛ hω α α.property u hu x)
  exact R.preservesSet_generatedSemigroup_of_scaledOperator C hc hv hz hQ t hf

/-- The physical C₀ resolvent is a positive contractive resolvent. -/
def u2RegularPositiveC0Resolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    :
    MarkovProcess.PositiveC0ContractiveResolvent (Vec d) where
  toContractiveResolvent := u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω
  isPositive α f hf :=
    u2_regular_c0_resolvent_positive hd ω lam Λ hΛ hω α α.property f hf

/-- The spatial sub-Markov kernels represented by the physical C₀ evolution. -/
def u2RegularC0KernelSemigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    : MarkovProcess.SubMarkovKernelSemigroup (Vec d) :=
  (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).kernelSemigroup

/-- The physical spatial kernels represent the generated C₀ evolution. -/
theorem u2RegularC0KernelSemigroup_integral {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (x : Vec d) :
    ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) =
      u2RegularC0Semigroup hd ω lam Λ hΛ hω t f x :=
  (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).integral_kernelSemigroup t f x

/-- The physical spatial kernels satisfy the Feller interface. -/
theorem u2RegularC0KernelSemigroup_isFeller {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    :
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).IsFellerKernelSemigroup :=
  (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).isFellerKernelSemigroup_kernelSemigroup

/-- The Feller semigroup recovered from the physical kernels is the original C₀ evolution. -/
theorem u2RegularC0KernelSemigroup_c0Semigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    :
    (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω).c0Semigroup =
      u2RegularC0Semigroup hd ω lam Λ hΛ hω :=
  (u2RegularPositiveC0Resolvent hd ω lam Λ hΛ hω).c0Semigroup_kernelSemigroup


/-- The bounded Yosida generators agree on common C₀ and weighted L² inputs. -/
theorem u2_regular_yosidaGenerator_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : PositiveShift)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α F :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α f := by
  have hr := (u2_regular_c0_resolvent_ae_of_memLp hd ω lam Λ hΛ hω
    α α.property f F hae).symm
  filter_upwards [hae, hr,
    Lp.coeFn_smul (α : ℝ) (gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F),
    Lp.coeFn_sub ((α : ℝ) • gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F) F,
    Lp.coeFn_smul (α : ℝ) (((α : ℝ) •
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F) - F)] with x hf hr hs hdif ho
  change (((α : ℝ) • (((α : ℝ) •
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F) - F) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x) = _
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at ho hdif hs
  rw [ho, hdif, hs]
  change (α : ℝ) * ((α : ℝ) * _ - _) = (α : ℝ) * ((α : ℝ) * _ - _)
  rw [hr, hf]
  rfl

/-- All powers of the bounded Yosida generators agree on common inputs. -/
theorem u2_regular_yosidaGenerator_pow_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : PositiveShift)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) (n : ℕ) :
    (((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α ^ n) F :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      ((u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α ^ n) f := by
  induction n with
  | zero => simpa using hae
  | succ n ih =>
      simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
        u2_regular_yosidaGenerator_ae hd ω lam Λ hΛ hω α _ _ ih

/-- The bounded Yosida semigroups agree on common C₀ and weighted L² inputs. -/
theorem u2_regular_yosidaSemigroup_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : PositiveShift) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaSemigroup α t F :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).yosidaSemigroup α t f := by
  let A := (t : ℝ) • (gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α
  let a := (t : ℝ) • (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α
  have hp (n : ℕ) : ((A ^ n) F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (a ^ n) f := by
    induction n with
    | zero => simpa using hae
    | succ n ih =>
      have h := u2_regular_yosidaGenerator_ae hd ω lam Λ hΛ hω α _ _ ih
      filter_upwards [h, Lp.coeFn_smul (t : ℝ)
        ((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α ((A ^ n) F))] with x hx hs
      simp only [pow_succ', ContinuousLinearMap.mul_apply, A, a,
        ContinuousLinearMap.smul_apply] at hs ⊢
      simp only [Pi.smul_apply, smul_eq_mul] at hs
      rw [hs]
      change (t : ℝ) * _ = (t : ℝ) * _
      rw [hx]
      rfl
  let u (n : ℕ) := ((n.factorial : ℝ)⁻¹) • (A ^ n) F
  let v (n : ℕ) := ((n.factorial : ℝ)⁻¹) • (a ^ n) f
  have huv (n : ℕ) : (u n : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] v n := by
    filter_upwards [hp n, Lp.coeFn_smul ((n.factorial : ℝ)⁻¹) ((A ^ n) F)] with x hx hs
    change (((n.factorial : ℝ)⁻¹) • (A ^ n) F : Lp ℝ 2 _) x = _
    rw [hs]
    change ((n.factorial : ℝ)⁻¹) * _ = ((n.factorial : ℝ)⁻¹) * _
    rw [hx]
    rfl
  have hsum (n : ℕ) : ((∑ k ∈ Finset.range n, u k : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] ((∑ k ∈ Finset.range n, v k : ZeroAtInftyContinuousMap (Vec d) ℝ) : Vec d → ℝ) := by
    induction n with
    | zero => simpa using Lp.coeFn_zero ℝ 2 (physicalReversibleMeasure ω hd lam)
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      filter_upwards [ih, huv n, Lp.coeFn_add (∑ k ∈ Finset.range n, u k) (u n)] with x hx hy hz
      simp only [Pi.add_apply] at hz
      rw [hz]
      change (∑ k ∈ Finset.range n, u k : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x + u n x =
        (∑ k ∈ Finset.range n, v k : ZeroAtInftyContinuousMap (Vec d) ℝ) x + v n x
      rw [hx, hy]
  have hL := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (ContinuousLinearMap.apply ℝ _ F) (ContinuousLinearMap.continuous _)
  have hC := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map
    (ContinuousLinearMap.apply ℝ _ f) (ContinuousLinearMap.continuous _)
  apply gmpPhysicalC0L2_ae_of_limits hd ω lam
    (fun n => ∑ k ∈ Finset.range n, v k) (fun n => ∑ k ∈ Finset.range n, u k) _ _ hsum
  · simpa [v, a, ContractiveResolvent.yosidaSemigroup_apply, ContractiveResolvent.yosidaOperator] using! hC.tendsto_sum_nat
  · simpa [u, A, ContractiveResolvent.yosidaSemigroup_apply, ContractiveResolvent.yosidaOperator] using! hL.tendsto_sum_nat

/-- The physical C₀ and weighted L² evolutions agree on common inputs. -/
theorem u2_regular_semigroup_ae_of_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t F : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] (u2RegularC0Semigroup hd ω lam Λ hΛ hω) t f := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let r := u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω
  apply gmpPhysicalC0L2_ae_of_limits hd ω lam
    (fun n => r.yosidaSemigroup (naturalShift n) t f)
    (fun n => R.yosidaSemigroup (naturalShift n) t F) _ _
  · intro n
    exact u2_regular_yosidaSemigroup_ae hd ω lam Λ hΛ hω (naturalShift n) t f F hae
  · exact r.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t f
  · exact R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t F

/-- The physical spatial kernels represent the weighted L² evolution on common inputs. -/
theorem u2RegularC0KernelSemigroup_integral_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) =
        (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t F x := by
  filter_upwards [u2_regular_semigroup_ae_of_memLp hd ω lam Λ hΛ hω t f F hae] with x hx
  exact (u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f x).trans hx.symm


/-- Symmetry of the actual spatial kernel against compact continuous tests. -/
theorem u2_regular_kernel_compact_symmetry {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f g : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x, (∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) * g x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, f x * (∫ y, g y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ∂physicalReversibleMeasure ω hd lam := by
  let F := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f
  let G := (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hg hgc).toLp g
  have hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).coeFn_toLp
  have hG : (G : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g :=
    (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hg hgc).coeFn_toLp
  have hPF := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t
    (Blueprint.gmpPhysicalCompactC0 f hf hfc) F hF
  have hPG := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t
    (Blueprint.gmpPhysicalCompactC0 g hg hgc) G hG
  change (fun x => ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) =ᵐ[_] _ at hPF
  change (fun x => ∫ y, g y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) =ᵐ[_] _ at hPG
  have hs := Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω t F G
  rw [L2.inner_def, L2.inner_def] at hs
  dsimp [F, G] at *
  calc
    _ = ∫ x, inner ℝ (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t F x) (G x) ∂physicalReversibleMeasure ω hd lam := by
      apply integral_congr_ae
      filter_upwards [hPF, hG] with x h1 h2
      simp only [RCLike.inner_apply', conj_trivial, F, G, ← h1, h2]
    _ = ∫ x, inner ℝ (F x) (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t G x) ∂physicalReversibleMeasure ω hd lam := hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hPG, hF] with x h1 h2
      simp only [RCLike.inner_apply', conj_trivial, F, G, ← h1, h2]


/-- A uniform bound on the bounded Yosida generators controls displacement
under the generated contraction semigroup. -/
theorem u2_generatedSemigroup_displacement_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ContractiveResolvent E) (f : E) (B : ℝ)
    (hB : ∀ α : PositiveShift, ‖R.yosidaGenerator α f‖ ≤ B) (t : ℝ≥0) :
    ‖R.generatedSemigroup t f - f‖ ≤ (t : ℝ) * B := by
  refine le_of_tendsto
    ((R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t f).sub
      tendsto_const_nhds).norm ?_
  exact Eventually.of_forall fun n => by
    have hcontract : ∀ s ∈ Set.Icc (0 : ℝ) (t : ℝ),
        ‖NormedSpace.exp (s • R.yosidaGenerator (naturalShift n))‖ ≤ 1 := by
      intro s hs
      have h := R.norm_yosidaOperator_le_one (naturalShift n) ⟨s, hs.1⟩
      simp only [ContractiveResolvent.yosidaOperator] at h
      exact h
    have h := (norm_exp_apply_sub_le (R.yosidaGenerator (naturalShift n))
      (NNReal.coe_nonneg t) hcontract f).trans
        (mul_le_mul_of_nonneg_left (hB (naturalShift n)) (NNReal.coe_nonneg t))
    simpa only [ContractiveResolvent.yosidaSemigroup_apply,
      ContractiveResolvent.yosidaOperator] using h

/-- A scaled-resolvent error bound yields the same time-linear bound for
semigroup displacement. -/
theorem u2_generatedSemigroup_displacement_of_resolvent_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : ContractiveResolvent E) (f : E) (B : ℝ)
    (hB : ∀ α : PositiveShift,
      ‖(α : ℝ) • R.operator α f - f‖ ≤ B / (α : ℝ)) (t : ℝ≥0) :
    ‖R.generatedSemigroup t f - f‖ ≤ (t : ℝ) * B := by
  apply u2_generatedSemigroup_displacement_le R f B
  intro α
  change ‖(α : ℝ) • ((α : ℝ) • R.operator α f - f)‖ ≤ B
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos α.property]
  calc
    (α : ℝ) * ‖(α : ℝ) • R.operator α f - f‖ ≤
        (α : ℝ) * (B / (α : ℝ)) := mul_le_mul_of_nonneg_left (hB α) α.property.le
    _ = B := by field_simp [ne_of_gt (show 0 < (α : ℝ) from α.property)]

/-- A smooth compact input moves at most linearly in time under the regular
physical C₀ semigroup. -/
theorem u2_regular_c0_semigroup_compactTest_displacement {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f : Vec d → ℝ))
    (hc : HasCompactSupport (f : Vec d → ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ≥0,
      ‖u2RegularC0Semigroup hd ω lam Λ hΛ hω t f - f‖ ≤ (t : ℝ) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    u2_regular_c0_resolvent_compactTest_approximation hd ω lam Λ hΛ hω f hf hc
  refine ⟨C, hC, fun t => ?_⟩
  apply u2_generatedSemigroup_displacement_of_resolvent_bound
    (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω) f C
  intro α
  exact hbound α α.property

/-- A bound on the actual compact-test generator controls the scaled physical
resolvent error with the same constant. -/
theorem u2_regular_c0_resolvent_compactTest_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f : Vec d → ℝ))
    (hc : HasCompactSupport (f : Vec d → ℝ))
    (B : ℝ) (hB : 0 < B)
    (hgen : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |physicalGenerator (firstCoordinateIndex hd) ω lam f x| ≤ B)
    (α : ℝ) (hα : 0 < α) :
    ‖α • u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f - f‖ ≤ B / α := by
  let u := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam f hf hc)
  let g := sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |g x| ≤ B := by
    filter_upwards [hgen, (sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc).coeFn_toLp] with x hb hx
    change g x = physicalGenerator (firstCoordinateIndex hd) ω lam f x at hx
    rw [hx]
    exact hb
  have hb := gmpPhysicalResolvent_abs_le hd ω lam Λ hΛ hω α hα hB hg
  have hid : α • G u - u = G g :=
    u2_regular_physical_resolvent_compactTest_sub hd ω lam Λ hΛ hω α hα f hf hc
  have hid' : (α • G u - u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =ᵐ[
      physicalReversibleMeasure ω hd lam] G g := Filter.EventuallyEq.of_eq
    (congrArg (fun z : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => (z : Vec d → ℝ)) hid)
  let v := u2RegularC0Resolvent hd ω lam Λ hΛ hω α hα f
  have hv := u2_regular_c0_resolvent_ae hd ω lam Λ hΛ hω α hα f hc u
    (gmpPhysicalH1Value_compactTest hd ω lam Λ hω f hf hc)
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |α * v x - f x| ≤ B / α := by
    filter_upwards [hb, hid', Lp.coeFn_sub (α • G u) u, Lp.coeFn_smul α (G u),
      gmpPhysicalCompactTest_value_ae hd ω lam Λ hω f hf hc, hv] with x hx he hs hm hu hvx
    change |G g x| ≤ B / α at hx
    change (α • G u - u) x = G g x at he
    rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu] at he
    change v x = G u x at hvx
    rw [hvx, he]
    exact hx
  have hvol := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hclosed : IsClosed {x : Vec d | |α * v x - f x| ≤ B / α} :=
    isClosed_le (((continuous_const.mul v.continuous).sub f.continuous).abs) continuous_const
  have hfull : {x : Vec d | |α * v x - f x| ≤ B / α} = Set.univ :=
    (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hvol)
  change ‖(α • v - f).toBCF‖ ≤ B / α
  apply (BoundedContinuousFunction.norm_le (div_nonneg hB.le hα.le)).2
  intro x
  change ‖α * v x - f x‖ ≤ B / α
  have hx : x ∈ {x : Vec d | |α * v x - f x| ≤ B / α} := by
    rw [hfull]
    exact Set.mem_univ x
  change |α * v x - f x| ≤ B / α at hx
  simpa only [Real.norm_eq_abs] using hx

/-- Generator bounds give time-linear displacement for compact tests, without
requiring the generator to have a continuous representative. -/
theorem u2_regular_c0_semigroup_compactTest_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f : Vec d → ℝ))
    (hc : HasCompactSupport (f : Vec d → ℝ))
    (B : ℝ) (hB : 0 < B)
    (hgen : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |physicalGenerator (firstCoordinateIndex hd) ω lam f x| ≤ B)
    (t : ℝ≥0) :
    ‖u2RegularC0Semigroup hd ω lam Λ hΛ hω t f - f‖ ≤ (t : ℝ) * B := by
  apply u2_generatedSemigroup_displacement_of_resolvent_bound
    (u2RegularC0ContractiveResolvent hd ω lam Λ hΛ hω) f B
  intro α
  exact u2_regular_c0_resolvent_compactTest_bound hd ω lam Λ hΛ hω f hf hc B hB hgen α α.property

/-- Smooth cutoffs with vanishing bounds on their actual regular-field
generators exclude loss of mass from the physical kernel. -/
theorem u2_regular_kernel_conservative_of_cutoffs {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (χ : ℕ → Vec d → ℝ) (B : ℕ → ℝ)
    (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n))
    (hc : ∀ n, HasCompactSupport (χ n))
    (hle : ∀ n x, χ n x ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hB : ∀ n, 0 < B n) (hBlim : Tendsto B atTop (𝓝 0))
    (hgen : ∀ n, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |physicalGenerator (firstCoordinateIndex hd) ω lam (χ n) x| ≤ B n) :
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).IsConservative := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  intro t x
  let : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hmass : P t x Set.univ ≤ 1 := P.measure_univ_le_one t x
  have hleMass (n : ℕ) : (∫ y, χ n y ∂(P t x)) ≤ (P t x).real Set.univ := by
    have hi : Integrable (χ n) (P t x) := (hs n).continuous.integrable_of_hasCompactSupport (hc n)
    have h := integral_mono hi (integrable_const (1 : ℝ)) (fun y => hle n y)
    simpa using h
  have hbound (n : ℕ) : χ n x ≤ (P t x).real Set.univ + (t : ℝ) * B n := by
    let f : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨χ n, (hs n).continuous⟩, (hc n).is_zero_at_infty⟩
    let v := u2RegularC0Semigroup hd ω lam Λ hΛ hω t f - f
    have hv : ‖v x‖ ≤ ‖v‖ := by
      simpa using BoundedContinuousFunction.norm_coe_le_norm v.toBCF x
    have hn := u2_regular_c0_semigroup_compactTest_generator_bound hd ω lam Λ hΛ hω
      f (hs n) (hc n) (B n) (hB n) (hgen n) t
    have hi := u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f x
    change (∫ y, χ n y ∂P t x) = _ at hi
    have hp : |(∫ y, χ n y ∂P t x) - χ n x| ≤ (t : ℝ) * B n := by
      rw [hi]
      change |v x| ≤ _
      simpa only [Real.norm_eq_abs] using hv.trans hn
    linarith [(abs_le.mp hp).1, hleMass n]
  have hlower : 1 ≤ (P t x).real Set.univ := by
    have ht : Tendsto (fun n : ℕ => (P t x).real Set.univ + (t : ℝ) * B n) atTop
        (𝓝 ((P t x).real Set.univ + (t : ℝ) * 0)) :=
      tendsto_const_nhds.add (hBlim.const_mul (t : ℝ))
    have hh := le_of_tendsto_of_tendsto (hlim x) ht (Filter.Eventually.of_forall hbound)
    simpa using hh
  have hr : (1 : ℝ) ≤ (P t x Set.univ).toReal := hlower
  apply le_antisymm hmass
  exact (ENNReal.toReal_le_toReal (by simp) (ne_of_lt (lt_of_le_of_lt hmass (by simp)))).mp (by simpa using hr)

/-- For a regular field, the physical divergence generator agrees with its
second-order expression almost everywhere, simultaneously for all C² tests. -/
theorem u2_regular_physical_generator_ae_textbook {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ (f : Vec d → ℝ), ContDiff ℝ 2 f →
      physicalGenerator (firstCoordinateIndex hd) ω lam f x =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω (firstCoordinateIndex hd) lam) f x := by
  filter_upwards [c16_reduced_generator_ae_textbook (by linarith : 0 < Λ) hω] with x hx
  intro f hf
  rw [physicalGenerator_eq_inv_mul, hx (firstCoordinateIndex hd) lam f hf]
  have e : (⇑ω.1 : Vec d → Mat d) =
      fun y => (clockDensity ω y)⁻¹ • reducedCoefficient ω y := by
    funext y
    rw [reducedCoefficient, inv_smul_smul₀ (clockDensity_pos ω y).ne']
  rw [e]
  exact (svGenerator_smul (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω)
    (firstCoordinateIndex hd) lam) (fun y => (clockDensity ω y)⁻¹) f x).symm

/-- First and second derivatives control the regular generator at almost every point. -/
theorem u2_regular_generator_ae_bound_of_pointwise_derivatives {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ (φ : Vec d → ℝ), ContDiff ℝ 2 φ →
      ∀ (D₁ D₂ : ℝ), 0 ≤ D₁ → 0 ≤ D₂ →
      (∀ i, |fderiv ℝ φ x (unitVector i)| ≤ D₁) →
      (∀ i j, |fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤ D₂) →
      |physicalGenerator (firstCoordinateIndex hd) ω lam φ x| ≤ C₁ * D₁ + C₂ * D₂ := by
  obtain ⟨_, _, ⟨A, hA⟩, _, _, ⟨B, hB⟩⟩ :=
    EinsteinFull.physical_svHypotheses (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (firstCoordinateIndex hd) (firstCoordinateIndex hd))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (firstCoordinateIndex hd))
  refine ⟨d * B, (d : ℝ) * d * A / 2, by positivity, by positivity, ?_⟩
  filter_upwards [u2_regular_physical_generator_ae_textbook hd ω lam Λ hΛ hω] with x hx
  intro φ hφ D₁ D₂ hD₁ hD₂ hfirst hsecond
  rw [hx φ hφ]
  unfold EinsteinFull.External.Draft.svGenerator
  have hsecondSum : |∑ i : Fin d, ∑ j : Fin d, ω.1 x i j *
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤
      (d : ℝ) * d * (A * D₂) := by
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |ω.1 x i j *
          fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A * D₂ := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul (hA x i j) (hsecond i j) (abs_nonneg _) hA0
      _ = _ := by simp; ring
  have hfirstSum : |∑ i : Fin d, EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
      fderiv ℝ φ x (unitVector i)| ≤ (d : ℝ) * (B * D₁) := by
    calc
      _ ≤ ∑ i : Fin d, |EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
          fderiv ℝ φ x (unitVector i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, B * D₁ := by
        apply Finset.sum_le_sum; intro i _; rw [abs_mul]
        exact mul_le_mul (hB x i) (hfirst i) (abs_nonneg _) hB0
      _ = _ := by simp
  calc
    _ ≤ |(1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, ω.1 x i j *
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i))| +
      |∑ i : Fin d, EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
      fderiv ℝ φ x (unitVector i)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ((d : ℝ) * d * (A * D₂)) + d * (B * D₁) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hsecondSum (by norm_num)) hfirstSum
    _ = _ := by ring

/-- Dilated compact tests have regular-generator bounds that vanish with scale. -/
theorem u2_regular_scaledTest_generator_ae_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => φ (a • y)) x| ≤ C * a := by
  obtain ⟨B, hB, hfirst, hsecond⟩ := gmpPhysical_compactTest_derivative_bounds φ hφ hc
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨(C₁ + C₂) * B, mul_nonneg (add_nonneg hC₁ hC₂) hB, ?_⟩
  intro a ha ha1
  filter_upwards [(gmpPhysical_ae_iff_volume hd ω lam _).mpr hgen] with x hx
  have hs : ContDiff ℝ 2 (fun y : Vec d => φ (a • y)) :=
    (hφ.comp (contDiff_const_smul a)).of_le (by simp)
  have hf (y : Vec d) (i : Fin d) :
      |fderiv ℝ (fun z => φ (a • z)) y (unitVector i)| ≤ B * a := by
    rw [(gmpPhysical_scaledTest_derivatives φ hφ a y i i).1, abs_mul, abs_of_nonneg ha]
    nlinarith [hfirst (a • y) i]
  have hh (y : Vec d) (i j : Fin d) :
      |fderiv ℝ (fun z => fderiv ℝ (fun w => φ (a • w)) z (unitVector j)) y (unitVector i)| ≤ B * a := by
    rw [(gmpPhysical_scaledTest_derivatives φ hφ a y i j).2, abs_mul,
      abs_of_nonneg (sq_nonneg a)]
    have hsq : a ^ 2 ≤ a := by nlinarith
    have h := hsecond (a • y) i j
    calc
      a ^ 2 * |fderiv ℝ (fun z => fderiv ℝ φ z (unitVector j)) (a • y) (unitVector i)| ≤ a ^ 2 * B :=
        mul_le_mul_of_nonneg_left h (sq_nonneg a)
      _ ≤ a * B := mul_le_mul_of_nonneg_right hsq hB
      _ = B * a := by ring
  have h := hx _ hs (B * a) (B * a) (mul_nonneg hB ha) (mul_nonneg hB ha)
    (hf x) (hh x)
  convert h using 1 <;> ring

/-- Every regular physical spatial kernel is conservative. -/
theorem u2_regular_kernel_conservative {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    :
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).IsConservative := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let χ : ℕ → Vec d → ℝ := fun n x => b (a n • x)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n ≤ 1 := by
    dsimp [a]
    exact (inv_le_one₀ (by positivity)).2 (by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χ n) := b.contDiff.comp (contDiff_const_smul (a n))
  have hc (n : ℕ) : HasCompactSupport (χ n) := b.hasCompactSupport.comp_smul (ha n).ne'
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have hlim (x : Vec d) : Tendsto (fun n => χ n x) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => a n • x) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := x))
    simpa only [χ, hb0, Function.comp_def] using (b.continuous.tendsto 0).comp ht
  obtain ⟨C, hC, hbound⟩ := u2_regular_scaledTest_generator_ae_bound hd ω lam Λ hΛ hω b b.contDiff b.hasCompactSupport
  let B : ℕ → ℝ := fun n => (C + 1) * a n
  have hB (n : ℕ) : 0 < B n := by dsimp [B]; positivity
  have hBlim : Tendsto B atTop (𝓝 0) := by
    simpa [B] using hat.const_mul (C + 1)
  apply u2_regular_kernel_conservative_of_cutoffs hd ω lam Λ hΛ hω χ B hs hc
    (fun n x => b.le_one) hlim hB hBlim
  intro n
  filter_upwards [hbound (a n) (ha n).le (ha1 n)] with x hx
  change |physicalGenerator (firstCoordinateIndex hd) ω lam (χ n) x| ≤ B n
  exact hx.trans (by dsimp [B]; nlinarith [ha n])

/-- Compact absolute displacement has a uniform time-linear bound for the regular kernel. -/
theorem u2_regular_kernel_coordinateAbsCutoff_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (k : Fin d) (a : ℝ),
      0 < a → a ≤ 1 → ∀ t : ℝ≥0,
      (∫ y, gmpPhysicalCoordinateAbsCutoff x k a y ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤ C * (t : ℝ) := by
  obtain ⟨M, hM, hderiv⟩ := gmpPhysical_coordinateAbsCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  let C := C₁ * M + C₂ * M + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC.le, ?_⟩
  intro x k a ha ha1 t
  let ψ := gmpPhysicalCoordinateAbsCutoff x k a
  have hp := gmpPhysical_coordinateAbsCutoff_properties x k a ha
  let f := gmpPhysicalCompactC0 ψ hp.1.continuous hp.2.1
  have hgen : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam,
      |physicalGenerator (firstCoordinateIndex hd) ω lam f y| ≤ C := by
    filter_upwards [(gmpPhysical_ae_iff_volume hd ω lam _).mpr hg] with y hy
    have hs : ContDiff ℝ 2 ψ := hp.1.of_le (by simp)
    have h := hy ψ hs M M hM hM (fun i => (hderiv x y k i i a ha ha1).1)
      (fun i j => (hderiv x y k i j a ha ha1).2)
    change |physicalGenerator (firstCoordinateIndex hd) ω lam ψ y| ≤ C
    exact h.trans (by dsimp [C]; linarith)
  have hn := u2_regular_c0_semigroup_compactTest_generator_bound hd ω lam Λ hΛ hω
    f hp.1 hp.2.1 C hC hgen t
  have hv := BoundedContinuousFunction.norm_coe_le_norm
    (u2RegularC0Semigroup hd ω lam Λ hΛ hω t f - f).toBCF x
  have hi := u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f x
  have hz : ψ x = 0 := by simp [ψ, gmpPhysicalCoordinateAbsCutoff]
  change (∫ y, ψ y ∂_) = _ at hi
  change ‖u2RegularC0Semigroup hd ω lam Λ hΛ hω t f x - ψ x‖ ≤ _ at hv
  rw [hz, sub_zero, ← hi, Real.norm_eq_abs] at hv
  exact (le_abs_self _).trans (hv.trans (hn.trans_eq (mul_comm _ _)))

/-- Fatou yields the regular kernel's smooth absolute displacement bound. -/
theorem u2_regular_kernel_smoothAbs_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (∫⁻ y, ENNReal.ofReal (Real.sqrt (1 + (y k - x k) ^ 2) - 1) ∂
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
          ENNReal.ofReal (C * (t : ℝ)) := by
  obtain ⟨C, hC, hcut⟩ := u2_regular_kernel_coordinateAbsCutoff_le hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro x k t
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateAbsCutoff x k (((m : ℝ) + 1)⁻¹) y) ∂μ) ≤
        ENNReal.ofReal (C * (t : ℝ)) := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hp := gmpPhysical_coordinateAbsCutoff_properties x k a ha
    have hi : Integrable (gmpPhysicalCoordinateAbsCutoff x k a) μ :=
      hp.1.continuous.integrable_of_hasCompactSupport hp.2.1
    change (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateAbsCutoff x k a y) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp.2.2.1)]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha ha1 t)
  exact (gmpPhysical_coordinateAbsCutoff_fatou x k μ).trans
    (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))

/-- The conservative regular kernel has finite first absolute coordinate moment. -/
theorem u2_regular_kernel_coordinateAbs_integrable_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => |y k - x k|)
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, |y k - x k| ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ≤
        1 + C * (t : ℝ) := by
  obtain ⟨C, hC, hfatou⟩ := u2_regular_kernel_smoothAbs_lintegral_le hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro x k t
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  letI : IsProbabilityMeasure μ := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  let g : Vec d → ℝ := fun y => Real.sqrt (1 + (y k - x k) ^ 2) - 1
  have hgcont : Continuous g := by dsimp [g]; fun_prop
  have hg0 (y : Vec d) : 0 ≤ g y := (gmpPhysical_smoothAbs_bounds (y k - x k)).1
  have hgl : (∫⁻ y, ENNReal.ofReal (g y) ∂μ) ≤ ENNReal.ofReal (C * (t : ℝ)) := hfatou x k t
  have hg : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hgcont.aestronglyMeasurable
      (ae_of_all _ hg0)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgl)
  have hgint : (∫ y, g y ∂μ) ≤ C * (t : ℝ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg0)] at hgl
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (NNReal.coe_nonneg t))).1 hgl
  have ha : Integrable (fun y => |y k - x k|) μ := by
    apply (hg.add (integrable_const 1)).mono_nonneg
      (((continuous_apply k).sub continuous_const).abs.aestronglyMeasurable)
      (ae_of_all _ (fun y => abs_nonneg _))
    exact ae_of_all _ (fun y => by
      dsimp [g]
      linarith [(gmpPhysical_smoothAbs_bounds (y k - x k)).2.2])
  refine ⟨ha, ?_⟩
  have h := integral_mono ha (hg.add (integrable_const 1)) (fun y => by
    dsimp [g]
    linarith [(gmpPhysical_smoothAbs_bounds (y k - x k)).2.2])
  change (∫ y, |y k - x k| ∂μ) ≤ ∫ y, (g y + 1) ∂μ at h
  rw [integral_add hg (integrable_const 1)] at h
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  linarith

/-- The square-cutoff generator has linear coordinate growth on one common
full-measure set, uniformly in the cutoff scale and center. -/
theorem u2_regular_coordinateSquareCutoff_generator_ae_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        ∀ (z : Vec d) (k : Fin d) (a : ℝ), 0 < a →
          |physicalGenerator (firstCoordinateIndex hd) ω lam
            (gmpPhysicalCoordinateMomentCutoff z k 1 a) x| ≤ A * |x k - z k| + B := by
  obtain ⟨D, hD, hderiv⟩ := gmpPhysical_coordinateSquareCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    u2_regular_generator_ae_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω
  refine ⟨C₁ * D, C₂ * D, mul_nonneg hC₁ hD, mul_nonneg hC₂ hD, ?_⟩
  filter_upwards [(gmpPhysical_ae_iff_volume hd ω lam _).mpr hg] with x hx
  intro z k a ha
  have hs : ContDiff ℝ 2 (gmpPhysicalCoordinateMomentCutoff z k 1 a) :=
    (gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha).1.of_le (by simp)
  have h := hx _ hs (D * |x k - z k|) D (mul_nonneg hD (abs_nonneg _)) hD
    (fun i => (hderiv z x k i i a ha).1) (fun i j => (hderiv z x k i j a ha).2)
  convert h using 1 <;> ring

/-- The regular compact-test generator has a jointly measurable transition
orbit and a uniform bound, for every real force. -/
theorem u2_regular_kernel_compactTest_generator_orbit {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ B : ℝ, 0 ≤ B ∧
      Measurable (fun p : ℝ × Vec d => ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal p.1) p.2) ∧
      ∀ (t : ℝ≥0) (x : Vec d),
        |∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤ B := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam φ
  obtain ⟨B, hB, hg⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hφ hc
  let κ : ProbabilityTheory.Kernel (ℝ≥0 × Vec d) (Vec d) :=
    ⟨fun p => P p.1 p.2, P.measurable_toMeasure⟩
  let : ProbabilityTheory.IsMarkovKernel κ := ⟨fun p =>
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω p.1 p.2⟩⟩
  have hm : Measurable g := measurable_physicalGenerator (firstCoordinateIndex hd) ω lam φ
  have hj : Measurable (fun p : ℝ≥0 × Vec d => ∫ y, g y ∂κ p) :=
    hm.stronglyMeasurable.integral_kernel.measurable
  refine ⟨B, hB, ?_, ?_⟩
  · change Measurable (fun p : ℝ × Vec d => ∫ y, g y ∂κ (Real.toNNReal p.1, p.2))
    exact hj.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  · intro t x
    change |∫ y, g y ∂κ (t, x)| ≤ B
    have hb := norm_integral_le_of_norm_le_const (μ := κ (t, x)) (f := g) (C := B)
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hg y)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb











end EinsteinFull
