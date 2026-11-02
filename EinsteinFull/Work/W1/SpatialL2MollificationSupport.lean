import EinsteinRelation.Calculus.Mollifier
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure

/-!
# Spatial L² mollification on the actual coordinate carrier

Translations here act on Lebesgue classes on `Vec d`, rather than on random
environments. The fixed, genuinely Euclidean-supported blueprint mollifier gives
contractive Bochner averages converging strongly for every scalar or vector L²
datum. Compactly supported data retain support in the prescribed open region at
small scales. These are spatial approximation ingredients, not a weak-gradient
commutation theorem or a zero-boundary H¹ identification.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace EinsteinFull
open EinsteinRelation
noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal spatial translation on Lebesgue L², including vector-valued data. -/
def spatialTranslationL2 (y : Vec d) : Lp E 2 (volume : Measure (Vec d)) →ₗᵢ[ℝ]
    Lp E 2 (volume : Measure (Vec d)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + y) (measurePreserving_add_right volume y)

theorem spatialTranslationL2_ae_eq (y : Vec d) (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialTranslationL2 y f =ᵐ[volume] fun x => f (x + y) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)

theorem spatialTranslationL2_zero (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialTranslationL2 0 f = f := by
  apply Lp.ext
  filter_upwards [spatialTranslationL2_ae_eq 0 f] with x hx
  simpa only [add_zero] using hx

theorem spatialTranslationL2_add (y z : Vec d) (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialTranslationL2 (y + z) f = spatialTranslationL2 y (spatialTranslationL2 z f) := by
  apply Lp.ext
  have h := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae
    (spatialTranslationL2_ae_eq z f)
  filter_upwards [spatialTranslationL2_ae_eq (y + z) f,
    spatialTranslationL2_ae_eq y (spatialTranslationL2 z f), h] with x ha hb hc
  rw [ha, hb, hc, add_assoc]

theorem norm_spatialTranslationL2 (y : Vec d) (f : Lp E 2 (volume : Measure (Vec d))) :
    ‖spatialTranslationL2 y f‖ = ‖f‖ := (spatialTranslationL2 y).norm_map f

/-- Joint strong continuity uses local finiteness of Lebesgue measure, without
assuming that the ambient measure is finite. -/
theorem continuous_spatialTranslationL2 :
    Continuous (fun q : Vec d × Lp E 2 (volume : Measure (Vec d)) =>
      spatialTranslationL2 q.1 q.2) := by
  let g : Vec d × Lp E 2 (volume : Measure (Vec d)) → C(Vec d, Vec d) :=
    fun q => ⟨fun x => x + q.1, continuous_id.add continuous_const⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.add continuous_fst.fst
  exact continuous_snd.compMeasurePreservingLp hg
    (fun q => measurePreserving_add_right volume q.1) (by norm_num)

theorem tendsto_spatialTranslationL2_zero (f : Lp E 2 (volume : Measure (Vec d))) :
    Tendsto (fun y : Vec d => spatialTranslationL2 y f) (𝓝 0) (𝓝 f) := by
  have h := (continuous_spatialTranslationL2.comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : Vec d => f))).tendsto 0
  have h2 : Tendsto (fun y : Vec d => spatialTranslationL2 y f) (𝓝 0)
      (𝓝 (spatialTranslationL2 0 f)) := h
  rwa [spatialTranslationL2_zero] at h2


/-- The actual spatial Bochner integrand is integrable at every real scale. -/
theorem integrable_spatialMollifier (ε : ℝ) (f : Lp E 2 (volume : Measure (Vec d))) :
    Integrable (fun y : Vec d => mollifier d y • spatialTranslationL2 (ε • y) f) := by
  have hc : Continuous (fun y : Vec d => spatialTranslationL2 (ε • y) f) :=
    continuous_spatialTranslationL2.comp
      ((continuous_id.const_smul ε).prodMk continuous_const)
  refine Integrable.mono'
    (((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const ‖f‖)
    (((contDiff_mollifier d).continuous.smul hc).aestronglyMeasurable) ?_
  exact ae_of_all _ fun y => by
    rw [norm_smul, norm_spatialTranslationL2, Real.norm_eq_abs,
      abs_of_nonneg (mollifier_nonneg d y)]

private theorem norm_spatialMollifier_integral_le (ε : ℝ)
    (f : Lp E 2 (volume : Measure (Vec d))) :
    ‖∫ y : Vec d, mollifier d y • spatialTranslationL2 (ε • y) f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ y : Vec d, ‖mollifier d y • spatialTranslationL2 (ε • y) f‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Vec d, mollifier d y * ‖f‖ := by
      congr 1
      funext y
      rw [norm_smul, norm_spatialTranslationL2, Real.norm_eq_abs,
        abs_of_nonneg (mollifier_nonneg d y)]
    _ = ‖f‖ := by rw [integral_mul_const, integral_mollifier, one_mul]

/-- Spatial averaging as a bounded operator on the actual Lebesgue L² classes.
The formula averages `f (x + ε • y)` with the fixed unit-mass smooth kernel. -/
def spatialMollifyL2 (ε : ℝ) : Lp E 2 (volume : Measure (Vec d)) →L[ℝ]
    Lp E 2 (volume : Measure (Vec d)) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ y : Vec d, mollifier d y • spatialTranslationL2 (ε • y) f
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_spatialMollifier ε f) (integrable_spatialMollifier ε g)
      map_smul' := fun c f => by
        simp only [map_smul, RingHom.id_apply, smul_comm (mollifier d _) c]
        exact integral_smul c _ }
    1 (fun f => by rw [one_mul]; exact norm_spatialMollifier_integral_le ε f)

theorem spatialMollifyL2_apply (ε : ℝ) (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialMollifyL2 ε f =
      ∫ y : Vec d, mollifier d y • spatialTranslationL2 (ε • y) f := rfl

theorem norm_spatialMollifyL2_le (ε : ℝ) (f : Lp E 2 (volume : Measure (Vec d))) :
    ‖spatialMollifyL2 ε f‖ ≤ ‖f‖ := norm_spatialMollifier_integral_le ε f

variable [CompleteSpace E]

theorem spatialMollifyL2_zero (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialMollifyL2 0 f = f := by
  simp only [spatialMollifyL2_apply, zero_smul, spatialTranslationL2_zero,
    integral_smul_const, integral_mollifier, one_smul]

/-- Strong spatial approximation for every L² datum, with no pointwise regularity premise. -/
theorem tendsto_spatialMollifyL2_zero (f : Lp E 2 (volume : Measure (Vec d))) :
    Tendsto (fun ε : ℝ => spatialMollifyL2 ε f) (𝓝 0) (𝓝 f) := by
  have hm : ∀ ε : ℝ, Continuous (fun y : Vec d =>
      mollifier d y • spatialTranslationL2 (ε • y) f) := fun ε =>
    (contDiff_mollifier d).continuous.smul
      (continuous_spatialTranslationL2.comp
        ((continuous_id.const_smul ε).prodMk continuous_const))
  have hlim : ∀ y : Vec d, Tendsto
      (fun ε : ℝ => mollifier d y • spatialTranslationL2 (ε • y) f)
      (𝓝 0) (𝓝 (mollifier d y • f)) := by
    intro y
    have hs : Tendsto (fun ε : ℝ => ε • y) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul] using (show Continuous (fun ε : ℝ => ε • y) from
        continuous_id.smul continuous_const).tendsto (0 : ℝ)
    exact ((tendsto_spatialTranslationL2_zero f).comp hs).const_smul _
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Vec d)))
    (fun y : Vec d => mollifier d y * ‖f‖)
    (Eventually.of_forall fun ε => (hm ε).aestronglyMeasurable)
    (Eventually.of_forall fun ε => ae_of_all _ fun y => by
      rw [norm_smul, norm_spatialTranslationL2, Real.norm_eq_abs,
        abs_of_nonneg (mollifier_nonneg d y)])
    (((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const ‖f‖)
    (ae_of_all _ hlim)
  simpa only [spatialMollifyL2_apply, integral_smul_const, integral_mollifier, one_smul] using h

omit [CompleteSpace E]

/-- The compact support allowed by the literal averaging formula, before any
norm comparison: all `k - ε • y` with `k ∈ K` and `y` in the fixed kernel support. -/
def spatialMollifySupport (K : Set (Vec d)) (ε : ℝ) : Set (Vec d) :=
  (fun p : Vec d × Vec d => p.1 - ε • p.2) '' (K ×ˢ tsupport (mollifier d))

/-- Compactly supported data retain compact support at each scale. -/
theorem isCompact_spatialMollifySupport {K : Set (Vec d)} (hK : IsCompact K) (ε : ℝ) :
    IsCompact (spatialMollifySupport K ε) :=
  (hK.prod (hasCompactSupport_mollifier d)).image
    (continuous_fst.sub (continuous_snd.const_smul ε))

/-- The actual L² average vanishes off the support computed from the literal
translation formula; exceptional representative sets are transported by Lebesgue translations. -/
theorem spatialMollifyL2_zero_off [CompleteSpace E] {K : Set (Vec d)} (hK : IsCompact K) (ε : ℝ)
    (f : Lp E 2 (volume : Measure (Vec d)))
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ∀ᵐ x ∂volume, x ∉ spatialMollifySupport K ε → spatialMollifyL2 ε f x = 0 := by
  let S := spatialMollifySupport K ε
  have hS : MeasurableSet S := (isCompact_spatialMollifySupport hK ε).isClosed.measurableSet
  let R := LpToLpRestrictCLM (Vec d) E ℝ volume 2 Sᶜ
  have hR : R (spatialMollifyL2 ε f) = 0 := by
    rw [spatialMollifyL2_apply, ← R.integral_comp_comm (integrable_spatialMollifier ε f)]
    apply integral_eq_zero_of_ae
    refine ae_of_all _ fun y => ?_
    change R (mollifier d y • spatialTranslationL2 (ε • y) f) =
      (0 : Lp E 2 (volume.restrict Sᶜ))
    by_cases hy : mollifier d y = 0
    · simp only [hy, zero_smul, map_zero]
    · rw [map_smul]
      suffices R (spatialTranslationL2 (ε • y) f) = 0 by rw [this, smul_zero]
      apply Lp.ext
      have hshift := (measurePreserving_add_right volume (ε • y)).quasiMeasurePreserving.ae hf
      filter_upwards [LpToLpRestrictCLM_coeFn ℝ Sᶜ (spatialTranslationL2 (ε • y) f),
        ae_restrict_of_ae (spatialTranslationL2_ae_eq (ε • y) f),
        ae_restrict_of_ae hshift, ae_restrict_mem hS.compl,
        Lp.coeFn_zero E 2 (volume.restrict Sᶜ)] with x hxR hx hxshift hxS hz
      rw [hxR, hx, hz]
      change f (x + ε • y) = 0
      apply hxshift
      intro hxK
      apply hxS
      exact ⟨(x + ε • y, y), ⟨hxK, subset_tsupport _ hy⟩,
        add_sub_cancel_right x (ε • y)⟩
  have hzero : ∀ᵐ x ∂volume.restrict Sᶜ, spatialMollifyL2 ε f x = 0 := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ Sᶜ (spatialMollifyL2 ε f),
      Lp.coeFn_zero E 2 (volume.restrict Sᶜ)] with x hx hz0
    have hz : R (spatialMollifyL2 ε f) x = 0 := by rw [hR]; exact hz0
    exact hx.symm.trans hz
  exact (ae_restrict_iff' hS.compl).mp hzero


/-- Uniformly small scales preserve support in any open neighborhood of the
original compact set, including both signs and scale zero. -/
theorem eventually_spatialMollifySupport_subset {K U : Set (Vec d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∀ᶠ ε : ℝ in 𝓝 0, spatialMollifySupport K ε ⊆ U := by
  have hc : Continuous (fun p : ℝ × (Vec d × Vec d) => p.2.1 - p.1 • p.2.2) := by
    fun_prop
  have h := (hK.prod (hasCompactSupport_mollifier d)).eventually_forall_of_forall_eventually
    (x₀ := (0 : ℝ)) (P := fun ε p => p.1 - ε • p.2 ∈ U) (fun p hp =>
      hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by
        simpa only [zero_smul, sub_zero] using hKU hp.1)))
  filter_upwards [h] with ε hε x hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact hε p hp

/-- Actual spatial approximants retain interior support at every sufficiently
small scale, for arbitrary signed scalar data and vector data alike. -/
theorem eventually_spatialMollifyL2_zero_off [CompleteSpace E] {K U : Set (Vec d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : Lp E 2 (volume : Measure (Vec d)))
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ᵐ x ∂volume, x ∉ U → spatialMollifyL2 ε f x = 0 := by
  filter_upwards [eventually_spatialMollifySupport_subset hK hU hKU] with ε hε
  filter_upwards [spatialMollifyL2_zero_off hK ε f hf] with x hx hxU
  exact hx (fun hxS => hxU (hε hxS))

/-- Spatial translation commutes with every bounded real linear value map,
including the coordinate maps on the Euclidean gradient carrier. -/
theorem spatialTranslationL2_compLpL {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (y : Vec d) (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialTranslationL2 y (A.compLpL 2 volume f) =
      A.compLpL 2 volume (spatialTranslationL2 y f) := by
  apply Lp.ext
  have hA := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae
    (A.coeFn_compLpL f)
  filter_upwards [spatialTranslationL2_ae_eq y (A.compLpL 2 volume f),
    A.coeFn_compLpL (spatialTranslationL2 y f), spatialTranslationL2_ae_eq y f, hA]
      with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₂, hx₃, hx₄]

/-- Scalar and vector averages use the same operator: bounded linear maps
commute with the actual spatial Bochner mollification. -/
theorem spatialMollifyL2_compLpL [CompleteSpace E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (ε : ℝ) (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialMollifyL2 ε (A.compLpL 2 volume f) =
      A.compLpL 2 volume (spatialMollifyL2 ε f) := by
  rw [spatialMollifyL2_apply, spatialMollifyL2_apply,
    ← (A.compLpL 2 volume).integral_comp_comm (integrable_spatialMollifier ε f)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    rw [map_smul, spatialTranslationL2_compLpL]

end
end EinsteinFull
