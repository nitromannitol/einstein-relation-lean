import EinsteinFull.Work.W1.SpatialSmoothMollificationSupport
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise representatives of spatial L² mollification

Finite-set integral tests are bounded on L². They commute with the actual
Bochner average; Fubini then identifies its representative with the literal
pointwise average. Compactly supported L² data need no extra integrability
assumption. At positive scales the genuine smooth convolution therefore has
exactly the Bochner average's L² class and strong approximation property.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace EinsteinFull
open EinsteinRelation
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integration on a finite-measure spatial set, as a bounded functional on L². -/
def spatialSetIntegralL2 {S : Set (Vec d)} (hS : MeasurableSet S)
    (hvol : volume S ≠ ∞) : Lp E 2 (volume : Measure (Vec d)) →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume 2 2 (indicatorConstLp 2 hS hvol (1 : ℝ))

theorem spatialSetIntegralL2_apply {S : Set (Vec d)} (hS : MeasurableSet S)
    (hvol : volume S ≠ ∞) (f : Lp E 2 (volume : Measure (Vec d))) :
    spatialSetIntegralL2 hS hvol f = ∫ x in S, f x := by
  rw [spatialSetIntegralL2, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    _ = ∫ x : Vec d, S.indicator f x := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hvol)
        (c := (1 : ℝ))] with x hx
      rw [ContinuousLinearMap.lsmul_apply, hx]
      by_cases h : x ∈ S <;> simp [h]
    _ = ∫ x in S, f x := integral_indicator hS

omit [CompleteSpace E] in
/-- Joint integrability of the literal averaging formula for integrable L² data. -/
theorem integrable_spatialMollifier_prod (ε : ℝ)
    (f : Lp E 2 (volume : Measure (Vec d))) (hf : Integrable f volume) :
    Integrable (fun q : Vec d × Vec d => mollifier d q.1 • f (q.2 + ε • q.1))
      (volume.prod volume) := by
  have hm : StronglyMeasurable (fun q : Vec d × Vec d =>
      mollifier d q.1 • f (q.2 + ε • q.1)) :=
    ((contDiff_mollifier d).continuous.comp continuous_fst).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable f).comp_measurable
        (continuous_snd.add (continuous_fst.const_smul ε)).measurable)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun y =>
      ((measurePreserving_add_right volume (ε • y)).integrable_comp_of_integrable hf).fun_smul
        (mollifier d y)
  · have heq (y : Vec d) : (∫ x : Vec d, ‖mollifier d y • f (x + ε • y)‖) =
        mollifier d y * ∫ x : Vec d, ‖f x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d y),
        integral_const_mul]
      rw [(measurePreserving_add_right volume (ε • y)).integral_comp
        (Homeomorph.addRight (ε • y)).measurableEmbedding (fun x => ‖f x‖)]
    simp_rw [heq]
    exact ((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const _

/-- Fubini identifies the pointwise average with the actual L² Bochner average. -/
theorem spatialMollifyL2_ae_eq_average (ε : ℝ)
    (f : Lp E 2 (volume : Measure (Vec d))) (hf : Integrable f volume) :
    spatialMollifyL2 ε f =ᵐ[volume]
      fun x => ∫ y : Vec d, mollifier d y • f (x + ε • y) := by
  have hF := integrable_spatialMollifier_prod ε f hf
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S _ hvol
    letI : IsFiniteMeasure (volume.restrict S : Measure (Vec d)) :=
      ⟨by simpa using hvol⟩
    exact ((Lp.memLp (spatialMollifyL2 ε f)).restrict S).integrable (by norm_num)
  · intro S _ _
    exact hF.integral_prod_right.integrableOn
  · intro S hS hvol
    let A := spatialSetIntegralL2 (E := E) hS hvol.ne
    have hFr : Integrable (fun q : Vec d × Vec d =>
        mollifier d q.1 • f (q.2 + ε • q.1)) (volume.prod (volume.restrict S)) := by
      have ht := hF.integrableOn (s := Set.univ ×ˢ S)
      change Integrable _ ((volume.prod volume).restrict (Set.univ ×ˢ S)) at ht
      simpa only [← Measure.prod_restrict, Measure.restrict_univ] using ht
    calc
      _ = A (spatialMollifyL2 ε f) := (spatialSetIntegralL2_apply hS hvol.ne _).symm
      _ = ∫ y : Vec d, A (mollifier d y • spatialTranslationL2 (ε • y) f) := by
        rw [spatialMollifyL2_apply, A.integral_comp_comm (integrable_spatialMollifier ε f)]
      _ = ∫ y : Vec d, ∫ x in S, mollifier d y • f (x + ε • y) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          change A (mollifier d y • spatialTranslationL2 (ε • y) f) = _
          rw [A.map_smul, spatialSetIntegralL2_apply, ← integral_smul]
          apply integral_congr_ae
          filter_upwards [(spatialTranslationL2_ae_eq (ε • y) f).restrict (s := S)] with x hx
          rw [hx]
      _ = _ := integral_integral_swap hFr

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- AE compact support makes an actual L² representative integrable. -/
theorem integrable_L2_of_ae_zero_off_compact
    (f : Lp E 2 (volume : Measure (Vec d))) {K : Set (Vec d)} (hK : IsCompact K)
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) : Integrable f volume := by
  have hi := ((Lp.memLp f).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  have heq : K.indicator f =ᵐ[volume] f := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h, hx h]
  exact ((integrable_indicator_iff hK.measurableSet).mpr hi).congr heq

/-- At positive scales, the smooth pointwise convolution represents the L² average. -/
theorem spatialSmoothMollify_ae_eq_L2 {ε : ℝ} (hε : 0 < ε)
    (f : Lp E 2 (volume : Measure (Vec d))) (hf : Integrable f volume) :
    spatialSmoothMollify ε f =ᵐ[volume] spatialMollifyL2 ε f := by
  filter_upwards [spatialMollifyL2_ae_eq_average ε f hf] with x hx
  rw [spatialSmoothMollify_eq_average hε, hx]

/-- Compactly supported L² data need no extra integrability premise. -/
theorem spatialSmoothMollify_ae_eq_L2_of_ae_zero_off_compact
    {ε : ℝ} (hε : 0 < ε) (f : Lp E 2 (volume : Measure (Vec d)))
    {K : Set (Vec d)} (hK : IsCompact K) (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    spatialSmoothMollify ε f =ᵐ[volume] spatialMollifyL2 ε f :=
  spatialSmoothMollify_ae_eq_L2 hε f (integrable_L2_of_ae_zero_off_compact f hK hf)

/-- The smooth representative belongs to the same genuine Lebesgue L² space. -/
theorem memLp_spatialSmoothMollify {ε : ℝ} (hε : 0 < ε)
    (f : Lp E 2 (volume : Measure (Vec d))) (hf : Integrable f volume) :
    MemLp (spatialSmoothMollify ε f) 2 volume :=
  (Lp.memLp (spatialMollifyL2 ε f)).ae_eq (spatialSmoothMollify_ae_eq_L2 hε f hf).symm

/-- The actual L² class of the smooth representative is the Bochner average. -/
theorem toLp_spatialSmoothMollify {ε : ℝ} (hε : 0 < ε)
    (f : Lp E 2 (volume : Measure (Vec d))) (hf : Integrable f volume) :
    (memLp_spatialSmoothMollify hε f hf).toLp (spatialSmoothMollify ε f) =
      spatialMollifyL2 ε f := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (spatialSmoothMollify_ae_eq_L2 hε f hf)

/-- Strong convergence of the literal smooth representatives in Lebesgue L². -/
theorem tendsto_toLp_spatialSmoothMollify_zero
    (f : Lp E 2 (volume : Measure (Vec d))) (hf : Integrable f volume) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      (memLp_spatialSmoothMollify ε.property f hf).toLp (spatialSmoothMollify ε f))
      (comap Subtype.val (𝓝 0)) (𝓝 f) := by
  have heq : (fun ε : {ε : ℝ // 0 < ε} =>
      (memLp_spatialSmoothMollify ε.property f hf).toLp (spatialSmoothMollify ε f)) =
      (fun ε : {ε : ℝ // 0 < ε} => spatialMollifyL2 (ε : ℝ) f) := by
    funext ε
    exact toLp_spatialSmoothMollify ε.property f hf
  rw [heq]
  exact (tendsto_spatialMollifyL2_zero f).comp tendsto_comap

/-- The classical derivative represents the mollified actual weak derivative. -/
theorem coordinateDerivative_spatialSmoothMollify_ae_eq_L2
    {ε : ℝ} (hε : 0 < ε) (f g : Lp ℝ 2 (volume : Measure (Vec d)))
    {i : Fin d} (hfg : HasWeakPartialDerivative Set.univ i f g)
    (hg : Integrable g volume) :
    coordinateDerivative i (spatialSmoothMollify ε f) =ᵐ[volume] spatialMollifyL2 ε g := by
  rw [coordinateDerivative_spatialSmoothMollify hε.ne' hfg]
  exact spatialSmoothMollify_ae_eq_L2 hε g hg

/-- The classical derivative of the smooth average is an actual L² function. -/
theorem memLp_coordinateDerivative_spatialSmoothMollify
    {ε : ℝ} (hε : 0 < ε) (f g : Lp ℝ 2 (volume : Measure (Vec d)))
    {i : Fin d} (hfg : HasWeakPartialDerivative Set.univ i f g)
    (hg : Integrable g volume) :
    MemLp (coordinateDerivative i (spatialSmoothMollify ε f)) 2 volume :=
  (Lp.memLp (spatialMollifyL2 ε g)).ae_eq
    (coordinateDerivative_spatialSmoothMollify_ae_eq_L2 hε f g hfg hg).symm

/-- Its L² class is exactly the average of the genuine weak derivative. -/
theorem toLp_coordinateDerivative_spatialSmoothMollify
    {ε : ℝ} (hε : 0 < ε) (f g : Lp ℝ 2 (volume : Measure (Vec d)))
    {i : Fin d} (hfg : HasWeakPartialDerivative Set.univ i f g)
    (hg : Integrable g volume) :
    (memLp_coordinateDerivative_spatialSmoothMollify hε f g hfg hg).toLp
      (coordinateDerivative i (spatialSmoothMollify ε f)) = spatialMollifyL2 ε g := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (coordinateDerivative_spatialSmoothMollify_ae_eq_L2 hε f g hfg hg)

/-- Strong approximation of each actual weak derivative in Lebesgue L². -/
theorem tendsto_toLp_coordinateDerivative_spatialSmoothMollify_zero
    (f g : Lp ℝ 2 (volume : Measure (Vec d)))
    {i : Fin d} (hfg : HasWeakPartialDerivative Set.univ i f g)
    (hg : Integrable g volume) :
    Tendsto (fun ε : {ε : ℝ // 0 < ε} =>
      (memLp_coordinateDerivative_spatialSmoothMollify ε.property f g hfg hg).toLp
        (coordinateDerivative i (spatialSmoothMollify ε f)))
      (comap Subtype.val (𝓝 0)) (𝓝 g) := by
  have heq : (fun ε : {ε : ℝ // 0 < ε} =>
      (memLp_coordinateDerivative_spatialSmoothMollify ε.property f g hfg hg).toLp
        (coordinateDerivative i (spatialSmoothMollify ε f))) =
      (fun ε : {ε : ℝ // 0 < ε} => spatialMollifyL2 (ε : ℝ) g) := by
    funext ε
    exact toLp_coordinateDerivative_spatialSmoothMollify ε.property f g hfg hg
  rw [heq]
  exact (tendsto_spatialMollifyL2_zero g).comp tendsto_comap

end
end EinsteinFull
