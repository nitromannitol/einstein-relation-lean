import EinsteinFull.Work.W1.SpatialL2MollificationSupport
import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Convolution

/-!
# Smooth spatial averages of locally integrable data

The pointwise averages use the same fixed Euclidean kernel and translations as
`spatialMollifyL2`. Change of variables identifies them with smooth convolutions.
Compact AE support of the datum gives literal compact support of the smooth
average. Coordinate weak derivatives commute with the actual pointwise averages.
Identification with the L²-valued Bochner integral and weighted H¹ convergence
are separate remaining steps.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology Convolution
namespace EinsteinFull
open EinsteinRelation
noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The dilated fixed spatial kernel; positive scales have mass one. -/
def spatialScaledKernel (ε : ℝ) (y : Vec d) : ℝ :=
  (ε ^ d)⁻¹ * mollifier d (ε⁻¹ • y)

theorem contDiff_spatialScaledKernel (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialScaledKernel (d := d) ε) :=
  contDiff_const.mul ((contDiff_mollifier d).comp (contDiff_const_smul ε⁻¹))

theorem hasCompactSupport_spatialScaledKernel {ε : ℝ} (hε : ε ≠ 0) :
    HasCompactSupport (spatialScaledKernel (d := d) ε) :=
  ((hasCompactSupport_mollifier d).comp_smul (inv_ne_zero hε)).mul_left

theorem spatialScaledKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (y : Vec d) :
    0 ≤ spatialScaledKernel ε y :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε d)) (mollifier_nonneg d _)

/-- Pointwise spatial smoothing, with the translation orientation `x+y`. -/
def spatialSmoothMollify (ε : ℝ) (f : Vec d → E) (x : Vec d) : E :=
  ∫ y : Vec d, spatialScaledKernel ε y • f (x + y)

/-- The literal fixed-kernel average equals the scaled-kernel pointwise average.
No regularity or representative choice is needed for this change of variables. -/
theorem spatialSmoothMollify_eq_average {ε : ℝ} (hε : 0 < ε)
    (f : Vec d → E) (x : Vec d) :
    spatialSmoothMollify ε f x = ∫ y : Vec d, mollifier d y • f (x + ε • y) := by
  have hn : ε ^ d ≠ 0 := pow_ne_zero _ hε.ne'
  have hk (y : Vec d) : spatialScaledKernel ε (ε • y) = (ε ^ d)⁻¹ * mollifier d y := by
    dsimp only [spatialScaledKernel]
    rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Vec d))
    (fun y : Vec d => spatialScaledKernel ε y • f (x + y)) ε (hR := hε.le)
  rw [Module.finrank_fin_fun] at h
  have hi : (∫ y : Vec d, spatialScaledKernel ε (ε • y) • f (x + ε • y)) =
      (ε ^ d)⁻¹ • ∫ y : Vec d, mollifier d y • f (x + ε • y) := by
    simp only [hk, mul_smul, integral_smul]
  rw [hi] at h
  have hc := congrArg (fun v : E => (ε ^ d) • v) h
  show (∫ y : Vec d, spatialScaledKernel ε y • f (x + y)) =
    ∫ y : Vec d, mollifier d y • f (x + ε • y)
  simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using hc.symm

theorem integral_spatialScaledKernel {ε : ℝ} (hε : 0 < ε) :
    (∫ y : Vec d, spatialScaledKernel ε y) = 1 := by
  have h := spatialSmoothMollify_eq_average hε (fun _ : Vec d => (1 : ℝ)) 0
  simpa only [spatialSmoothMollify, smul_eq_mul, mul_one, integral_mollifier] using h

/-- Reflection turns the literal `x+y` average into a standard convolution. -/
theorem spatialSmoothMollify_eq_convolution (ε : ℝ) (f : Vec d → E) :
    spatialSmoothMollify ε f =
      (fun y : Vec d => spatialScaledKernel ε (-y)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext x
  rw [spatialSmoothMollify, convolution_def, ← integral_neg_eq_self]
  simp only [ContinuousLinearMap.lsmul_apply, sub_eq_add_neg]

theorem spatialSmoothMollify_congr_ae (ε : ℝ) {f g : Vec d → E}
    (hfg : f =ᵐ[volume] g) : spatialSmoothMollify ε f = spatialSmoothMollify ε g := by
  funext x
  apply integral_congr_ae
  filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hfg] with y hy
  rw [hy]

/-- The spatial average is genuinely smooth for every nonzero scale, even when
its input has only local integrability. -/
theorem contDiff_spatialSmoothMollify {ε : ℝ} (hε : ε ≠ 0) {f : Vec d → E}
    (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialSmoothMollify ε f) := by
  rw [spatialSmoothMollify_eq_convolution]
  exact ((hasCompactSupport_spatialScaledKernel hε).comp_homeomorph (Homeomorph.neg (Vec d))).contDiff_convolution_left _
    ((contDiff_spatialScaledKernel ε).comp contDiff_neg) hf

/-- AE support of the input becomes pointwise support control after smoothing. -/
theorem spatialSmoothMollify_zero_off {ε : ℝ} (hε : ε ≠ 0) {K : Set (Vec d)}
    {f : Vec d → E} (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0)
    {x : Vec d} (hx : x ∉ spatialMollifySupport K ε) : spatialSmoothMollify ε f x = 0 := by
  change (∫ y : Vec d, spatialScaledKernel ε y • f (x + y)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hf] with y hy
  change spatialScaledKernel ε y • f (x + y) = 0
  by_cases hk : mollifier d (ε⁻¹ • y) = 0
  · simp only [spatialScaledKernel, hk, mul_zero, zero_smul]
  · have hnot : x + y ∉ K := by
      intro hmem
      apply hx
      refine ⟨(x + y, ε⁻¹ • y), ⟨hmem, subset_tsupport _ hk⟩, ?_⟩
      change (x + y) - ε • (ε⁻¹ • y) = x
      rw [smul_smul, mul_inv_cancel₀ hε, one_smul, add_sub_cancel_right]
    rw [hy hnot, smul_zero]

theorem tsupport_spatialSmoothMollify_subset {ε : ℝ} (hε : ε ≠ 0)
    {K : Set (Vec d)} (hK : IsCompact K) {f : Vec d → E}
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    tsupport (spatialSmoothMollify ε f) ⊆ spatialMollifySupport K ε := by
  apply closure_minimal ?_ (isCompact_spatialMollifySupport hK ε).isClosed
  intro x hx
  by_contra hnot
  exact hx (spatialSmoothMollify_zero_off hε hf hnot)

theorem hasCompactSupport_spatialSmoothMollify {ε : ℝ} (hε : ε ≠ 0)
    {K : Set (Vec d)} (hK : IsCompact K) {f : Vec d → E}
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    HasCompactSupport (spatialSmoothMollify ε f) :=
  (isCompact_spatialMollifySupport hK ε).of_isClosed_subset isClosed_closure
    (tsupport_spatialSmoothMollify_subset hε hK hf)

/-- Every locally integrable compactly supported datum produces actual smooth
compactly supported spatial approximants inside every prescribed open region. -/
theorem eventually_spatialSmoothMollify_test {K U : Set (Vec d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : Vec d → E}
    (hf : LocallyIntegrable f volume) (hfK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ∀ᶠ ε : ℝ in 𝓝[≠] 0, ContDiff ℝ (⊤ : ℕ∞) (spatialSmoothMollify ε f) ∧
      HasCompactSupport (spatialSmoothMollify ε f) ∧ tsupport (spatialSmoothMollify ε f) ⊆ U := by
  filter_upwards [(eventually_spatialMollifySupport_subset hK hU hKU).filter_mono inf_le_left,
    self_mem_nhdsWithin] with ε hsub hne
  exact ⟨contDiff_spatialSmoothMollify hne hf,
    hasCompactSupport_spatialSmoothMollify hne hK hfK,
    (tsupport_spatialSmoothMollify_subset hne hK hfK).trans hsub⟩

/-! The next convolution-calculus proofs adapt Armstrong–Kuusi–Loher's
`PDEFoundation/PDE/HarmonicConvolution.lean` and
`PDEFoundation/Sobolev/Inequalities/SobolevWholeSpaceCutoff.lean`, revision
`1e29da02bcc6e3c2359a5b8e0559e76d02ec4002` (Apache-2.0), to the existing
blueprint `coordinateDerivative` and `HasWeakPartialDerivative` carriers.
All proofs are replayed here against the pinned Mathlib. -/

/-- Coordinate differentiation of a compact smooth kernel convolution. -/
theorem coordinateDerivative_convolution_left {K g : Vec d → ℝ}
    (hKc : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : LocallyIntegrable g volume) (i : Fin d) :
    coordinateDerivative i (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      coordinateDerivative i K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  unfold coordinateDerivative
  rw [(hKc.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (hf := hK.of_le (by norm_num)) hg x).fderiv]
  calc
    ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d), volume] g) x)
        (unitVector i) =
        ((g ⋆[((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)).flip, volume]
          fderiv ℝ K) x) (unitVector i) := by rw [convolution_flip]
    _ = ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR (Vec d), volume]
          fderiv ℝ K) x) (unitVector i) := rfl
    _ = (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume]
          (fun y => fderiv ℝ K y (unitVector i))) x :=
      convolution_precompR_apply (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
        hg (hKc.fderiv ℝ) (hK.continuous_fderiv (by norm_num)) x (unitVector i)
    _ = ((fun y => fderiv ℝ K y (unitVector i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          g) x := by rw [convolution_flip]

/-- Reflection contributes the actual minus sign to a coordinate derivative. -/
theorem coordinateDerivative_comp_const_sub {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (x : Vec d) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun z => K (x - z)) y = -coordinateDerivative i K (x - y) := by
  have hi : HasFDerivAt (fun z : Vec d => x - z) (-(ContinuousLinearMap.id ℝ (Vec d))) y :=
    (hasFDerivAt_id y).const_sub x
  have hc := ((hK.differentiable (by simp) (x - y)).hasFDerivAt.comp y hi).fderiv
  change fderiv ℝ (fun z => K (x - z)) y (unitVector i) = _
  change fderiv ℝ (fun z => K (x - z)) y = _ at hc
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg, coordinateDerivative]

/-- Smooth compact convolution commutes with an actual distributional derivative;
the premise is the existing weak-derivative definition, not a smoothing identity. -/
theorem coordinateDerivative_convolution_eq_of_hasWeakPartialDerivative
    {K f g : Vec d → ℝ} (hKc : HasCompactSupport K)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) {i : Fin d}
    (hfg : HasWeakPartialDerivative Set.univ i f g) :
    coordinateDerivative i (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) =
      K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext x
  have hf : LocallyIntegrable f volume := by
    simpa only [locallyIntegrableOn_univ] using hfg.1
  rw [coordinateDerivative_convolution_left hKc hK hf i]
  have ht : IsSpatialTest Set.univ (fun y : Vec d => K (x - y)) :=
    ⟨hK.comp (contDiff_const.sub contDiff_id),
      hKc.comp_homeomorph (Homeomorph.subLeft x), subset_univ _⟩
  have hw := hfg.2.2 _ ht
  simp only [setIntegral_univ, coordinateDerivative_comp_const_sub hK x i,
    mul_neg, integral_neg, neg_inj] at hw
  rw [convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simpa only [mul_comm] using hw

/-- The classical coordinate derivative of the actual spatial average is the
same average of the weak derivative, for every nonzero scale and every point. -/
theorem coordinateDerivative_spatialSmoothMollify {ε : ℝ} (hε : ε ≠ 0)
    {f g : Vec d → ℝ} {i : Fin d} (hfg : HasWeakPartialDerivative Set.univ i f g) :
    coordinateDerivative i (spatialSmoothMollify ε f) = spatialSmoothMollify ε g := by
  rw [spatialSmoothMollify_eq_convolution, spatialSmoothMollify_eq_convolution]
  exact coordinateDerivative_convolution_eq_of_hasWeakPartialDerivative
    ((hasCompactSupport_spatialScaledKernel hε).comp_homeomorph (Homeomorph.neg (Vec d)))
    ((contDiff_spatialScaledKernel ε).comp contDiff_neg) hfg

end
end EinsteinFull
