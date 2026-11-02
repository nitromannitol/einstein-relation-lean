import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Support

/-! # Locally integrable functions with zero weak gradient are constant

A locally integrable `w : Vec d → ℝ` whose weak coordinate derivatives all vanish is almost
everywhere equal to a constant. The proof convolves `w` with normalized bump functions `ψₙ`
whose radii shrink to zero:

* each convolution `ψₙ ⋆ w` has zero derivative, because its derivative pairs `w` with the
  coordinate derivatives of translated bumps, which vanish by hypothesis; hence it is constant;
* by the Lebesgue differentiation theorem for bump families
  (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), `ψₙ ⋆ w` converges to `w`
  almost everywhere;
* a limit of a constant sequence is unique, so `w` takes one value on a set of full measure.
-/

open MeasureTheory Filter Topology
open scoped Convolution

namespace EinsteinRelation

/-- Lebesgue measure on `Vec d` is invariant under negation. The pinned Mathlib has no
`Measure.IsNegInvariant` instance for Haar measures. Negation is the linear map `(-1) • id`, whose
determinant `(-1) ^ d` has absolute value one, so the pushforward rescales the measure by one. -/
private instance isNegInvariant_volume_vec (d : ℕ) :
    Measure.IsNegInvariant (volume : Measure (Vec d)) := by
  refine ⟨?_⟩
  have hdet : LinearMap.det ((-1 : ℝ) • (LinearMap.id : Vec d →ₗ[ℝ] Vec d)) = (-1) ^ d := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun ℝ]
  have hdetne : LinearMap.det ((-1 : ℝ) • (LinearMap.id : Vec d →ₗ[ℝ] Vec d)) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ (by norm_num)
  have hf : ⇑((-1 : ℝ) • (LinearMap.id : Vec d →ₗ[ℝ] Vec d)) = (Neg.neg : Vec d → Vec d) := by
    funext v
    simp
  show Measure.map (Neg.neg : Vec d → Vec d) (volume : Measure (Vec d)) = volume
  rw [← hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdetne, hdet]
  simp [abs_inv, abs_pow]

/-- The normalized bump family used for mollification: the `n`-th bump has outer radius
`1 / (n + 1)` and inner radius half of that. -/
private noncomputable def shrinkingBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- A linear functional on `Vec d` is determined by its values on the coordinate vectors. -/
private theorem apply_eq_sum_unitVector_mul {d : ℕ} (T : Vec d →L[ℝ] ℝ) (v : Vec d) :
    T v = ∑ j, v j * T (unitVector j) := by
  have hv : v = ∑ j, v j • unitVector j := by
    funext i
    simp [unitVector, Finset.sum_apply, Pi.single_apply, mul_ite]
  calc T v = T (∑ j, v j • unitVector j) := by rw [← hv]
    _ = ∑ j, v j * T (unitVector j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

/-- The directional derivative of `ψ` in direction `v` is the `v`-weighted sum of its coordinate
derivatives. -/
private theorem fderiv_apply_eq_sum_coordinateDerivative {d : ℕ} (ψ : Vec d → ℝ) (t v : Vec d) :
    fderiv ℝ ψ t v = ∑ j, v j * coordinateDerivative j ψ t :=
  apply_eq_sum_unitVector_mul (fderiv ℝ ψ t) v

/-- Pairing the derivative of a convolution with a fixed direction gives the convolution of the
directional derivative of the smooth left factor. -/
private theorem fderiv_convolution_apply_eq {d : ℕ} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) {g : Vec d → ℝ} (hg : LocallyIntegrable g volume)
    (x v : Vec d) :
    (fderiv ℝ ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d),
        volume] g) x v =
      ((fun z => fderiv ℝ ψ z v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL
      (Vec d) (fderiv ℝ ψ t) (g (x - t))) volume :=
    (hψc.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d))
      (hψ.continuous_fderiv (by simp)) hg x
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hint v]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => rfl

/-- Reflecting a smooth test function through `y` reverses the sign of its coordinate
derivatives. -/
private theorem coordinateDerivative_reflect {d : ℕ} {ζ : Vec d → ℝ} (hζ1 : ContDiff ℝ 1 ζ)
    (y x : Vec d) (j : Fin d) :
    coordinateDerivative j (fun z : Vec d => ζ (y - z)) x =
      -coordinateDerivative j ζ (y - x) := by
  have hA : HasFDerivAt ζ (fderiv ℝ ζ (y - x)) (y - x) :=
    (hζ1.differentiable one_ne_zero (y - x)).hasFDerivAt
  have hg : HasFDerivAt (fun z : Vec d => y - z) (-ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).const_sub y
  have hc : HasFDerivAt (fun z : Vec d => ζ (y - z))
      ((fderiv ℝ ζ (y - x)).comp (-ContinuousLinearMap.id ℝ (Vec d))) x :=
    HasFDerivAt.comp x hA hg
  unfold coordinateDerivative
  rw [hc.fderiv]
  simp

/-- Each coordinate derivative of `ζ`, paired with `w` along the reflection `t ↦ y - t`, integrates
to zero. This is the weak gradient hypothesis applied to the test function `x ↦ ζ (y - x)`. -/
private theorem integral_coordinateDerivative_reflect_eq_zero {d : ℕ} {w : Vec d → ℝ}
    (hzero : ∀ (j : Fin d) (ψ : Vec d → ℝ), IsSpatialTest Set.univ ψ →
      ∫ x, w x * coordinateDerivative j ψ x = 0)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (y : Vec d)
    (j : Fin d) :
    ∫ t, w (y - t) * coordinateDerivative j ζ t = 0 := by
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (mod_cast le_top)
  have hψC : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ζ (y - x)) :=
    hζ.comp ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Vec d => y).sub contDiff_id)
  have hψc : HasCompactSupport (fun x : Vec d => ζ (y - x)) :=
    hζc.comp_homeomorph (Homeomorph.subLeft y)
  have hcv := integral_sub_left_eq_self
    (fun t : Vec d => w (y - t) * coordinateDerivative j ζ t) volume y
  simp only [sub_sub_cancel] at hcv
  rw [← hcv]
  have hψ := hzero j (fun x : Vec d => ζ (y - x)) ⟨hψC, hψc, Set.subset_univ _⟩
  simp only [coordinateDerivative_reflect hζ1, mul_neg, integral_neg, neg_eq_zero] at hψ
  exact hψ

/-- The product of `w (y - ·)` with a coordinate derivative of a smooth compactly supported `ζ` is
integrable: `w` is locally integrable, and the derivative is continuous with compact support. -/
private theorem integrable_coordinateDerivative_reflect {d : ℕ} {w : Vec d → ℝ}
    (hw : LocallyIntegrable w volume) {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (y : Vec d) (j : Fin d) :
    Integrable (fun t => w (y - t) * coordinateDerivative j ζ t) volume := by
  have hcont : Continuous (fun x : Vec d => coordinateDerivative j ζ x) := by
    unfold coordinateDerivative
    exact (hζ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x : Vec d => coordinateDerivative j ζ x) :=
    hζc.fderiv_apply ℝ (unitVector j)
  have h : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      (coordinateDerivative j ζ t) (w (y - t))) volume :=
    hcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hcont hw y
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  ring

/-- The scalar convolution of `w` with the directional derivative of a smooth compactly supported
`ζ` vanishes at every point, because each coordinate pairing does. -/
private theorem convolution_fderiv_apply_eq_zero {d : ℕ} {w : Vec d → ℝ}
    (hw : LocallyIntegrable w volume)
    (hzero : ∀ (j : Fin d) (ψ : Vec d → ℝ), IsSpatialTest Set.univ ψ →
      ∫ x, w x * coordinateDerivative j ψ x = 0)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (y v : Vec d) :
    ((fun z => fderiv ℝ ζ z v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) y = 0 := by
  have hpt : ∀ t : Vec d, fderiv ℝ ζ t v * w (y - t) =
      ∑ j, v j * (w (y - t) * coordinateDerivative j ζ t) := by
    intro t
    rw [fderiv_apply_eq_sum_coordinateDerivative ζ t v, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∫ t : Vec d, ∑ j, v j * (w (y - t) * coordinateDerivative j ζ t) =
      ∑ j, ∫ t : Vec d, v j * (w (y - t) * coordinateDerivative j ζ t) :=
    integral_finset_sum Finset.univ fun j _ =>
      (integrable_coordinateDerivative_reflect hw hζ hζc y j).const_mul (v j)
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hpt]
  rw [hsplit]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, integral_coordinateDerivative_reflect_eq_zero hzero hζ hζc y j,
    mul_zero]

/-- The convolution `ζ ⋆ w` of a smooth compactly supported `ζ` with a locally integrable `w` of
zero weak gradient has zero derivative everywhere. -/
private theorem hasFDerivAt_convolution_zero {d : ℕ} {w : Vec d → ℝ}
    (hw : LocallyIntegrable w volume)
    (hzero : ∀ (j : Fin d) (ψ : Vec d → ℝ), IsSpatialTest Set.univ ψ →
      ∫ x, w x * coordinateDerivative j ψ x = 0)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (y : Vec d) :
    HasFDerivAt (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) (0 : Vec d →L[ℝ] ℝ) y := by
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (mod_cast le_top)
  refine (hζc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hζ1 hw y).congr_fderiv
    ?_
  ext v
  rw [fderiv_convolution_apply_eq hζ1 hζc hw y v, ContinuousLinearMap.zero_apply]
  exact convolution_fderiv_apply_eq_zero hw hzero hζ hζc y v

/-- The convolution `ζ ⋆ w` of a smooth compactly supported `ζ` with a locally integrable `w` of
zero weak gradient is constant. -/
private theorem convolution_const_of_zero_weak {d : ℕ} {w : Vec d → ℝ}
    (hw : LocallyIntegrable w volume)
    (hzero : ∀ (j : Fin d) (ψ : Vec d → ℝ), IsSpatialTest Set.univ ψ →
      ∫ x, w x * coordinateDerivative j ψ x = 0)
    {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) (x y : Vec d) :
    (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x =
      (ζ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) y :=
  is_const_of_fderiv_eq_zero
    (fun z => (hasFDerivAt_convolution_zero hw hzero hζ hζc z).differentiableAt)
    (fun z => (hasFDerivAt_convolution_zero hw hzero hζ hζc z).fderiv) x y

/-- A locally integrable function on `Vec d` whose weak coordinate derivatives all vanish along
every smooth compactly supported test function is almost everywhere equal to a constant. -/
theorem ae_eq_const_of_zero_weak_gradient {d : ℕ} {w : Vec d → ℝ}
    (hw : LocallyIntegrable w volume)
    (hzero : ∀ (j : Fin d) (ψ : Vec d → ℝ), IsSpatialTest Set.univ ψ →
      ∫ x, w x * coordinateDerivative j ψ x = 0) :
    ∃ c : ℝ, w =ᵐ[volume] fun _ => c := by
  have hζsm : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) ((shrinkingBump d n).normed volume) :=
    fun n => (shrinkingBump d n).contDiff_normed
  have hζcs : ∀ n : ℕ, HasCompactSupport ((shrinkingBump d n).normed volume) :=
    fun n => (shrinkingBump d n).hasCompactSupport_normed
  -- Each mollification is constant.
  have hconst : ∀ (n : ℕ) (x y : Vec d),
      ((shrinkingBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x =
        ((shrinkingBump d n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) y :=
    fun n x y => convolution_const_of_zero_weak hw hzero (hζsm n) (hζcs n) x y
  -- The mollifications converge to `w` almost everywhere.
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ0 : Tendsto (fun n : ℕ => (shrinkingBump d n).rOut) atTop (𝓝 0) := hinv
  have h'φ : ∀ᶠ n in atTop, (shrinkingBump d n).rOut ≤ 2 * (shrinkingBump d n).rIn :=
    Eventually.of_forall fun n => by
      show 1 / ((n : ℝ) + 1) ≤ 2 * (1 / ((n : ℝ) + 1) / 2)
      exact le_of_eq (by ring)
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := shrinkingBump d) (l := atTop) (K := 2) hφ0 h'φ hw
  -- The ambient measure is nonzero, so the almost-everywhere set is nonempty.
  haveI : (ae (volume : Measure (Vec d))).NeBot := by
    refine ae_neBot.mpr fun h => ?_
    have hpos := Metric.measure_ball_pos volume (0 : Vec d) one_pos
    rw [h] at hpos
    simp at hpos
  obtain ⟨x₀, hx₀⟩ := hae.exists
  refine ⟨w x₀, ?_⟩
  filter_upwards [hae] with x hx
  have hx' := Filter.Tendsto.congr (fun n => hconst n x x₀) hx
  exact tendsto_nhds_unique hx' hx₀


end EinsteinRelation
