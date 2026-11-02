import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# Bounded linear Volterra equations and force power series

Neumann inversion identifies solutions and proves analytic dependence at zero
in a complete complex normed space, including the operator norm topology.
-/

open Filter
open scoped Topology
noncomputable section
namespace EinsteinFull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The inverse Neumann operator solves a bounded linear perturbation equation. -/
theorem eq_inverse_one_sub_smul_of_eq_add (V : E →L[ℂ] E) (z : ℂ) (u b : E)
    (he : u = b + z • V u) (hs : ‖z • V‖ < 1) :
    u = Ring.inverse (1 - z • V) b := by
  let A := z • V
  have he' : (1 - A) u = b := by
    change u - z • V u = b
    exact sub_eq_iff_eq_add.mpr he
  have hunit : IsUnit (1 - A) := isUnit_one_sub_of_norm_lt_one (x := A) hs
  have hi := Ring.inverse_mul_cancel (1 - A) hunit
  have hx := congrArg (fun L => L u) hi
  change Ring.inverse (1 - A) ((1 - A) u) = u at hx
  rw [he'] at hx
  exact hx.symm

/-- The Neumann force series converges to every solution of the bounded perturbation equation. -/
theorem hasSum_pow_smul_of_eq_add (V : E →L[ℂ] E) (z : ℂ) (u b : E)
    (he : u = b + z • V u) (hs : ‖z • V‖ < 1) :
    HasSum (fun n : ℕ => z ^ n • (V ^ n) b) u := by
  rw [eq_inverse_one_sub_smul_of_eq_add V z u b he hs]
  have hh := (hasSum_geom_series_inverse (z • V) hs).mapL (ContinuousLinearMap.apply ℂ E b)
  simpa only [smul_pow, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.apply_apply] using hh

/-- A family solving the same bounded linear perturbation equation is analytic at zero. -/
theorem analyticAt_of_eq_add_smul (V : E →L[ℂ] E) (b : E) (u : ℂ → E)
    (he : ∀ z, u z = b + z • V (u z)) : AnalyticAt ℂ u 0 := by
  have hi : AnalyticAt ℂ (fun z : ℂ => z • V) 0 := by
    exact (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).fun_smul
      (analyticAt_const (v := V))
  have hinv : AnalyticAt ℂ (fun z : ℂ => Ring.inverse (1 - z • V)) 0 := by
    exact (analyticAt_inverse_one_sub ℂ (E →L[ℂ] E)).comp_of_eq hi (zero_smul ℂ V)
  have ha : AnalyticAt ℂ (fun z : ℂ => Ring.inverse (1 - z • V) b) 0 :=
    ((ContinuousLinearMap.apply ℂ E b).analyticAt _).comp hinv
  apply ha.congr
  have hs : ∀ᶠ z : ℂ in 𝓝 0, ‖z • V‖ < 1 :=
    ((continuous_id.smul continuous_const).norm.tendsto (0 : ℂ)).eventually
      (eventually_lt_nhds (show ‖(0 : ℂ) • V‖ < 1 by simp only [zero_smul, norm_zero]; norm_num))
  filter_upwards [hs] with z hz
  exact (eq_inverse_one_sub_smul_of_eq_add V z (u z) b (he z) hz).symm

/-- Left composition transfers the perturbation argument to the operator norm topology. -/
theorem analyticAt_clm_of_eq_add_comp_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : E →L[ℂ] E) (b : F →L[ℂ] E) (u : ℂ → F →L[ℂ] E)
    (he : ∀ z, u z = b + z • V.comp (u z)) : AnalyticAt ℂ u 0 :=
  analyticAt_of_eq_add_smul ((ContinuousLinearMap.compL ℂ F E E) V) b u he

end EinsteinFull
