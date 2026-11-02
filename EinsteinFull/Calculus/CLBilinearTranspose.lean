import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bilinear transposes on complex L²

Every bounded operator `T` on complex `L²` has a bilinear transpose `Tᵀ`, with
`∫ (T f) g = ∫ f (Tᵀ g)` for all `f g`: conjugate the Hilbert adjoint by complex conjugation,
`Tᵀ g = conj (T† (conj g))`.
-/

open MeasureTheory

noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem Lp_star_add (f g : Lp ℂ 2 μ) : star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g),
    Lp.coeFn_star f, Lp.coeFn_star g] with x h1 h2 h3 h4 h5
  simp only [h1, h3, Pi.star_apply, Pi.add_apply, h2, h4, h5, star_add]

theorem Lp_star_smul (c : ℂ) (f : Lp ℂ 2 μ) : star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_smul (star c) (star f),
    Lp.coeFn_star f] with x h1 h2 h3 h4
  simp only [h1, h3, Pi.star_apply, Pi.smul_apply, h2, h4, smul_eq_mul, star_mul']

theorem Lp_norm_star (f : Lp ℂ 2 μ) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

/-- The bilinear pairing is the inner product with the conjugate. -/
theorem integral_mul_eq_inner_star (g h : Lp ℂ 2 μ) :
    ∫ x, g x * h x ∂μ = inner ℂ (star g) h := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  change (star g : Lp ℂ 2 μ) x = star (g x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def, Complex.conj_conj, mul_comm]

theorem integral_mul_star_eq_inner (u f : Lp ℂ 2 μ) :
    ∫ x, f x * (star u : Lp ℂ 2 μ) x ∂μ = inner ℂ u f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with x hx
  change (star u : Lp ℂ 2 μ) x = star (u x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def]

/-- The bilinear transpose `g ↦ conj (T† (conj g))`. -/
def bilinearTranspose (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun g => star (ContinuousLinearMap.adjoint T (star g))
      map_add' := fun g h => by
        simp only [Lp_star_add, map_add]
      map_smul' := fun c g => by
        simp only [Lp_star_smul, map_smul, star_star, RingHom.id_apply] }
    ‖ContinuousLinearMap.adjoint T‖ fun g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp_norm_star]
      calc ‖ContinuousLinearMap.adjoint T (star g)‖ ≤
            ‖ContinuousLinearMap.adjoint T‖ * ‖star g‖ :=
            (ContinuousLinearMap.adjoint T).le_opNorm _
        _ = ‖ContinuousLinearMap.adjoint T‖ * ‖g‖ := by rw [Lp_norm_star]

theorem bilinearTranspose_apply (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (g : Lp ℂ 2 μ) :
    bilinearTranspose T g = star (ContinuousLinearMap.adjoint T (star g)) := rfl

/-- The defining identity `∫ (T f) g = ∫ f (Tᵀ g)`. -/
theorem integral_mul_bilinearTranspose (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (f g : Lp ℂ 2 μ) :
    ∫ x, T f x * g x ∂μ = ∫ x, f x * bilinearTranspose T g x ∂μ := by
  have h1 : ∫ x, T f x * g x ∂μ = inner ℂ (star g) (T f) := by
    rw [← integral_mul_eq_inner_star]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [h1, bilinearTranspose_apply, integral_mul_star_eq_inner,
    ContinuousLinearMap.adjoint_inner_left]

end EinsteinFull
