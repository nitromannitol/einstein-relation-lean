import EinsteinRelation.Correctors.PairedPDETesting
import Mathlib.MeasureTheory.Integral.Prod

/-! # Spatial integration by parts for actual space-time energy fields

Source: `paper/main.tex:832–840`. Slice weak gradients and genuine L²
integrability suffice for the space-time identity needed to transfer a
spatial derivative through the regularizing convolution.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Spatial slice integration by parts integrates to the actual space-time
identity. The field needs no time derivative.
Source: `paper/main.tex:832–840`. -/
theorem paired_spacetime_spatial_integration_by_parts {d : ℕ}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 volume)
    (hG : ∀ j, MemLp (fun z => G z j) 2 volume)
    (hweak : ∀ᵐ t ∂(volume : Measure ℝ),
      HasWeakGradient Set.univ (fun x => u (t, x)) (fun x => G (t, x)))
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (j : Fin d) :
    (∫ z : ℝ × Vec d, u z * fderiv ℝ ζ z (0, unitVector j)) =
      -(∫ z : ℝ × Vec d, G z j * ζ z) := by
  have hD : MemLp (fun z => fderiv ℝ ζ z (0, unitVector j)) 2 volume :=
    (((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous).memLp_of_hasCompactSupport (hζc.fderiv_apply ℝ _)
  have hζ2 : MemLp ζ 2 volume := hζ.continuous.memLp_of_hasCompactSupport hζc
  have hL : Integrable (fun z => u z * fderiv ℝ ζ z (0, unitVector j)) volume :=
    hu.integrable_mul hD
  have hR : Integrable (fun z => G z j * ζ z) volume :=
    (hG j).integrable_mul hζ2
  rw [Measure.volume_eq_prod ℝ (Vec d)] at hL hR ⊢
  rw [integral_prod _ hL, integral_prod _ hR, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hweak] with t ht
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ζ (t,x)) :=
    hζ.comp (contDiff_const.prodMk contDiff_id)
  have hemb : Topology.IsClosedEmbedding (fun x : Vec d => (t,x)) := by
    rw [Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
    exact ⟨continuous_const.prodMk continuous_id,
      fun _ _ h => congrArg Prod.snd h, isClosedMap_prodMk_left t⟩
  have htest : IsSpatialTest Set.univ (fun x => ζ (t,x)) :=
    ⟨hcomp, hζc.comp_isClosedEmbedding hemb, Set.subset_univ _⟩
  have hder (x : Vec d) : coordinateDerivative j (fun y => ζ (t,y)) x =
      fderiv ℝ ζ (t,x) (0,unitVector j) := by
    have hd := ((hζ.differentiable (by simp) (t,x)).hasFDerivAt).comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change fderiv ℝ (ζ ∘ Prod.mk t) x (unitVector j) = _
    rw [hd.fderiv]
    rfl
  simpa only [Measure.restrict_univ, hder] using (ht j).2.2 _ htest

end EinsteinRelation.Correctors
