import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace EinsteinRelation.Correctors

/-- The scalar distribution test functional is continuous in spatial L².
Source: `paper/main.tex:699-704`. -/
theorem continuous_integral_mul_L2 {d : ℕ} (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U)]
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (fun f : Lp ℝ 2 (volume.restrict U) =>
      ∫ x in U, f x * φ x ∂volume) := by
  have hφ_memLp : MemLp φ 2 (volume.restrict U) :=
    hφ.memLp_of_hasCompactSupport hφc
  let φ_lp : Lp ℝ 2 (volume.restrict U) := MemLp.toLp φ hφ_memLp
  have h_eq : (fun f : Lp ℝ 2 (volume.restrict U) => ∫ x in U, f x * φ x ∂volume) =
      (fun f => inner ℝ f φ_lp) := by
    ext f
    dsimp [φ_lp]
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hφ_memLp] with x hx
    simp [hx, mul_comm]
  rw [h_eq]
  exact continuous_inner.comp (continuous_prodMk.2 ⟨continuous_id, continuous_const⟩)

end EinsteinRelation.Correctors
