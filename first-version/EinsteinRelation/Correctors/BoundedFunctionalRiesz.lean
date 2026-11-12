import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.Basic

namespace EinsteinRelation.Correctors

/-- A functional bounded through a Hilbert-space map has a Riesz representative.
Source: `paper/main.tex:798–806`; prescribed-time weak derivative recovery. -/
theorem exists_riesz_of_linear_factor_bound
    {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : V →ₗ[ℝ] H) (L : V →ₗ[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ v, |L v| ≤ B * ‖T v‖) :
    ∃ g : H, ‖g‖ ≤ B ∧ ∀ v, inner ℝ g (T v) = L v := by
  -- Step 1: L vanishes on ker T
  have hL_ker : LinearMap.ker T ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := hb x
    rw [hx, norm_zero, mul_zero] at h
    have h_abs : |L x| = 0 := le_antisymm h (abs_nonneg _)
    exact abs_eq_zero.mp h_abs
  -- Step 2: Lift L to V / ker T
  let L' := (LinearMap.ker T).liftQ L hL_ker
  have hL'_apply (v : V) : L' (Submodule.Quotient.mk v) = L v :=
    Submodule.liftQ_apply _ _ _
  -- Step 3: Compose with the isomorphism V/ker T ≃ range T
  let φ := L'.comp (T.quotKerEquivRange.symm.toLinearMap)
  have hφ_apply_T (v : V) : φ ⟨T v, LinearMap.mem_range_self T v⟩ = L v := by
    calc
      φ ⟨T v, LinearMap.mem_range_self T v⟩ =
          L' (T.quotKerEquivRange.symm ⟨T v, LinearMap.mem_range_self T v⟩) := rfl
      _ = L' ((LinearMap.ker T).mkQ v) := by
        rw [T.quotKerEquivRange_symm_apply_image v (LinearMap.mem_range_self T v)]
      _ = L v := Submodule.liftQ_apply _ _ _
  -- Step 4: Show φ is bounded
  have hφ_bound (x : LinearMap.range T) : ‖φ x‖ ≤ B * ‖(x : H)‖ := by
    rcases x.property with ⟨v, hv⟩
    have h1 : φ x = L v := by
      have hx_eq : x = ⟨T v, LinearMap.mem_range_self T v⟩ := Subtype.ext hv.symm
      rw [hx_eq, hφ_apply_T v]
    rw [h1]
    have h := hb v
    simpa [Real.norm_eq_abs, ← hv] using h
  let f : StrongDual ℝ (LinearMap.range T) := φ.mkContinuous B hφ_bound
  have hf : ‖f‖ ≤ B := φ.mkContinuous_norm_le hB hφ_bound
  obtain ⟨F,hF,hFnorm⟩ := Real.exists_extension_norm_eq (LinearMap.range T) f
  let g := (InnerProductSpace.toDual ℝ H).symm F
  refine ⟨g, ?_, ?_⟩
  · simpa [g, hFnorm] using hf
  · intro v
    change inner ℝ ((InnerProductSpace.toDual ℝ H).symm F) (T v) = L v
    rw [InnerProductSpace.toDual_symm_apply]
    exact (hF ⟨T v, LinearMap.mem_range_self T v⟩).trans (hφ_apply_T v)

end EinsteinRelation.Correctors
