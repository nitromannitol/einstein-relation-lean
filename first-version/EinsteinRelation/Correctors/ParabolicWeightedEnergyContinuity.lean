import EinsteinRelation.Correctors.SemigroupLocalL2Continuity
import Mathlib.MeasureTheory.Function.Holder

/-! # Continuous weighted energies of the actual flow

Source: `paper/main.tex:832–850`. A bounded spatial multiplier acts
continuously on L². Thus the scalar local trace, rather than an assumed
classical time derivative, supplies the continuous weighted energy and
its zero initial value used in the paired energy argument.
-/

open MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

/-- A fixed bounded measurable spatial weight gives a continuous quadratic
energy on L². Source: `paper/main.tex:832–848`. -/
theorem continuousOn_weighted_square_integral_of_L2
    {X T : Type*} [MeasurableSpace X] [TopologicalSpace T]
    {μ : Measure X} {S : Set T} {χ : X → ℝ} (hχ : MemLp χ ∞ μ)
    {v : T → Lp ℝ 2 μ} (hv : ContinuousOn v S) :
    ContinuousOn (fun t => ∫ x, χ x ^ 2 * (v t x)^2 ∂μ) S := by
  let M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 (hχ.toLp χ)
  have heq (t : T) : ‖M (v t)‖^2 = ∫ x, χ x^2 * (v t x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    have hM := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
      (r := (2 : ℝ≥0∞)) (hχ.toLp χ) (v t)
    filter_upwards [hM, hχ.coeFn_toLp] with x hx hχx
    change (M (v t)) x = _ at hx
    simp only [ContinuousLinearMap.mul_apply', hχx] at hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  simpa only [Function.comp_apply, heq] using ((M.continuous.comp_continuousOn hv).norm.pow 2)

open External.AKM Environment.AKMTestIntegralSupport

/-- A genuine paired local L² trace supplies a continuous weighted energy
with zero initial value. The positive-time values are the literal spatial
integrals of the specified flows. Source: `paper/main.tex:832–850`. -/
theorem paired_weighted_energy_continuous_of_local_L2_trace
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)]
    (v : ℝ → Lp ℝ 2 (volume.restrict U))
    (hv : ContinuousWithinAt v (Set.Ici 0) 0) (hv₀ : v 0 = 0)
    (hrep : ∀ t : ℝ, 0 < t →
      (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t,x) - u₂ (t,x))
    {χ : Vec d → ℝ} (hχ : MemLp χ ∞ (volume.restrict U)) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Set.Ici 0) ∧ F 0 = 0 ∧
      (∀ t, 0 ≤ F t) ∧ ∀ t : ℝ, 0 < t →
        F t = ∫ x in U, χ x^2 * (u₁ (t,x) - u₂ (t,x))^2 := by
  let F : ℝ → ℝ := fun t => ∫ x in U, χ x^2 * (v t x)^2
  refine ⟨F, continuousOn_weighted_square_integral_of_L2 hχ
    (paired_semigroupSolutions_continuous_local_L2_of_trace h₁ h₂ hU v hv hrep), ?_, ?_, ?_⟩
  · dsimp only [F]
    rw [hv₀]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict U)] with x hx
    simp only [hx, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · intro t
    exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · intro t ht
    apply integral_congr_ae
    filter_upwards [hrep t ht] with x hx
    rw [hx]

end EinsteinRelation.Correctors
