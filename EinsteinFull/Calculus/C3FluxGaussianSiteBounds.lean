import EinsteinFull.Calculus.C1FluxGeneralTestAssembly

open scoped BigOperators
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Value and Euclidean gradient bounds for a Gaussian-controlled site block. -/
theorem c3_gaussian_site_recovery_bounds (d : ℕ) (c : ℝ) (hc : 0 < c)
    (B : ℕ → ℝ) (hB : ∀ q, 0 < B q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s r : ℝ), 0 < s → 0 < r →
      ∀ (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k c B ψ →
      ∀ z : Vec d,
      let R := 2 * Real.sqrt (d : ℝ) + 2
      let W := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-c * euclideanNorm y ^ 2 / s)) ''
          {y : Vec d | euclideanNorm (y - z) ≤ R * r})
      let A := C * s ^ (-(k : ℝ) / 2)
      let B' := C * (R * s ^ (-(k : ℝ) / 2) +
        r * s ^ (-((k + 1 : ℕ) : ℝ) / 2))
      let f := fun w : Vec d => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))
      0 ≤ A ∧ 0 ≤ B' ∧ (∀ w, ‖f w‖ ≤ A * W) ∧
        (∀ w, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ f w (unitVector j)‖ ^ 2) ≤
          (B' / r) * W) := by
  obtain ⟨C, hC, hbound⟩ := c1_flux_compact_schwartz_block_value_gradient d c hc B hB
  refine ⟨C, hC, ?_⟩
  intro s r hs hr k ψ hψ z
  have h := hbound s r hs hr k ψ hψ z
  dsimp only at h ⊢
  refine ⟨?_, ?_, h.1, ?_⟩
  · positivity
  · positivity
  · intro w
    convert h.2 w using 1 <;> field_simp [ne_of_gt hr] <;> ring

end EinsteinFull.Blueprint
