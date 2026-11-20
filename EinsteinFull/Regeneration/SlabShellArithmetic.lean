import Mathlib.Tactic

/-!
# Arithmetic of the slab shell estimate

Substitution of value and gradient error bounds yields an affine energy
recurrence with explicit coefficients.
-/

namespace EinsteinFull.Regeneration

/-- Value and gradient shell bounds give an explicit affine energy estimate. -/
theorem slab_shell_substitution (Ein P α β T S lam A B E : ℝ)
    (hlam : 0 < lam) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hvalue : lam * T ≤ lam * A + B * E)
    (hgrad : lam * S ≤ lam * A + E)
    (henergy : Ein ≤ P + α * T + β * S) :
    Ein ≤ P + (α + β) * A + ((α * B + β) / lam) * E := by
  have ht : T ≤ A + (B / lam) * E := by
    have h : T ≤ (lam * A + B * E) / lam :=
      (le_div_iff₀ hlam).2 (by nlinarith [hvalue])
    have heq : (lam * A + B * E) / lam = A + (B / lam) * E := by
      field_simp
    simpa only [heq] using h
  have hs : S ≤ A + E / lam := by
    have h : S ≤ (lam * A + E) / lam :=
      (le_div_iff₀ hlam).2 (by nlinarith [hgrad])
    have heq : (lam * A + E) / lam = A + E / lam := by
      field_simp
    simpa only [heq] using h
  have htmul := mul_le_mul_of_nonneg_left ht hα
  have hsmul := mul_le_mul_of_nonneg_left hs hβ
  have heq : P + α * (A + (B / lam) * E) + β * (A + E / lam) =
      P + (α + β) * A + ((α * B + β) / lam) * E := by ring
  rw [← heq]
  linarith

end EinsteinFull.Regeneration
