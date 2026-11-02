import EinsteinRelation.Diffusion.Basic

/-!
# Support for `sharp.example#positive-coefficient`

Uniqueness of quenched almost-sure limits, the coordinate formula for the dot product with a unit
vector, and the one-variable expansion `(η⁻¹ - 1) / λ → δ (A - 1)` for `η = 1 - δ λ (avg - 1)`.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull
open EinsteinRelation

/-- A quenched almost-sure equality of constants forces equality, when `Q` is a probability
measure and the path laws are almost surely probability measures. -/
theorem eq_of_quenched_ae {d : ℕ} {β : Type*} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {P : ProbabilityTheory.Kernel (FieldPair d) (Path d)}
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P ω)) {a b : β}
    (h : ∀ᵐ ω ∂Q, ∀ᵐ _γ ∂P ω, a = b) : a = b := by
  obtain ⟨ω, hω, hprob⟩ := (h.and hP).exists
  haveI : IsProbabilityMeasure (P ω) := hprob
  obtain ⟨_, hab⟩ := hω.exists
  exact hab

theorem dot_unitVector_right' {d : ℕ} (i : Fin d) (v : Vec d) : dot v (unitVector i) = v i := by
  simp [dot, unitVector, Pi.single_apply]

/-- Algebra of the clock expansion at a fixed positive force. -/
theorem sharp_expansion_algebra (lam η δ a : ℝ) (hl : lam ≠ 0) (hη : η ≠ 0)
    (h : η = 1 - δ * lam * (a - 1)) :
    (lam⁻¹ * (η⁻¹ * lam) - 1) / lam = δ * (a - 1) / η := by
  have e1 : lam⁻¹ * (η⁻¹ * lam) = η⁻¹ := by field_simp
  have e2 : η⁻¹ - 1 = (1 - η) / η := by field_simp
  have e3 : 1 - η = δ * lam * (a - 1) := by linarith
  rw [e1, e2, e3]
  field_simp

/-- The limit of the expansion as the force tends to zero from the right. -/
theorem tendsto_sharp_expansion (δ A : ℝ) (avg : ℝ → ℝ)
    (havg : Tendsto avg (𝓝[>] (0 : ℝ)) (𝓝 A)) :
    Tendsto (fun lam : ℝ => δ * (avg lam - 1) / (1 - δ * lam * (avg lam - 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 (δ * (A - 1))) := by
  have hl : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun lam : ℝ => δ * (avg lam - 1)) (𝓝[>] (0 : ℝ)) (𝓝 (δ * (A - 1))) :=
    tendsto_const_nhds.mul (havg.sub tendsto_const_nhds)
  have hden : Tendsto (fun lam : ℝ => 1 - δ * lam * (avg lam - 1)) (𝓝[>] (0 : ℝ))
      (𝓝 (1 - δ * 0 * (A - 1))) :=
    tendsto_const_nhds.sub ((tendsto_const_nhds.mul hl).mul (havg.sub tendsto_const_nhds))
  have h1 : (1 : ℝ) - δ * 0 * (A - 1) = 1 := by rw [mul_zero, zero_mul, sub_zero]
  rw [h1] at hden
  have := hnum.div hden one_ne_zero
  rw [div_one] at this
  exact this

end EinsteinFull
