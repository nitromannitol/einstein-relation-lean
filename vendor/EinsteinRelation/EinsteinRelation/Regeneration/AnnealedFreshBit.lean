import EinsteinRelation.Regeneration.Coupling

/-! # Annealed fresh-bit identity

Source `paper/main.tex:353–364`, the Bernoulli fresh-bit step for `Γₙ` in the
first-regeneration decomposition. The identity is an INTERNAL consequence of the
cited fresh-bit kernel input `HasFreshBits` (GMP Prop.5.4(ii)): the fibrewise
kernel identity `FreshBitsAt` is integrated against the actual annealed law
`annealedCoupledLaw`, keeping the physical environment in the joint law. No new
external premise is assumed, and renewal is not closed here.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration

/-- A bounded joint test has bounded sample fibres at every fixed environment. -/
private theorem boundedRealTest_fiber {α β : Type*} (f : α × β → ℝ)
    (hf : BoundedRealTest f) (a : α) : BoundedRealTest (fun b => f (a, b)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, |f x| ≤ C := hf
  exact ⟨C, fun b => hC (a, b)⟩

/-- Multiplying a bounded test by the fresh-bit indicator keeps the same bound,
since the indicator takes only the values zero and one. -/
private theorem boundedRealTest_mul_bit {d : ℕ} (n : ℕ)
    (H : FieldPair d × CoupledSample d → ℝ) (hb : BoundedRealTest H) :
    BoundedRealTest (fun ωz : FieldPair d × CoupledSample d =>
      H ωz * (if ωz.2.2 n = true then (1 : ℝ) else 0)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, |H x| ≤ C := hb
  refine ⟨C, fun ωz => ?_⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC ωz)
  show |H ωz * (if ωz.2.2 n = true then (1 : ℝ) else 0)| ≤ C
  split_ifs
  · simpa using hC ωz
  · simpa using hC0

/-- The fresh-bit indicator is measurable for the literal product sigma algebra
on the physical environment and the coupled path/Bernoulli sample. -/
private theorem measurable_fresh_bit_indicator {d : ℕ} (n : ℕ) :
    Measurable (fun ωz : FieldPair d × CoupledSample d =>
      (if ωz.2.2 n = true then (1 : ℝ) else 0)) := by
  have hbit : Measurable (fun ωz : FieldPair d × CoupledSample d => ωz.2.2 n) :=
    (measurable_pi_apply (X := fun _ : ℕ => Bool) n).comp measurable_snd.snd
  have hset : MeasurableSet {ωz : FieldPair d × CoupledSample d | ωz.2.2 n = true} :=
    hbit (measurableSet_singleton true)
  exact Measurable.ite hset measurable_const measurable_const

/-- Source `paper/main.tex:353–364`, annealed form of the fresh-bit identity for `Γₙ`.
The origin-a.e. kernel identity `FreshBitsAt` is applied on each environment fibre
`z ↦ H (ω, z)`, which is finite-history measurable by `hPast` and bounded by `hB`.
Integrating over the environment with `integral_annealedCoupledLaw` on both sides
gives the identity. -/
theorem integral_annealed_fresh_bit {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (δ : ℝ)
    (hFresh : HasFreshBits Q Δ δ K) (n : ℕ)
    (H : FieldPair d × CoupledSample d → ℝ) (hH : Measurable H) (hB : BoundedRealTest H)
    (hPast : ∀ ω, @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance (fun z => H (ω,z))) :
    (∫ ωz, H ωz * (if ωz.2.2 n = true then (1:ℝ) else 0) ∂annealedCoupledLaw Q K) =
      δ * ∫ ωz, H ωz ∂annealedCoupledLaw Q K := by
  have hFm : Measurable (fun ωz : FieldPair d × CoupledSample d =>
      H ωz * (if ωz.2.2 n = true then (1 : ℝ) else 0)) :=
    hH.mul (measurable_fresh_bit_indicator n)
  rw [integral_annealedCoupledLaw Q K hK _ hFm (boundedRealTest_mul_bit n H hB),
    integral_annealedCoupledLaw Q K hK H hH hB, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hFresh.1] with ω hω
  exact hω n (fun z => H (ω, z)) (hPast ω) (boundedRealTest_fiber H hB ω)

end EinsteinRelation.Regeneration
