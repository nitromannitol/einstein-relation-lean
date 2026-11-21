import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Integration of a slab absorption estimate

Splitting an energy comparison into its inset and its shell cancels the
solution's shell energy and leaves an estimate on the inset.
-/

open MeasureTheory Set

namespace EinsteinFull.Regeneration

/-- A half-energy gain on the inset gives an integrated inset bound. -/
theorem inner_energy_le_of_absorption
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Q I : Set X)
    (hQ : MeasurableSet Q) (hI : MeasurableSet I) (hIQ : I ⊆ Q)
    (eu ep ec t : X → ℝ) (α : ℝ)
    (heu : IntegrableOn eu Q μ) (hep : IntegrableOn ep Q μ)
    (hec : IntegrableOn ec Q μ) (ht : IntegrableOn t Q μ)
    (hmin : (∫ x in Q, eu x ∂μ) ≤ ∫ x in Q, ec x ∂μ)
    (hinner : ∀ᵐ x ∂(μ.restrict I),
      ec x ≤ (1 / 2 : ℝ) * eu x + (3 / 2 : ℝ) * ep x + α * t x)
    (hshell : ∀ᵐ x ∂(μ.restrict (Q \ I)),
      ec x ≤ eu x + (3 / 2 : ℝ) * ep x + α * t x) :
    (∫ x in I, eu x ∂μ) ≤ 3 * (∫ x in Q, ep x ∂μ) +
      2 * α * ∫ x in Q, t x ∂μ := by
  have hdis : Disjoint I (Q \ I) := Set.disjoint_left.2 (fun _ hx hy => hy.2 hx)
  have hunion : I ∪ (Q \ I) = Q := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hIQ hx
      · exact hx.1
    · intro hx
      by_cases hi : x ∈ I
      · exact Or.inl hi
      · exact Or.inr ⟨hx, hi⟩
  have hsplit (f : X → ℝ) (hf : IntegrableOn f Q μ) :
      (∫ x in Q, f x ∂μ) = (∫ x in I, f x ∂μ) + ∫ x in Q \ I, f x ∂μ := by
    calc
      _ = ∫ x in I ∪ (Q \ I), f x ∂μ := by rw [hunion]
      _ = _ := setIntegral_union hdis (hQ.diff hI) (hf.mono_set hIQ) (hf.mono_set sdiff_subset)
  have hpart (S : Set X) (hSQ : S ⊆ Q) (c : ℝ)
      (hpoint : ∀ᵐ x ∂(μ.restrict S), ec x ≤ c * eu x + (3 / 2 : ℝ) * ep x + α * t x) :
      (∫ x in S, ec x ∂μ) ≤ c * (∫ x in S, eu x ∂μ) +
        (3 / 2 : ℝ) * (∫ x in S, ep x ∂μ) + α * ∫ x in S, t x ∂μ := by
    have hu := heu.mono_set hSQ
    have hp := hep.mono_set hSQ
    have ht' := ht.mono_set hSQ
    have hsum := (hu.const_mul c).add (hp.const_mul (3 / 2 : ℝ))
    have hbound := integral_mono_ae (hec.mono_set hSQ) (hsum.add (ht'.const_mul α)) hpoint
    have h1 := integral_add hsum (ht'.const_mul α)
    have h2 := integral_add (hu.const_mul c) (hp.const_mul (3 / 2 : ℝ))
    simp only [Pi.add_apply] at hbound h1 h2
    rw [h1, h2, integral_const_mul, integral_const_mul, integral_const_mul] at hbound
    exact hbound
  have hi := hpart I hIQ (1 / 2) hinner
  have hs : (∫ x in Q \ I, ec x ∂μ) ≤ (∫ x in Q \ I, eu x ∂μ) +
      (3 / 2 : ℝ) * (∫ x in Q \ I, ep x ∂μ) + α * ∫ x in Q \ I, t x ∂μ := by
    simpa only [one_mul] using hpart (Q \ I) sdiff_subset 1 (by simpa only [one_mul] using hshell)
  rw [hsplit eu heu, hsplit ec hec] at hmin
  rw [hsplit ep hep, hsplit t ht]
  linarith

end EinsteinFull.Regeneration
