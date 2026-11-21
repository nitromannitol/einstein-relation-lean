import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Integration of a shell energy comparison

An energy-minimizing function and a competitor equal to a comparison profile
on an inner set give an energy estimate in terms of shell errors.
-/

open MeasureTheory Set

namespace EinsteinFull.Regeneration

/-- Integrating the pointwise shell bound and canceling outer energy gives the
inner energy estimate. -/
theorem inner_energy_le_profile_add_shell_errors
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Q I : Set X)
    (hQ : MeasurableSet Q) (hI : MeasurableSet I) (hIQ : I ⊆ Q)
    (eu ep ec t s : X → ℝ) (α β : ℝ)
    (heu : IntegrableOn eu Q μ) (hep : IntegrableOn ep Q μ) (hec : IntegrableOn ec Q μ)
    (ht : IntegrableOn t (Q \ I) μ) (hs : IntegrableOn s (Q \ I) μ)
    (hmin : (∫ x in Q, eu x ∂μ) ≤ ∫ x in Q, ec x ∂μ)
    (hplateau : ∀ᵐ x ∂(μ.restrict I), ec x = ep x)
    (hshell : ∀ᵐ x ∂(μ.restrict (Q \ I)),
      ec x ≤ ep x + eu x + α * t x + β * s x) :
    (∫ x in I, eu x ∂μ) ≤ (∫ x in Q, ep x ∂μ) +
      α * (∫ x in Q \ I, t x ∂μ) + β * ∫ x in Q \ I, s x ∂μ := by
  have hshellmeas : MeasurableSet (Q \ I) := hQ.diff hI
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
      _ = _ := setIntegral_union hdis hshellmeas (hf.mono_set hIQ) (hf.mono_set sdiff_subset)
  have hplateau' : (∫ x in I, ec x ∂μ) = ∫ x in I, ep x ∂μ := integral_congr_ae hplateau
  have hsum : IntegrableOn (fun x => ep x + eu x + α * t x + β * s x) (Q \ I) μ :=
    (((hep.mono_set sdiff_subset).add (heu.mono_set sdiff_subset)).add (ht.const_mul α)).add
      (hs.const_mul β)
  have hbound := integral_mono_ae (hec.mono_set sdiff_subset) hsum hshell
  have hcalc : (∫ x in Q \ I, ec x ∂μ) ≤ (∫ x in Q \ I, ep x ∂μ) +
      (∫ x in Q \ I, eu x ∂μ) + α * (∫ x in Q \ I, t x ∂μ) +
        β * (∫ x in Q \ I, s x ∂μ) := by
    have heps : IntegrableOn ep (Q \ I) μ := hep.mono_set sdiff_subset
    have heus : IntegrableOn eu (Q \ I) μ := heu.mono_set sdiff_subset
    have h1 := integral_add ((heps.add heus).add (ht.const_mul α)) (hs.const_mul β)
    have h2 := integral_add (heps.add heus) (ht.const_mul α)
    have h3 := integral_add heps heus
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3, integral_const_mul, integral_const_mul] at hbound
    exact hbound
  rw [hsplit eu heu, hsplit ec hec, hplateau'] at hmin
  rw [hsplit ep hep]
  linarith

end EinsteinFull.Regeneration
