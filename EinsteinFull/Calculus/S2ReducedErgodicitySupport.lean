import EinsteinFull.Calculus.ComplexGeneratorEnergySupport
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinFull.Frozen.ComplexGeneratorGraph
import EinsteinRelation.Environment.TranslationErgodicitySupport
import Mathlib.Order.Filter.CountableSeparatingOn

/-!
# Ergodicity of the reduced law and constancy of zero-gradient classes

Finite range and stationarity of the actual physical law give translation
ergodicity of the reduced law (the time change commutes with translations).
A complex `L²` class that is fixed by every translation is therefore constant,
and a class with zero actual horizontal gradient is fixed by every translation.
Zero horizontal Dirichlet energy forces zero gradient by ellipticity.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Translation-invariant events of the reduced law are trivial: the reduction
commutes with translations and the physical law is ergodic. -/
theorem reducedLaw_translation_ergodic {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) (A : Set (FieldPair d))
    (hA : MeasurableSet A)
    (hInv : ∀ z : Vec d, ∀ᵐ ω ∂reducedLaw Q, (translate z ω ∈ A ↔ ω ∈ A)) :
    reducedLaw Q A = 0 ∨ reducedLaw Q A = 1 := by
  have hm : Measurable (reduce : FieldPair d → FieldPair d) :=
    Probability.measurable_reduce
  have h1 : ∀ z : Vec d, ∀ᵐ ω ∂Q.measure,
      (translate z ω ∈ reduce ⁻¹' A ↔ ω ∈ reduce ⁻¹' A) := by
    intro z
    have hz : ∀ᵐ ω ∂Q.measure.map reduce, (translate z ω ∈ A ↔ ω ∈ A) := hInv z
    filter_upwards [ae_of_ae_map hm.aemeasurable hz] with ω hω
    simpa only [Set.mem_preimage, reduce_translate] using hω
  have h2 := Localization.environmentLaw_translation_ergodic Q hd (reduce ⁻¹' A) (hm hA) h1
  simpa only [reducedLaw, Measure.map_apply hm hA] using h2

/-- A complex `L²` class of the reduced law fixed by every translation is a constant. -/
theorem exists_const_of_complexTranslation_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : ∀ z : Vec d,
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z f = f) :
    ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c := by
  letI := reducedLaw_probability Q
  have hinv : ∀ z : Vec d, ∀ᵐ ω ∂reducedLaw Q, f (translate z ω) = f ω := by
    intro z
    filter_upwards [coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z f]
      with ω hω
    rw [hf z] at hω
    exact hω.symm
  have hsep : ∀ U : Set ℂ, MeasurableSet U →
      (∀ᶠ x in ae (reducedLaw Q), f x ∈ U) ∨ (∀ᶠ x in ae (reducedLaw Q), f x ∉ U) := by
    intro U hU
    have hmeas : MeasurableSet (f ⁻¹' U) := (Lp.stronglyMeasurable f).measurable hU
    have hI : ∀ z : Vec d, ∀ᵐ ω ∂reducedLaw Q,
        (translate z ω ∈ f ⁻¹' U ↔ ω ∈ f ⁻¹' U) := by
      intro z
      filter_upwards [hinv z] with ω hω
      simp only [Set.mem_preimage, hω]
    rcases reducedLaw_translation_ergodic Q hd (f ⁻¹' U) hmeas hI with h0 | h1
    · right
      have := measure_eq_zero_iff_ae_notMem.mp h0
      filter_upwards [this] with ω hω
      exact hω
    · left
      have hc : reducedLaw Q (f ⁻¹' U)ᶜ = 0 := (prob_compl_eq_zero_iff hmeas).mpr h1
      have := measure_eq_zero_iff_ae_notMem.mp hc
      filter_upwards [this] with ω hω
      exact not_not.mp hω
  exact exists_eventuallyEq_const_of_forall_separating MeasurableSet hsep

/-- Zero derivative of the translation orbit at the origin in a coordinate direction gives
a constant orbit along that direction. -/
theorem complexTranslation_unit_eq_of_derivative_zero {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (i : Fin d) (f : Lp ℂ 2 Q)
    (h : HasComplexHorizontalDerivative Q hQ i f 0) (t : ℝ) :
    complexTranslation Q hQ (t • unitVector i) f = f := by
  have hd : ∀ s : ℝ, HasDerivAt
      (fun r : ℝ => complexTranslation Q hQ (r • unitVector i) f) (0 : Lp ℂ 2 Q) s := by
    intro s
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hlim := ((complexTranslation Q hQ (s • unitVector i)).continuous.tendsto 0).comp h
    rw [map_zero] at hlim
    refine hlim.congr fun r => ?_
    have e1 : complexTranslation Q hQ ((s + r) • unitVector i) f =
        complexTranslation Q hQ (s • unitVector i)
          (complexTranslation Q hQ (r • unitVector i) f) := by
      rw [add_smul, complexTranslation_add]
    show complexTranslation Q hQ (s • unitVector i)
        ((r : ℂ)⁻¹ • (complexTranslation Q hQ (r • unitVector i) f - f)) =
      r⁻¹ • (complexTranslation Q hQ ((s + r) • unitVector i) f -
        complexTranslation Q hQ (s • unitVector i) f)
    rw [e1, map_smul, map_sub, ← Complex.ofReal_inv, Complex.coe_smul]
    rfl
  have hc := is_const_of_deriv_eq_zero
    (f := fun r : ℝ => complexTranslation Q hQ (r • unitVector i) f)
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [zero_smul, complexTranslation_zero] using hc

/-- A class with zero actual horizontal gradient is fixed by every translation. -/
theorem complexTranslation_eq_of_horizontalGradient_zero {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (f : Lp ℂ 2 Q)
    (h : HasComplexHorizontalGradient Q hQ f (fun _ => 0)) (x : Vec d) :
    complexTranslation Q hQ x f = f := by
  have hx : x = ∑ j, x j • unitVector j := by
    ext k
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  have key : ∀ s : Finset (Fin d),
      complexTranslation Q hQ (∑ j ∈ s, x j • unitVector j) f = f := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty, complexTranslation_zero]
    · intro a s ha ih
      rw [Finset.sum_insert ha, complexTranslation_add, ih]
      exact complexTranslation_unit_eq_of_derivative_zero Q hQ a f (h a) (x a)
  rw [hx]
  exact key Finset.univ

/-- A class with zero actual horizontal gradient is an a.e. constant on the reduced law. -/
theorem exists_const_of_horizontalGradient_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) (f : Lp ℂ 2 (reducedLaw Q))
    (h : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f
      (fun _ => 0)) :
    ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c :=
  exists_const_of_complexTranslation_eq Q hd f
    (complexTranslation_eq_of_horizontalGradient_zero _ _ f h)

/-- A family of `L²` classes with nonpositive sum of squared norms vanishes. -/
theorem eq_zero_of_sum_norm_sq_le_zero {d : ℕ} {Q : Measure (FieldPair d)}
    (G : Fin d → Lp ℂ 2 Q) (h : ∑ j, ‖G j‖ ^ 2 ≤ 0) : G = fun _ => 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg ‖G j‖)).mp (le_antisymm h
      (Finset.sum_nonneg fun j _ => sq_nonneg ‖G j‖))
  funext j
  have := hz j (Finset.mem_univ j)
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp this)

/-- Zero energy forces zero gradient, by ellipticity of the actual reduced coefficient. -/
theorem horizontalGradient_eq_zero_of_energy_eq_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (h : (∫ ω, (∑ j : Fin d, ∑ k : Fin d,
      (ω.1 0 j k : ℂ) * G k ω * star (G j ω)).re ∂reducedLaw Q) = 0) :
    G = fun _ => 0 := by
  have hE := integrable_reduced_complex_energy Q G G
  have hre : (∫ ω, (∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω).re ∂reducedLaw Q) =
      (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q).re :=
    integral_re hE
  have hpt : ∀ ω : FieldPair d, (∑ j : Fin d, ∑ k : Fin d,
      (ω.1 0 j k : ℂ) * G k ω * star (G j ω)) =
      ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω := fun ω =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have he : (∫ ω, (∑ j : Fin d, ∑ k : Fin d,
      (ω.1 0 j k : ℂ) * G k ω * star (G j ω)).re ∂reducedLaw Q) =
      (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q).re := by
    simp only [hpt]
    exact hre
  have hlow := reduced_complex_energy_lowerBound Q G
  rw [← he, h] at hlow
  have hK : 0 < (Real.exp (2 * Λ₀) * Λ₀)⁻¹ :=
    inv_pos.mpr (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))
  have hs : ∑ j, ‖G j‖ ^ 2 ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    exact absurd hlow (not_le.mpr (mul_pos hK hpos))
  exact eq_zero_of_sum_norm_sq_le_zero G hs

end EinsteinFull
