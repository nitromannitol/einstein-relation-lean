import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.FiniteTimeIntegralSupport

/-!
# The full generator graph of the finite-time corrector

For every L2 datum, its integrated continuous semigroup orbit belongs to the
full unforced generator domain. The positive resolvent recovers the actual weak
graph, including the horizontal gradient and every horizontal H1 test.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Integrating the output orbit of a full generator pair gives the orbit increment. -/
theorem IsComplexEnvironmentSemigroup.integral_generator_orbit
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (τ : ℝ≥0) :
    (∫ r in Icc (0 : ℝ) (τ : ℝ), P r.toNNReal g) = P τ f - f := by
  have hu := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv := (hP.2.2.1 g).comp continuous_real_toNNReal
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (a := (0 : ℝ)) (b := (τ : ℝ)) τ.property hu.continuousOn
    (fun r hr => (hP.hasDerivWithinAt_orbit hfg r hr.1.le).mono Ioi_subset_Ici_self)
    (hv.intervalIntegrable 0 τ)
  calc
    _ = (∫ r in (0 : ℝ)..(τ : ℝ), P r.toNNReal g) :=
      integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le τ.property).symm
    _ = _ := by
      simpa only [Function.comp_apply, Real.toNNReal_coe, Real.toNNReal_zero, hP.1,
        ContinuousLinearMap.id_apply] using hi

/-- Every complete unforced semigroup commutes with the actual positive resolvent. -/
theorem IsComplexEnvironmentSemigroup.unforced_resolvent_apply
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (s : ℝ) (hs : 0 < s) (τ : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    unforcedComplexResolvent Q i s hs (P τ f) =
      P τ (unforcedComplexResolvent Q i s hs f) := by
  apply IsComplexGeneratorPair.unforced_resolvent_unique hs
    (unforcedComplexResolvent_spec Q i s hs (P τ f))
  simpa only [map_sub, map_smul] using
    hP.map_generator (unforcedComplexResolvent_spec Q i s hs f) τ

/-- The integral of any L2 orbit belongs to the actual full unforced generator graph.
No generator-domain hypothesis is imposed on the initial datum. -/
theorem IsComplexEnvironmentSemigroup.integral_orbit_graph
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) :
    IsComplexGeneratorPair Q i 0
      (∫ r in Icc (0 : ℝ) (τ : ℝ), P r.toNNReal f) (P τ f - f) := by
  let R := unforcedComplexResolvent Q i 1 zero_lt_one
  have hc (t : ℝ≥0) : R (P t f) = P t (R f) :=
    hP.unforced_resolvent_apply 1 zero_lt_one t f
  have hfint := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (τ : ℝ)
  have hRfint := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 (R f)) (τ : ℝ)
  have hRint : (∫ r in Icc (0 : ℝ) (τ : ℝ), P r.toNNReal (R f)) =
      R (∫ r in Icc (0 : ℝ) (τ : ℝ), P r.toNNReal f) := by
    simp_rw [← hc]
    exact R.integral_comp_comm hfint
  have hfg : IsComplexGeneratorPair Q i 0 (R f) (R f - f) := by
    simpa only [Complex.ofReal_one, one_smul] using
      unforcedComplexResolvent_spec Q i 1 zero_lt_one f
  have hi := hP.integral_generator_orbit hfg τ
  simp_rw [map_sub] at hi
  rw [integral_sub hRfint hfint, hRint, ← hc] at hi
  apply (isComplexGeneratorPair_iff_resolvent Q i 1 zero_lt_one _ _).mpr
  change R ((1 : ℂ) • _ - (P τ f - f)) = _
  rw [one_smul, map_sub, map_sub, ← hi, sub_sub_cancel]

/-- The literal frozen finite-time corrector satisfies its full unforced generator equation. -/
theorem IsComplexEnvironmentSemigroup.finiteTimeCorrector_graph
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (j : Fin d) :
    IsComplexGeneratorPair Q i 0 (finiteTimeCorrector Q P hP.2.2.1 β τ j)
      (P τ (β j) - β j) :=
  hP.integral_orbit_graph (β j) τ

end EinsteinFull
