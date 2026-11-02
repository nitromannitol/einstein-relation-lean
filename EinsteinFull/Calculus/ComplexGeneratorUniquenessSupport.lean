import EinsteinFull.Calculus.ComplexHorizontalDensitySupport
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Frozen.ComplexGeneratorGraph
import EinsteinFull.Frozen.ReducedLawProbability

/-!
# Functionality of the full complex stationary generator graph

The strong gradient is unique. Testing the full weak graph on conjugates of
the actual horizontal H1 domain and using its L2 value density then proves
uniqueness of the generator output, for every complex force.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull

open EinsteinRelation

/-- The actual strong horizontal gradient has a unique value. -/
theorem HasComplexHorizontalGradient.unique {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {f : Lp ℂ 2 Q} {G H : Fin d → Lp ℂ 2 Q}
    (hG : HasComplexHorizontalGradient Q hQ f G)
    (hH : HasComplexHorizontalGradient Q hQ f H) : G = H :=
  funext fun i => (hG i).unique (hH i)

private theorem inner_eq_integral_mul_star {d : ℕ} (Q : Measure (FieldPair d))
    (u g : Lp ℂ 2 Q) :
    inner ℂ u g = ∫ ω, g ω * (star u) ω ∂Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with ω hω
  change (star u) ω = star (u ω) at hω
  simp only [hω, RCLike.inner_apply, Complex.star_def]

/-- Testing the full actual H1 domain determines an L2 output uniquely. -/
theorem eq_zero_of_complexHorizontalH1_inner_eq_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℂ 2 Q)
    (hf : ∀ (u : Lp ℂ 2 Q) (G : Fin d → Lp ℂ 2 Q),
      HasComplexHorizontalGradient Q hQ u G → inner ℂ u f = 0) : f = 0 := by
  obtain ⟨u, hu, ht⟩ := exists_complexHorizontalGradient_approximation Q hQ f
  have heq : (fun n => inner ℂ (u n) f) = fun _ => (0 : ℂ) := by
    funext n
    obtain ⟨G, hG⟩ := hu n
    exact hf (u n) G hG
  have hlim := ht.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))
  have hzero : Tendsto (fun n => inner ℂ (u n) f) atTop (𝓝 (0 : ℂ)) := by
    rw [heq]
    exact tendsto_const_nhds
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (tendsto_nhds_unique hlim hzero)

/-- For every complex force, the full weak generator graph has a unique output. -/
theorem IsComplexGeneratorPair.unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g h : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (hfh : IsComplexGeneratorPair Q i ζ f h) : g = h := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨G, hG, hweakG⟩ := hfg
  obtain ⟨H, hH, hweakH⟩ := hfh
  have hGH := hG.unique hH
  subst H
  apply sub_eq_zero.mp
  apply eq_zero_of_complexHorizontalH1_inner_eq_zero (reducedLaw Q) (reducedLaw_stationary Q)
  intro u Gu hGu
  have hstar : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (star u) (fun j => star (Gu j)) := fun j => (hGu j).star
  have hp := (hweakG (star u) (fun j => star (Gu j)) hstar).trans
    (hweakH (star u) (fun j => star (Gu j)) hstar).symm
  rw [← inner_eq_integral_mul_star, ← inner_eq_integral_mul_star] at hp
  rw [inner_sub_right, hp, sub_self]

end EinsteinFull
