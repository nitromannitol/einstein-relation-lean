import EinsteinRelation.Correctors.ParabolicFluxEnergyIdentity

/-! # Weak parabolic equations with independent flux

Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof.
These energy classes retain the actual scalar field, spatial gradient,
and distributional equation, while allowing the sign of the flux to vary.
-/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A local spatial energy class solving `∂ₜu = div F`. -/
structure IsParabolicFluxSolution {d : ℕ} (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G F : ℝ × Vec d → Vec d) : Prop where
  scalar_memLp : MemLp u 2 (volume.restrict (I ×ˢ U))
  gradient_memLp : ∀ j, MemLp (fun z => G z j) 2 (volume.restrict (I ×ˢ U))
  weak_gradient : ∀ᵐ t ∂volume.restrict I,
    HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x))
  flux_memLp : ∀ j, MemLp (fun z => F z j) 2 (volume.restrict (I ×ˢ U))
  weak_equation : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
    HasCompactSupport ψ → tsupport ψ ⊆ interior I ×ˢ U →
    (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1,0) +
      dot (F z) (fun j => fderiv ℝ ψ z (0,unitVector j))) = 0

/-- Every original parabolic solution has its actual coefficient flux.
Source: `paper/main.tex:787–792,850`. -/
theorem parabolicFluxSolution_of_parabolicSolution {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsParabolicSolution A I U u G) :
    IsParabolicFluxSolution I U u G (fun z => (A z.2).mulVec (G z)) :=
  ⟨h.1, parabolicSolution_gradient_coordinate_memLp h, h.2.2.2.1,
    parabolicSolution_flux_coordinate_memLp hK A h, h.2.2.2.2⟩

/-- Smooth compact tests have integrable temporal and spatial pairings.
Source: `paper/main.tex:787–792,850`. -/
theorem IsParabolicFluxSolution.test_integrable {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G F : ℝ × Vec d → Vec d}
    (h : IsParabolicFluxSolution I U u G F)
    {ψ : ℝ × Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => -(u z) * fderiv ℝ ψ z (1,0) +
      dot (F z) (fun j => fderiv ℝ ψ z (0,unitVector j)))
      (volume.restrict (I ×ˢ U)) := by
  have hD (v : ℝ × Vec d) : MemLp (fun z => fderiv ℝ ψ z v) 2
      (volume.restrict (I ×ˢ U)) :=
    (((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport (hψc.fderiv_apply ℝ v)).mono_measure
        Measure.restrict_le_self
  simpa only [neg_mul, Pi.neg_apply, Pi.mul_apply, Pi.add_apply, dot] using
    ((h.scalar_memLp.integrable_mul (hD (1,0))).neg).add
      (integrable_finset_sum Finset.univ fun j _ =>
        (h.flux_memLp j).integrable_mul (hD (0,unitVector j)))

/-- Subtracting independent weak flux equations preserves the energy class.
Source: `paper/main.tex:787–792,850`. -/
theorem IsParabolicFluxSolution.sub {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {u v : ℝ × Vec d → ℝ} {G H F J : ℝ × Vec d → Vec d}
    (hu : IsParabolicFluxSolution I U u G F)
    (hv : IsParabolicFluxSolution I U v H J) :
    IsParabolicFluxSolution I U (fun z => u z - v z)
      (fun z => G z - H z) (fun z => F z - J z) := by
  refine ⟨hu.scalar_memLp.sub hv.scalar_memLp,
    fun j => (hu.gradient_memLp j).sub (hv.gradient_memLp j), ?_,
    fun j => (hu.flux_memLp j).sub (hv.flux_memLp j), ?_⟩
  · filter_upwards [hu.weak_gradient, hv.weak_gradient] with t ht hs
    exact hasWeakGradient_sub ht hs
  · intro ψ hψ hψc hψs
    have hsplit (z : ℝ × Vec d) :
        -(u z - v z) * fderiv ℝ ψ z (1,0) +
          dot (F z - J z) (fun j => fderiv ℝ ψ z (0,unitVector j)) =
        (-(u z) * fderiv ℝ ψ z (1,0) +
          dot (F z) (fun j => fderiv ℝ ψ z (0,unitVector j))) -
        (-(v z) * fderiv ℝ ψ z (1,0) +
          dot (J z) (fun j => fderiv ℝ ψ z (0,unitVector j))) := by
      simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    simp_rw [hsplit]
    rw [integral_sub (hu.test_integrable hψ hψc) (hv.test_integrable hψ hψc),
      hu.weak_equation ψ hψ hψc hψs, hv.weak_equation ψ hψ hψc hψs, sub_self]

/-- The proved compact energy identity applies to an independent flux.
Source: `paper/main.tex:787–792,850`. -/
theorem IsParabolicFluxSolution.energy_identity {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G F : ℝ × Vec d → Vec d}
    (h : IsParabolicFluxSolution I U u G F)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζs : tsupport ζ ⊆ interior I ×ˢ U) :
    Integrable (fun z => dot (F z)
      (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0,unitVector j)))
      (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, dot (F z)
      (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0,unitVector j))) =
        ∫ z in I ×ˢ U, (u z)^2 * ζ z * fderiv ℝ ζ z (1,0) :=
  parabolicFlux_energy_identity hI hU h.scalar_memLp h.gradient_memLp h.weak_gradient
    h.flux_memLp h.weak_equation hζ hζc hζs

end EinsteinRelation.Correctors
