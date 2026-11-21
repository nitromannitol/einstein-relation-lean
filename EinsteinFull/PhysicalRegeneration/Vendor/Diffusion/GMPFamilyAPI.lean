import EinsteinRelation.Diffusion.GMPFamilyAPI
import EinsteinFull.Regeneration.PhysicalKernelPredicate

/-!
# Physical-kernel version of
`EinsteinRelation.Diffusion.GMPFamilyAPI`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal
open EinsteinRelation.External.GantertSection7Support (GantertFixedEnvironmentRealization)
namespace EinsteinRelation
/-- Every spatial path law of a fixed-environment realization is a probability measure, since
the path law is a Markov kernel. -/
private theorem isProbabilityMeasure_pathLaw {d : ℕ} {hd : 2 ≤ d} {Λ₀ : ℝ} {hΛ₀ : 1 ≤ Λ₀}
    {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1) (x : Vec d) :
    IsProbabilityMeasure (r.pathLaw x) :=
  r.pathLaw_isMarkovKernel.isProbabilityMeasure x

/-- A one-time marginal of a fixed-environment realization at a positive time is absolutely
continuous with respect to Lebesgue measure. The marginal is the transition kernel
(`pathLaw_endpoint`), which is the heat-kernel density measure
(`transitionKernel_eq_heatKernel`). -/
private theorem map_pathPosition_absolutelyContinuous {d : ℕ} {hd : 2 ≤ d} {Λ₀ : ℝ}
    {hΛ₀ : 1 ≤ Λ₀} {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ} {h0 : 0 ≤ lam}
    {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1) (t : ℝ≥0) (ht : 0 < t)
    (x : Vec d) :
    (r.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
  rw [r.pathLaw_endpoint t x, r.transitionKernel_eq_heatKernel t ht x]
  exact withDensity_absolutelyContinuous _ _

/-- The physical-kernel version of `EinsteinRelation.isProbabilityMeasure_of_isGMPReducedKernel`. -/
theorem isProbabilityMeasure_of_isGMPReducedKernel_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
  unfold EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound at hP
  filter_upwards [hP] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  intro x
  rw [hr x]
  exact isProbabilityMeasure_pathLaw r x

/-- The physical-kernel version of
`EinsteinRelation.map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel`. -/
theorem map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd hΛ₀ Q lam h0 h1 P) :
    ∀ t : ℝ≥0, 0 < t →
      ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        (P (x, ω)).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
  intro t ht
  unfold EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound at hP
  filter_upwards [hP] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  intro x
  rw [hr x]
  exact map_pathPosition_absolutelyContinuous r t ht x

end EinsteinRelation
