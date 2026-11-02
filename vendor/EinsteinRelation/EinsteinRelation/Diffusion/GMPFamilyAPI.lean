import EinsteinRelation.Diffusion.GMPFamily
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.Basic

/-! # Almost-sure properties of the GMP Section 7 origin laws

A kernel that realizes the physical or reduced origin law of one force, as in
`IsGMPPhysicalOriginLaw` and `IsGMPReducedOriginLaw`, is for almost every environment a
probability measure on paths started at the origin. Its one-time marginals at positive times
are absolutely continuous with respect to Lebesgue measure, because they are heat-kernel
densities. The reduced kernel `IsGMPReducedKernel` gives the same conclusions from every
starting point at once.
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

/-- The path law of a fixed-environment realization started at the origin sends almost every
path to the value `0` at time `0`, by `pathLaw_starts_at`. -/
private theorem ae_pathLaw_zero {d : ℕ} {hd : 2 ≤ d} {Λ₀ : ℝ} {hΛ₀ : 1 ≤ Λ₀}
    {ω : FieldPair d} {hω : IsRegular Λ₀ ω} {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1) :
    ∀ᵐ (γ : Path d) ∂r.pathLaw 0, γ 0 = 0 := by
  filter_upwards [r.pathLaw_starts_at 0] with γ hγ
  exact hγ

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

/-- For almost every environment, the physical origin law of one force is a probability measure
on paths. -/
theorem isProbabilityMeasure_of_isGMPPhysicalOriginLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hK : IsGMPPhysicalOriginLaw hd hΛ₀ Q lam h0 h1 K) :
    ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (K ω) := by
  unfold IsGMPPhysicalOriginLaw at hK
  filter_upwards [hK] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  rw [hr]
  exact isProbabilityMeasure_pathLaw r 0

/-- For almost every environment, the physical origin law of one force starts at the origin:
almost every path under `K ω` has value `0` at time `0`. -/
theorem ae_ae_path_zero_of_isGMPPhysicalOriginLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hK : IsGMPPhysicalOriginLaw hd hΛ₀ Q lam h0 h1 K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ (γ : Path d) ∂K ω, γ 0 = 0 := by
  unfold IsGMPPhysicalOriginLaw at hK
  filter_upwards [hK] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  rw [hr]
  exact ae_pathLaw_zero r

/-- For almost every environment, the one-time marginals of the physical origin law of one force
are absolutely continuous with respect to Lebesgue measure at every positive time. -/
theorem map_pathPosition_absolutelyContinuous_of_isGMPPhysicalOriginLaw {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (K : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hK : IsGMPPhysicalOriginLaw hd hΛ₀ Q lam h0 h1 K) :
    ∀ t : ℝ≥0, 0 < t →
      ∀ᵐ ω ∂Q.measure, (K ω).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
  intro t ht
  unfold IsGMPPhysicalOriginLaw at hK
  filter_upwards [hK] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  rw [hr]
  exact map_pathPosition_absolutelyContinuous r t ht 0

/-- For almost every environment, the reduced origin law of one force is a probability measure
on paths. -/
theorem isProbabilityMeasure_of_isGMPReducedOriginLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hK : IsGMPReducedOriginLaw hd hΛ₀ Q lam h0 h1 K) :
    ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (K ω) := by
  unfold IsGMPReducedOriginLaw at hK
  filter_upwards [hK] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  rw [hr]
  exact isProbabilityMeasure_pathLaw r 0

/-- For almost every environment, the reduced origin law of one force starts at the origin:
almost every path under `K ω` has value `0` at time `0`. -/
theorem ae_ae_path_zero_of_isGMPReducedOriginLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hK : IsGMPReducedOriginLaw hd hΛ₀ Q lam h0 h1 K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ (γ : Path d) ∂K ω, γ 0 = 0 := by
  unfold IsGMPReducedOriginLaw at hK
  filter_upwards [hK] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  rw [hr]
  exact ae_pathLaw_zero r

/-- For almost every environment, the one-time marginals of the reduced origin law of one force
are absolutely continuous with respect to Lebesgue measure at every positive time. -/
theorem map_pathPosition_absolutelyContinuous_of_isGMPReducedOriginLaw {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (K : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hK : IsGMPReducedOriginLaw hd hΛ₀ Q lam h0 h1 K) :
    ∀ t : ℝ≥0, 0 < t →
      ∀ᵐ ω ∂Q.measure, (K ω).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
  intro t ht
  unfold IsGMPReducedOriginLaw at hK
  filter_upwards [hK] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  rw [hr]
  exact map_pathPosition_absolutelyContinuous r t ht 0

/-- For almost every environment, the reduced quenched kernel of one force is a probability
measure from every starting point. -/
theorem isProbabilityMeasure_of_isGMPReducedKernel {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
  unfold IsGMPReducedKernel at hP
  filter_upwards [hP] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  intro x
  rw [hr x]
  exact isProbabilityMeasure_pathLaw r x

/-- For almost every environment, the one-time marginals of the reduced quenched kernel of one
force are absolutely continuous with respect to Lebesgue measure from every starting point, at
every positive time. -/
theorem map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (hP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P) :
    ∀ t : ℝ≥0, 0 < t →
      ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        (P (x, ω)).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
  intro t ht
  unfold IsGMPReducedKernel at hP
  filter_upwards [hP] with ω hω
  obtain ⟨_, r, hr⟩ := hω
  intro x
  rw [hr x]
  exact map_pathPosition_absolutelyContinuous r t ht x

end EinsteinRelation
