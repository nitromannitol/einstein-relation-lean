import EinsteinFull.Calculus.U6GMPEnvironmentRealization
import EinsteinFull.Calculus.U1SignedKernelBound
import EinsteinFull.Calculus.SunaS6GMPEnvironment

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- Under smooth bounds the measurable physical origin kernel has the GMP
realization and solves the martingale problem for the same path law. -/
theorem u1_gmp_physical_origin_law_and_mp_of_smooth_bounds
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd D.one_le_ellipticity Q lam h0 h1 K ∧
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω) := by
  obtain ⟨K, hK, hmp, hreal⟩ :=
    u6_physical_origin_kernel_with_smooth_gmp_identification
      hd D.one_le_ellipticity Q lam h0 h1
  refine ⟨K, hK, ?_, hmp⟩
  filter_upwards [hreal, Q.regular, hQ] with ω hr hreg hs
  exact ⟨hreg, hr hreg hs.1⟩

#print axioms u1_gmp_physical_origin_law_and_mp_of_smooth_bounds

/-- Every supplied regular GMP transition has a bounded normalized density. -/
theorem u1_supplied_gmp_transition_bounded_normalized_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (p : Vec d → Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, r.transitionKernel t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨M, p, hM, hp, hb, hi, hr⟩ :=
    u1_regular_signed_kernel_bounded_normalized_density hd ω lam Λ hΛ hω t ht
  refine ⟨M, p, hM, hp, hb, hi, ?_⟩
  intro x
  rw [s6_supplied_gmp_transition_eq_canonical_unconditional hd ω lam Λ hΛ hω h0 h1 r t]
  exact hr x

#print axioms u1_supplied_gmp_transition_bounded_normalized_density

/-- Killing the supplied path law can only decrease its endpoint measure. -/
theorem u1_supplied_killed_marginal_le_transition
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (U : Set (Vec d)) (t : ℝ≥0) (x : Vec d) :
    ((r.pathLaw x).restrict
      {γ : Path d | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ}).map
        (pathPosition t) ≤ r.transitionKernel t x := by
  rw [← r.pathLaw_endpoint t x]
  exact Measure.map_mono Measure.restrict_le_self (measurable_pathPosition t)

/-- Every positive-time killed marginal of the supplied law is volume-continuous. -/
theorem u1_supplied_killed_marginal_absolutelyContinuous
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (U : Set (Vec d)) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ((r.pathLaw x).restrict
      {γ : Path d | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ}).map
        (pathPosition t) ≪ (volume : Measure (Vec d)) := by
  apply (Measure.absolutelyContinuous_of_le
    (u1_supplied_killed_marginal_le_transition hd Λ hΛ ω hω lam h0 h1 r U t x)).trans
  rw [s6_supplied_gmp_transition_eq_canonical_unconditional hd ω lam Λ hΛ hω h0 h1 r t]
  exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x

/-- A single bounded normalized transition density dominates every killed marginal. -/
theorem u1_supplied_killed_marginal_bounded_density_majorant
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (U : Set (Vec d)) (t : ℝ≥0) (ht : 0 < t) :
    ∃ (M : ℝ) (p : Vec d → Vec d → ℝ), 0 < M ∧
      Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y ∧ p x y ≤ M) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, ((r.pathLaw x).restrict
        {γ : Path d | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ}).map
          (pathPosition t) ≤ volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨M, p, hM, hp, hb, hi, heq⟩ :=
    u1_supplied_gmp_transition_bounded_normalized_density hd ω lam Λ hΛ hω h0 h1 r t ht
  refine ⟨M, p, hM, hp, hb, hi, ?_⟩
  intro x
  rw [← heq x]
  exact u1_supplied_killed_marginal_le_transition hd Λ hΛ ω hω lam h0 h1 r U t x

#print axioms u1_supplied_killed_marginal_le_transition
#print axioms u1_supplied_killed_marginal_absolutelyContinuous
#print axioms u1_supplied_killed_marginal_bounded_density_majorant

end EinsteinFull
