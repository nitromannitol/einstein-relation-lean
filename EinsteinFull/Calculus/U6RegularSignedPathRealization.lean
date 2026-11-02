import EinsteinFull.Calculus.U2GMPFinalEnvironment

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- The signed regular physical transition kernel has a continuous-path
realization with its actual finite-dimensional distributions. -/
theorem u6_regular_signed_continuous_kernel_exists
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ K : Kernel (Vec d) (Path d), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0,
        K.map (ContinuousPath.finsetEvaluation I) =
          finiteSetKernel (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  apply u6_regular_continuous_kernel_of_volume_ac hd ω lam Λ hΛ hω
  intro t ht
  exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht

/-- One measurable origin kernel realizes the regular GMP law and solves the
physical martingale problem on the same almost-everywhere fibers. -/
theorem u6_foundation_regular_signed_origin_law_and_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K ∧
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω) := by
  apply u2_foundation_gmp_physical_origin_law_and_mp_of_kernel_ac hd hΛ Q lam h0 h1
  filter_upwards with ω hω t ht
  exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht

#print axioms u6_regular_signed_continuous_kernel_exists
#print axioms u6_foundation_regular_signed_origin_law_and_mp

end EinsteinFull
