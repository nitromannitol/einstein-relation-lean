import EinsteinFull.Calculus.C3CoarseSignedMeasurability
import EinsteinFull.Blueprint.G3.Proofs.C6CoarseIdentification
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
/-- Literal centering contracts the full matrix-clock error in Euclidean L². -/
theorem covarianceCoarse_actual_centering_L2_contraction :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ r : ℝ, D.dependenceRange ≤ r → ∀ x : Vec d,
      covarianceL2Size (reducedLaw Q)
        (fun ω (a : JointObservationIndex d) => match a with
          | .inl (j, k) =>
            (∫ z : Vec d, heatKernel 0 r z *
              commutatorObservation Q j k (translate (x-z) ω)) -
                covarianceCenteredCoarseEntry D Q r x j k ω
          | .inr _ => 0) ≤
      covarianceL2Size (reducedLaw Q)
        (fun ω (a : JointObservationIndex d) => match a with
          | .inl (j, k) =>
            (∫ z : Vec d, heatKernel 0 r z *
              commutatorObservation Q j k (translate (x-z) ω)) -
                covarianceCoarseEntry D Q r x j k ω
          | .inr _ => 0) := by
  classical
  intro d hd D Q hQ r hr x
  have hm := fun j k => coarseEntry_signed_aestronglyMeasurable d hd D Q hQ r hr x j k
  have hrp : 0 < r := lt_of_lt_of_le
    (lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange) hr
  let raw : FieldPair d → JointObservationIndex d → ℝ := fun ω a => match a with
    | .inl (j, k) => (∫ z : Vec d, heatKernel 0 r z *
        commutatorObservation Q j k (translate (x-z) ω)) -
          covarianceCoarseEntry D Q r x j k ω
    | .inr _ => 0
  let centered : FieldPair d → JointObservationIndex d → ℝ := fun ω a => match a with
    | .inl (j, k) => (∫ z : Vec d, heatKernel 0 r z *
        commutatorObservation Q j k (translate (x-z) ω)) -
          covarianceCenteredCoarseEntry D Q r x j k ω
    | .inr _ => 0
  have hraw : ∀ a, MemLp (fun ω => raw ω a) 2 (reducedLaw Q) := by
    rintro (⟨j, k⟩ | a)
    · exact (coarseCommutator_heatKernel_memLp_two Q j k x hrp).sub
        ((covarianceCoarse_entry_memLp_four hd D Q r hr x j k (hm j k)).mono_exponent
          (by norm_num : (2 : ENNReal) ≤ 4))
    · exact memLp_const (0 : ℝ)
  have hcentered : ∀ a, MemLp (fun ω => centered ω a) 2 (reducedLaw Q) := by
    rintro (⟨j, k⟩ | a)
    · exact (coarseCommutator_heatKernel_memLp_two Q j k x hrp).sub
        (covarianceCoarse_centered_entry_memLp_two hd D Q r hr x j k (hm j k))
    · exact memLp_const (0 : ℝ)
  change covarianceL2Size (reducedLaw Q) centered ≤ covarianceL2Size (reducedLaw Q) raw
  unfold covarianceL2Size covarianceVectorSize
  rw [(coarseFiniteVector_secondMoment hcentered).2,
    (coarseFiniteVector_secondMoment hraw).2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro a _
  rcases a with ⟨j, k⟩ | a
  · exact covarianceCoarse_centered_error_secondMoment_le hd D Q r hr x j k (hm j k)
  · exact le_rfl
#print axioms covarianceCoarse_actual_centering_L2_contraction
#lint

-- Include generated auxiliary declarations in the transitive axiom check.
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound,
          ``EinsteinFull.External.akm_averaged_corrector,
          ``EinsteinFull.External.akm_coarsened_coefficient_estimates].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      count := count + 1
  Lean.logInfo m!"Approved-axiom audit passed for all {count} local declarations."

end EinsteinFull.Blueprint
