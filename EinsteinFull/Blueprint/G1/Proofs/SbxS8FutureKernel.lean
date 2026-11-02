import EinsteinFull.Blueprint.G1.Proofs.SbxS2FutureKernel
import EinsteinRelation.Regeneration.CouplingSpatialMaps

/-!
# The precise kernel-version boundary for future locality

Projecting the literal full-record measure recovers the actual killed path/coin
kernel on every fibre. The s2 stopped-kernel identity then applies to this
projection on one common environment-a.e. set. Full-record locality necessarily
gives local versions for the actual killed path/coin expectations and masses.
These are support results, not the leaf reduction `app:factorization#future-kernel`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Regeneration

/-- Forget only the restricted fields in the full record. -/
def sbxS8FuturePathBit {d : ℕ} (R : ℝ) (i : Fin d)
    (y : FutureState d i R) : CoupledSample d :=
  (y.1, y.2.1)

theorem sbxS8_measurable_futurePathBit {d : ℕ} (R : ℝ) (i : Fin d) :
    Measurable (sbxS8FuturePathBit R i) :=
  measurable_fst.prodMk measurable_snd.fst

/-- Projection recovers the entire original path and every coin at the origin. -/
theorem sbxS8_futurePathBit_origin {d : ℕ} (R : ℝ) (i : Fin d)
    (ω : FieldPair d) (z : CoupledSample d) :
    sbxS8FuturePathBit R i (spatialFutureRecord R i (0, ω) z) = z := by
  change ((recenterSample 0 z).1, z.2) = z
  rw [recenterSample_zero]

/-- Full-record locality necessarily gives locality of the actual killed
path/coin expectation. No analytic locality hypothesis is discharged here. -/
theorem sbxS8_pathBit_versions_of_future_versions {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d) (R : ℝ) (i : Fin d) :
    (∀ Φ : FutureState d i R → ℝ, Measurable Φ → BoundedRealTest Φ →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
        (fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q] B) →
      HasKilledPathBitFutureVersions Q i R K := by
  classical
  intro h F hF hbF
  obtain ⟨B, hB, he⟩ := h (F ∘ sbxS8FuturePathBit R i)
    (hF.comp (sbxS8_measurable_futurePathBit R i))
    ⟨hbF.choose, fun y => hbF.choose_spec _⟩
  refine ⟨B, hB, he.symm.trans ?_⟩
  apply Eventually.of_forall
  intro ω
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  simp only [killedFutureTest, Function.comp_apply, sbxS8_futurePathBit_origin]

/-- The actual origin path/coin law killed on no backtracking. The same
probability-part totalization as in the s2 full-record kernel is used. -/
def sbxS8KilledPathBitKernel {d : ℕ} (R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) : Kernel (FieldPair d) (CoupledSample d) :=
  (Probability.probabilityPart (originCoupledLaw K)).restrict
    ((measurableSet_NoBacktracking R i).preimage measurable_fst)

/-- Its integrals agree with the literal killed expectation on the given
origin probability fibres. There is no spatial-a.e. substitution at the origin. -/
theorem sbxS8_integral_killedPathBitKernel {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (F : CoupledSample d → ℝ) :
    (fun ω => ∫ z, F z ∂sbxS8KilledPathBitKernel R i K ω) =ᵐ[Q]
      fun ω => ∫ z, (if NoBacktracking R z.1 i then F z else 0) ∂K (0, ω) := by
  classical
  filter_upwards [hK.1] with ω hp
  have : IsProbabilityMeasure ((originCoupledLaw K) ω) := hp
  rw [sbxS8KilledPathBitKernel, Kernel.restrict_apply,
    Probability.probabilityPart_eq_of_isProbabilityMeasure,
    ← integral_indicator ((measurableSet_NoBacktracking R i).preimage measurable_fst)]
  rfl

/-- Forgetting the restricted fields in the literal full-record measure gives
exactly the actual killed path/coin measure, including totalized fibres. -/
theorem sbxS8_map_futurePathBit_killedFutureRecordLaw {d : ℕ}
    (R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d) (ω : FieldPair d) :
    (sbxS2KilledFutureRecordLaw R i K ω).map (sbxS8FuturePathBit R i) =
      sbxS8KilledPathBitKernel R i K ω := by
  rw [sbxS2KilledFutureRecordLaw,
    Measure.map_map (sbxS8_measurable_futurePathBit R i)
      (sbxS2_measurable_originFutureRecord R i ω)]
  have he : sbxS8FuturePathBit R i ∘ spatialFutureRecord R i (0, ω) = id :=
    funext (sbxS8_futurePathBit_origin R i ω)
  rw [he, Measure.map_id]
  rfl

/-- The actual projected kernel is the stopped path/coin kernel killed at the
inner barrier on a common environment-a.e. set, without any locality premise. -/
theorem sbxS8_killedPathBitKernel_stopped_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (R : ℝ) (hR : 0 < R) (i : Fin d) :
    ∀ᵐ ω ∂Q.measure,
      sbxS8KilledPathBitKernel R i K ω =
        (sbxS2StoppedOriginKernel R i K ω).restrict {z | NoBacktracking R z.1 i} := by
  filter_upwards [sbxS2_stoppedOriginKernel_restrict_of_coupling
    hd Q lam l δ h₀ h₁ P K hK R hR i] with ω he
  exact he.symm

/-- A full-record local version must in particular localize every measurable
set mass of the actual killed path/coin law. The witness may depend on the set. -/
theorem sbxS8_killedPathBit_masses_of_future_versions {d : ℕ}
    (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hlocal : ∀ Φ : FutureState d i R → ℝ, Measurable Φ → BoundedRealTest Φ →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
        (fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q] B)
    (S : Set (CoupledSample d)) (hS : MeasurableSet S) :
    ∃ B : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
      (fun ω => (sbxS8KilledPathBitKernel R i K ω S).toReal) =ᵐ[Q] B := by
  classical
  have hb : BoundedRealTest (S.indicator fun _ => (1 : ℝ)) := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, abs_one, le_refl]
    · simp only [Set.indicator_of_notMem hz, abs_zero, zero_le_one]
  obtain ⟨B, hB, he⟩ := (sbxS8_pathBit_versions_of_future_versions Q K R i hlocal)
    (S.indicator fun _ => (1 : ℝ)) (measurable_const.indicator hS) hb
  have hi := sbxS8_integral_killedPathBitKernel Q K hK R i
    (S.indicator fun _ => (1 : ℝ))
  simp only [integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one,
    Measure.real] at hi
  exact ⟨B, hB, hi.trans he.symm⟩

#print axioms sbxS8FuturePathBit
#print axioms sbxS8_measurable_futurePathBit
#print axioms sbxS8_futurePathBit_origin
#print axioms sbxS8_pathBit_versions_of_future_versions
#print axioms sbxS8KilledPathBitKernel
#print axioms sbxS8_integral_killedPathBitKernel
#print axioms sbxS8_map_futurePathBit_killedFutureRecordLaw
#print axioms sbxS8_killedPathBitKernel_stopped_of_coupling
#print axioms sbxS8_killedPathBit_masses_of_future_versions

#lint

end EinsteinFull.Blueprint
