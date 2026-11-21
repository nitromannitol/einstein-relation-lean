import EinsteinFull.External.DFGW.FutureCylinderState

/-! # Closed space of state-determined past projections

The observables whose past projections are determined by the current state form a closed
linear subspace. Every bounded future cylinder belongs to it.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Projection onto current-state observables. -/
noncomputable def stateProjection (P : Measure C(ℝ, S)) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (lpMeas ℝ ℝ (MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance) 2 P).subtypeL.comp
    (condExpL2 ℝ ℝ (continuous_eval_const (0 : ℝ)).measurable.comap_le)

/-- Projection onto past observables. -/
noncomputable def pastProjection (P : Measure C(ℝ, S)) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (lpMeas ℝ ℝ (Draft.dfgwCoordSigma (Set.Iic 0)) 2 P).subtypeL.comp
    (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le 0))

/-- Observables whose past projection is determined by the current state. -/
noncomputable def stateDeterminedPast (P : Measure C(ℝ, S)) : Submodule ℝ (Lp ℝ 2 P) :=
  ((stateProjection P).comp (pastProjection P)).eqLocus (pastProjection P)

/-- The observables whose past projection is state determined form a closed subspace. -/
theorem isClosed_stateDeterminedPast (P : Measure C(ℝ, S)) :
    IsClosed (stateDeterminedPast P : Set (Lp ℝ 2 P)) := by
  exact isClosed_eq ((stateProjection P).comp (pastProjection P)).continuous
    (pastProjection P).continuous

/-- Every admissible finite future cylinder has a state-determined past projection. -/
theorem futureCylinder_mem_stateDeterminedPast (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (xs : List (ℝ≥0 × (S → ℝ))) (hxs : FutureCylinderAdmissible xs) :
    (futureCylinder_memLp hP xs hxs 0).toLp (futureCylinder xs 0) ∈ stateDeterminedPast P := by
  let z := (futureCylinder_memLp hP xs hxs 0).toLp (futureCylinder xs 0)
  let : Fact (MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S)) :=
    ⟨(continuous_eval_const (0 : ℝ)).measurable.comap_le⟩
  let K := lpMeas ℝ ℝ (MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance) 2 P
  have hm : pastProjection P z ∈ K := by
    apply mem_lpMeas_iff_aestronglyMeasurable.mpr
    exact condExpL2_futureCylinder_state_measurable hP xs hxs
  change stateProjection P (pastProjection P z) = pastProjection P z
  change ((K.orthogonalProjectionOnto (pastProjection P z) : K) : Lp ℝ 2 P) = _
  exact congrArg (fun w : K => (w : Lp ℝ 2 P))
    (K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨pastProjection P z, hm⟩)

end EinsteinFull.External.DFGW
