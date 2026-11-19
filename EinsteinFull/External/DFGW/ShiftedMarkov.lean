import EinsteinFull.External.DFGW.Trajectory
import EinsteinFull.Calculus.CLCondExpPushforward

/-! # Time-shifted Markov property

Stationarity transports the Markov property at time zero to arbitrary deterministic times.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

omit [BorelSpace S] in
/-- Pulling the past sigma-algebra back through a time shift moves its endpoint. -/
theorem comap_shift_past (s : ℝ) :
    MeasurableSpace.comap (Draft.dfgwShift (S := S) s)
      (Draft.dfgwCoordSigma (Set.Iic 0)) = Draft.dfgwCoordSigma (Set.Iic s) := by
  simp only [Draft.dfgwCoordSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  change (⨆ u ∈ Set.Iic (0 : ℝ), MeasurableSpace.comap
    (fun η : C(ℝ, S) => η (u + s)) inferInstance) =
      ⨆ u ∈ Set.Iic s, MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance
  apply le_antisymm
  · refine iSup₂_le fun u hu => ?_
    change u ≤ 0 at hu
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic s) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) (u + s)
      (by change u + s ≤ s; linarith [hu]) le_rfl
  · refine iSup₂_le fun u hu => ?_
    change u ≤ s at hu
    have h : u - s ∈ Set.Iic (0 : ℝ) := by change u - s ≤ 0; linarith [hu]
    have ht : u - s + s = u := by ring
    convert le_iSup₂_of_le (f := fun v (_ : v ∈ Set.Iic (0 : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η (v + s)) inferInstance) (u - s) h le_rfl using 1
    rw [ht]

/-- The Markov conditional expectation at any deterministic time. -/
theorem condExp_shifted (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s : ℝ) (t : ℝ≥0) (f : S → ℝ) (hf : Measurable f)
    (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    P[fun η : C(ℝ, S) => f (η ((t : ℝ) + s)) |
      Draft.dfgwCoordSigma (Set.Iic s)] =ᵐ[P]
      fun η => ∫ y, f y ∂T t (η s) := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨C, hC⟩ := hfb
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le 0
  have hi : Integrable (fun η : C(ℝ, S) => f (η t)) P :=
    Integrable.of_bound (hf.comp (continuous_eval_const (t : ℝ)).measurable).aestronglyMeasurable
      C (ae_of_all P fun η => by simpa only [Real.norm_eq_abs] using hC (η t))
  have hi' : Integrable (fun η : C(ℝ, S) => f (η t)) (P.map (Draft.dfgwShift s)) := by
    rw [hP.stationary]
    exact hi
  have hc := EinsteinFull.condExp_map_comp (measurable_shift (S := S) s) hσ hi'
  rw [hP.stationary, comap_shift_past s] at hc
  have hm := hP.markov t f hf ⟨C, hC⟩
  have hp : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hm' := hp.quasiMeasurePreserving.ae hm
  filter_upwards [hc, hm'] with η hcη hmη
  simpa only [Function.comp_def, Draft.dfgwShift, ContinuousMap.coe_comp,
    ContinuousMap.coe_mk, zero_add] using hcη.symm.trans hmη

end EinsteinFull.External.DFGW
