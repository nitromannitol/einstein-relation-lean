import EinsteinFull.External.DFGW.ShiftedMarkov

/-! # Shifted past sigma-algebras

A time shift transports the coordinate past at any real time to the corresponding shifted past.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

omit [BorelSpace S] in
/-- Pulling back the past through a time shift moves the endpoint by the same amount. -/
theorem comap_shift_past_at (s τ : ℝ) :
    MeasurableSpace.comap (Draft.dfgwShift (S := S) τ)
      (Draft.dfgwCoordSigma (Set.Iic s)) = Draft.dfgwCoordSigma (Set.Iic (s + τ)) := by
  simp only [Draft.dfgwCoordSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  change (⨆ u ∈ Set.Iic s, MeasurableSpace.comap
    (fun η : C(ℝ, S) => η (u + τ)) inferInstance) =
      ⨆ u ∈ Set.Iic (s + τ), MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance
  apply le_antisymm
  · refine iSup₂_le fun u hu => ?_
    change u ≤ s at hu
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Iic (s + τ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) (u + τ)
      (by change u + τ ≤ s + τ; linarith) le_rfl
  · refine iSup₂_le fun u hu => ?_
    change u ≤ s + τ at hu
    have h : u - τ ∈ Set.Iic s := by change u - τ ≤ s; linarith
    have ht : u - τ + τ = u := by ring
    convert le_iSup₂_of_le (f := fun v (_ : v ∈ Set.Iic s) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η (v + τ)) inferInstance) (u - τ) h le_rfl using 1
    rw [ht]

end EinsteinFull.External.DFGW
