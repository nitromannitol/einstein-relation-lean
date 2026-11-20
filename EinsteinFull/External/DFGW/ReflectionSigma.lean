import EinsteinFull.External.DFGW.Trajectory

/-! # Time reversal and coordinate sigma-algebras

Reflection at time zero exchanges the past and future coordinate sigma-algebras.
-/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

omit [BorelSpace S] in
/-- Reflection at time zero pulls the past coordinate sigma-algebra back to the future. -/
theorem comap_refl_past :
    MeasurableSpace.comap (Draft.dfgwRefl (S := S) 0)
      (Draft.dfgwCoordSigma (Set.Iic 0)) = Draft.dfgwCoordSigma (Set.Ici 0) := by
  simp only [Draft.dfgwCoordSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
    Function.comp_def, Draft.dfgwRefl, ContinuousMap.coe_comp, ContinuousMap.coe_mk, mul_zero]
  change (⨆ u ∈ Set.Iic (0 : ℝ), MeasurableSpace.comap
    (fun η : C(ℝ, S) => η (0 - u)) inferInstance) =
      ⨆ u ∈ Set.Ici (0 : ℝ), MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance
  apply le_antisymm
  · refine iSup₂_le fun u hu => ?_
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ Set.Ici (0 : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance) (0 - u)
      (by change 0 ≤ 0 - u; change u ≤ 0 at hu; linarith) le_rfl
  · refine iSup₂_le fun u hu => ?_
    have h : -u ∈ Set.Iic (0 : ℝ) := by change -u ≤ 0; change 0 ≤ u at hu; linarith
    convert le_iSup₂_of_le (f := fun v (_ : v ∈ Set.Iic (0 : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η (0 - v)) inferInstance) (-u) h le_rfl using 1
    simp

omit [MeasurableSpace S] [BorelSpace S] in
/-- Reflection at time zero is an involution. -/
theorem refl_zero_involutive : Function.Involutive (Draft.dfgwRefl (S := S) 0) := by
  intro η
  ext u
  simp only [Draft.dfgwRefl, ContinuousMap.coe_comp, ContinuousMap.coe_mk, Function.comp_apply]
  congr 1
  ring

omit [MeasurableSpace S] [BorelSpace S] in
/-- Time reversal conjugates a shift to the shift in the opposite direction. -/
theorem refl_zero_shift (u : ℝ) (η : C(ℝ, S)) :
    Draft.dfgwRefl 0 (Draft.dfgwShift u η) = Draft.dfgwShift (-u) (Draft.dfgwRefl 0 η) := by
  ext v
  simp only [Draft.dfgwRefl, Draft.dfgwShift, ContinuousMap.coe_comp, ContinuousMap.coe_mk,
    Function.comp_apply]
  congr 1
  ring

end EinsteinFull.External.DFGW
