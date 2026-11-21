import EllipticRegularity.Parabolic.Energy.Slab
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Stationary parabolic energy functions

A spatial weak-gradient pair defines a time-independent parabolic energy
function on any time set of finite measure.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A spatial energy function gives a stationary parabolic energy function. -/
noncomputable def stationaryParH1 {d : ℕ} (U : Set (PDE.Vec d)) (I : Set ℝ)
    [IsFiniteMeasure (volume.restrict I : Measure ℝ)] (v : PDE.Vec d → ℝ)
    (g : PDE.Vec d → PDE.Vec d) (hv : MemLp v 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hgrad : PDE.HasWeakGradientOn U v g) : PDE.ParH1Function U I where
  toFun := fun z => v z.1
  grad := fun z => g z.1
  memL2 := by
    rw [PDE.Parabolic.Energy.volume_restrict_prod]
    exact hv.comp_fst (volume.restrict I)
  gradMemL2 := fun i => by
    rw [PDE.Parabolic.Energy.volume_restrict_prod]
    exact (hg i).comp_fst (volume.restrict I)
  sliceWeakGradient := Filter.Eventually.of_forall fun _ => hgrad
  sliceL2loc := fun _ _ _ _ hKU => hv.mono_measure (Measure.restrict_mono_set volume hKU)
  weakCont := fun ψ _ => by
    change ContinuousOn (fun _ : ℝ => ∫ x in U, v x * ψ x) I
    exact continuousOn_const

end EinsteinFull.Regeneration
