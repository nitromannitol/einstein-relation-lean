import EinsteinRelation.Correctors.GTBallRegularRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Source: `paper/main.tex:694-704,735-737`. Continuous value and
gradient representatives inherit the actual Fréchet derivative from
local GT representatives, by uniqueness on open sets. -/

open MeasureTheory
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Continuous global choices inherit a local classical derivative from
their spatial volume classes. No pointwise identity is assumed. -/
theorem hasFDerivAt_of_local_regular_representatives {d : ℕ}
    (f : Vec d → ℝ) (G : Vec d → Vec d) (hf : Continuous f) (hG : Continuous G)
    (x : Vec d) (U : Set (Vec d)) (hU : IsOpen U) (hx : x ∈ U)
    (v : Vec d → ℝ) (h : Vec d → Vec d)
    (hv : ContinuousOn v U) (hh : ContinuousOn h U)
    (hd : ∀ y ∈ U, HasFDerivAt v
      (∑ j : Fin d, (h y j) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) y)
    (heqv : f =ᵐ[volume.restrict U] v) (heqh : G =ᵐ[volume.restrict U] h) :
    HasFDerivAt f
      (∑ j : Fin d, (G x j) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x := by
  have hvpoint := Measure.eqOn_open_of_ae_eq heqv hU hf.continuousOn hv
  have hhpoint := Measure.eqOn_open_of_ae_eq heqh hU hG.continuousOn hh
  rw [hhpoint hx]
  exact (hd x hx).congr_of_eventuallyEq
    (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hx, fun y hy => hvpoint hy⟩)

end EinsteinRelation.Correctors
