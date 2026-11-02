import EinsteinRelation.Correctors.SpatialWeakLocalization
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A compact smooth local multiplier produces an actual whole-space L²
function. Source: `paper/main.tex:792`; localized H¹ energy tests. -/
theorem memLp_mul_spatialTest_univ {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {f ψ : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hψ : IsSpatialTest U ψ) :
    MemLp (fun x => ψ x * f x) 2 volume := by
  have hm : MemLp ψ ⊤ (volume.restrict U) :=
    hψ.1.continuous.memLp_top_of_hasCompactSupport hψ.2.1 _
  have hi : MemLp (fun x => ψ x * f x) 2 (volume.restrict U) := hm.fun_mul hf
  have hs : Function.support (fun x => ψ x * f x) ⊆ U := by
    intro x hx
    apply hψ.2.2
    apply subset_tsupport ψ
    exact (mul_ne_zero_iff.mp hx).1
  have he : U.indicator (fun x => ψ x * f x) = fun x => ψ x * f x :=
    Set.indicator_eq_self.mpr hs
  rw [← he]
  exact (memLp_indicator_iff_restrict hU).mpr hi

end EinsteinRelation.Correctors
