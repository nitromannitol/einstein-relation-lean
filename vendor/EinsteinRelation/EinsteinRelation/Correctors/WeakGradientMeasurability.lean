import EinsteinRelation.Calculus.Weak
import EinsteinRelation.TimeChange.EuclideanTransport
open MeasureTheory
namespace EinsteinRelation.Correctors
/-- The actual weak gradient has measurable Euclidean norm
(`paper/main.tex:870–873`). -/
theorem aestronglyMeasurable_euclideanNorm_of_weakGradient {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (h : HasWeakGradient U u G) :
    AEStronglyMeasurable (fun x => euclideanNorm (G x)) (volume.restrict U) := by
  have hm (i : Fin d) : AEStronglyMeasurable (fun x => G x i) (volume.restrict U) :=
    (h i).2.1.aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun x => euclideanSq (G x)) (volume.restrict U) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => (hm j).mul (hm j)
  exact Real.continuous_sqrt.comp_aestronglyMeasurable hs
end EinsteinRelation.Correctors
