import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.Correctors.SpatialWeakLocalization

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- One-coordinate addition for the spatial-potential construction
(`paper/main.tex:693–698`). No openness restriction is added to the domain. -/
theorem hasWeakPartialDerivative_add {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {f h g k : Vec d → ℝ}
    (hf : HasWeakPartialDerivative U i f g)
    (hh : HasWeakPartialDerivative U i h k) :
    HasWeakPartialDerivative U i (fun x => f x + h x) (fun x => g x + k x) := by
  refine ⟨hf.1.add hh.1, hf.2.1.add hh.2.1, ?_⟩
  intro φ hφ
  have hdφ : IsSpatialTest U (coordinateDerivative i φ) := by
    refine ⟨(contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const,
      hφ.2.1.fderiv_apply ℝ (unitVector i), ?_⟩
    apply Set.Subset.trans ?_ hφ.2.2
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    by_contra hxs
    exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs])
  simp only [add_mul]
  rw [integral_add (integrableOn_mul_spatialTest hf.1 hdφ)
      (integrableOn_mul_spatialTest hh.1 hdφ),
    integral_add (integrableOn_mul_spatialTest hf.2.1 hφ)
      (integrableOn_mul_spatialTest hh.2.1 hφ)]
  rw [hf.2.2 φ hφ, hh.2.2 φ hφ]
  ring

end EinsteinRelation.Correctors
