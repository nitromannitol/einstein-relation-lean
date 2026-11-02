import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory
namespace EinsteinRelation

/-- Source `paper/main.tex:400–402`: spatial translation preserves the actual distributional gradient. -/
theorem HasWeakGradient.comp_add_left {d : ℕ}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (h : HasWeakGradient Set.univ f g) (a : Vec d) :
    HasWeakGradient Set.univ (fun y => f (a + y)) (fun y => g (a + y)) := by
  have hli (F : Vec d → ℝ) (hF : LocallyIntegrableOn F Set.univ volume) :
      LocallyIntegrableOn (fun y => F (a + y)) Set.univ volume := by
    rw [locallyIntegrableOn_univ] at hF ⊢
    have hm : (volume : Measure (Vec d)).map (Homeomorph.addLeft a) = volume :=
      (measurePreserving_add_left volume a).map_eq
    apply (locallyIntegrable_map_homeomorph (Homeomorph.addLeft a)).mp
    rwa [hm]
  intro i
  refine ⟨hli f (h i).1, hli _ (h i).2.1, ?_⟩
  intro φ hφ
  let ψ : Vec d → ℝ := fun x => φ (-a + x)
  have hψ : IsSpatialTest Set.univ ψ := by
    refine ⟨?_, ?_, Set.subset_univ _⟩
    · dsimp [ψ]
      exact hφ.1.comp (contDiff_const.add contDiff_id)
    · exact hφ.2.1.comp_homeomorph (Homeomorph.addLeft (-a))
  have hw := (h i).2.2 ψ hψ
  simp only [Measure.restrict_univ] at hw ⊢
  have ht (F : Vec d → ℝ) : (∫ x, F (a + x)) = ∫ x, F x :=
    (measurePreserving_add_left (volume : Measure (Vec d)) a).integral_comp
      (Homeomorph.addLeft a).measurableEmbedding F
  have hd : ∀ x, coordinateDerivative i ψ (a + x) = coordinateDerivative i φ x := by
    intro x
    simp only [coordinateDerivative, ψ, fderiv_comp_add_left, neg_add_cancel_left]
  rw [← ht (fun x => f x * coordinateDerivative i ψ x),
    ← ht (fun x => g x i * ψ x)] at hw
  simpa only [hd, ψ, neg_add_cancel_left] using hw

/-- Source `paper/main.tex:779–806`: translation preserves the spatial weak gradient. -/
theorem HasWeakGradient.translated {d : ℕ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (h : HasWeakGradient Set.univ u G) (z : Vec d) :
    HasWeakGradient Set.univ (fun x => u (z+x)) (fun x => G (z+x)) := by
  exact h.comp_add_left z

end EinsteinRelation
