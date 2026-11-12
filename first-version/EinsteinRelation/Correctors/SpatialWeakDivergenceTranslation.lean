import EinsteinRelation.Calculus.WeakGradientTranslation
import EinsteinRelation.Correctors.SpatialWeakCongruence

/-! # Translation of whole-space weak divergences

Source `paper/main.tex:913–938`. Translation by a fixed vector preserves
local integrability on the whole space and transports every smooth compactly
supported spatial test in the weak divergence identity. Row divergences are
handled coordinatewise.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Translation preserves local integrability on the whole space. -/
private theorem locallyIntegrableOn_univ_comp_add_left {d : ℕ} (a : Vec d)
    (f : Vec d → ℝ) (hf : LocallyIntegrableOn f Set.univ volume) :
    LocallyIntegrableOn (fun y => f (a + y)) Set.univ volume := by
  rw [locallyIntegrableOn_univ] at hf ⊢
  have hm : (volume : Measure (Vec d)).map (Homeomorph.addLeft a) = volume :=
    (measurePreserving_add_left volume a).map_eq
  apply (locallyIntegrable_map_homeomorph (Homeomorph.addLeft a)).mp
  rwa [hm]

/-- Spatial translation preserves the whole-space actual distributional divergence.
Source: `paper/main.tex:913–938`. -/
theorem hasWeakDivergence_comp_add_left {d : ℕ} {F : Vec d → Vec d} {g : Vec d → ℝ}
    (h : HasWeakDivergence Set.univ F g) (a : Vec d) :
    HasWeakDivergence Set.univ (fun x => F (a + x)) (fun x => g (a + x)) := by
  unfold HasWeakDivergence at h ⊢
  obtain ⟨hF, hg, hw⟩ := h
  refine ⟨fun j => locallyIntegrableOn_univ_comp_add_left a (fun x => F x j) (hF j),
    locallyIntegrableOn_univ_comp_add_left a g hg, ?_⟩
  intro φ hφ
  let ψ : Vec d → ℝ := fun x => φ (-a + x)
  have hψ : IsSpatialTest Set.univ ψ := by
    refine ⟨?_, ?_, Set.subset_univ _⟩
    · dsimp [ψ]
      exact hφ.1.comp (contDiff_const.add contDiff_id)
    · exact hφ.2.1.comp_homeomorph (Homeomorph.addLeft (-a))
  have hw' := hw ψ hψ
  have ht (G : Vec d → ℝ) : (∫ x, G (a + x)) = ∫ x, G x :=
    (measurePreserving_add_left (volume : Measure (Vec d)) a).integral_comp
      (Homeomorph.addLeft a).measurableEmbedding G
  have hψa : ∀ x, ψ (a + x) = φ x := fun x => by
    simp only [ψ, neg_add_cancel_left]
  have hgrad : ∀ x, gradient ψ (a + x) = gradient φ x := by
    intro x
    funext j
    show coordinateDerivative j ψ (a + x) = coordinateDerivative j φ x
    simp only [coordinateDerivative, ψ, fderiv_comp_add_left, neg_add_cancel_left]
  simp only [Measure.restrict_univ] at hw' ⊢
  rw [← ht (fun x => dot (F x) (gradient ψ x)), ← ht (fun x => g x * ψ x)] at hw'
  simpa only [hgrad, hψa] using hw'

/-- Spatial translation preserves the whole-space row divergence of a matrix field.
Source: `paper/main.tex:913–938`. -/
theorem hasWeakRowDivergence_comp_add_left {d : ℕ} {S : Vec d → Mat d} {g : Vec d → Vec d}
    (h : HasWeakRowDivergence Set.univ S g) (a : Vec d) :
    HasWeakRowDivergence Set.univ (fun x => S (a + x)) (fun x => g (a + x)) := by
  unfold HasWeakRowDivergence at h ⊢
  intro j
  exact hasWeakDivergence_comp_add_left (h j) a

end EinsteinRelation.Correctors
