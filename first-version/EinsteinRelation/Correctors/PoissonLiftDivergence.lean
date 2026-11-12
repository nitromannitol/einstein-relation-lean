import EinsteinRelation.Correctors.PoissonLiftHeightDerivative
import EinsteinRelation.Correctors.PoissonLiftHorizontalDerivative

/-! Source: `paper/main.tex:735-739`. Combining the genuine vertical and
horizontal test identities for the explicit augmented flux. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A divergence-free original flux and any locally integrable vertical
component form an actual divergence-free flux in the augmented space. -/
theorem hasWeakDivergence_poissonLiftFlux {d : ℕ}
    (F : Vec d → Vec d) (B : Vec d → ℝ)
    (hF : HasWeakDivergence Set.univ F (fun _ => 0))
    (hB : LocallyIntegrable B volume) :
    HasWeakDivergence Set.univ (poissonLiftFlux F B) (fun _ => 0) := by
  have hloc := locallyIntegrable_poissonLiftFlux F B
    (fun i => locallyIntegrableOn_univ.mp (hF.1 i)) hB
  refine ⟨fun i => locallyIntegrableOn_univ.mpr (hloc i),
    locallyIntegrableOn_zero, ?_⟩
  intro ψ hψ
  have hi (j : Fin (d + 1)) : Integrable (fun x : Vec (d + 1) =>
      poissonLiftFlux F B x j * coordinateDerivative j ψ x) volume := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j ψ) :=
      ((contDiff_infty_iff_fderiv.mp hψ.1).2).clm_apply contDiff_const
    simpa only [smul_eq_mul] using
      (hloc j).integrable_smul_right_of_hasCompactSupport hD.continuous
        (hψ.2.1.fderiv_apply ℝ (unitVector j))
  have hi0 : Integrable (fun x : Vec (d + 1) =>
      B (poissonLiftBase x) * coordinateDerivative 0 ψ x) volume := by
    simpa only [poissonLiftFlux, Fin.cons_zero] using hi 0
  have hisum : Integrable (fun x : Vec (d + 1) => ∑ i : Fin d,
      F (poissonLiftBase x) i * coordinateDerivative i.succ ψ x) volume := by
    apply integrable_finset_sum
    intro i _
    simpa only [poissonLiftFlux, Fin.cons_succ] using hi i.succ
  simp only [setIntegral_univ, dot, gradient, Fin.sum_univ_succ,
    poissonLiftFlux, Fin.cons_zero, Fin.cons_succ, zero_mul, integral_zero, neg_zero]
  rw [integral_add hi0 hisum, integral_height_derivative_poissonLift_zero B hB ψ hψ,
    integral_horizontal_gradient_poissonLift_zero F hF ψ hψ, add_zero]

end EinsteinRelation.Correctors
