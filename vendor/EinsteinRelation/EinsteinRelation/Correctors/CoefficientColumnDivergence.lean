import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.Environment.EuclideanLipschitz
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Spatial divergence of coefficient columns

Source: `paper/main.tex:777–782,840–842`. Summing the actual weak
coordinate derivatives gives the divergence datum used by the canonical
flow. A Lipschitz bound controls its literal Fréchet derivative expression.
-/

open MeasureTheory Set
open scoped NNReal

namespace EinsteinRelation.Correctors

private theorem coordinateDerivative_isSpatialTest {d : ℕ} {U : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) (j : Fin d) :
    IsSpatialTest U (coordinateDerivative j φ) := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const,
    hφ.2.1.fderiv_apply ℝ (unitVector j), ?_⟩
  apply Set.Subset.trans ?_ hφ.2.2
  apply closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra hxs
  exact hx (by simp only [coordinateDerivative,
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs, ContinuousLinearMap.zero_apply])

/-- The diagonal weak coordinate derivatives sum to the actual weak
divergence. Source: `paper/main.tex:777–782,840`. -/
theorem hasWeakDivergence_of_coordinate_derivatives {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {F : Vec d → Vec d} {D : Vec d → Vec d}
    (hD : ∀ j : Fin d, HasWeakPartialDerivative U j (fun x => F x j)
      (fun x => D x j)) :
    HasWeakDivergence U F (fun x => ∑ j, D x j) := by
  have hsum : LocallyIntegrableOn (fun x => ∑ j, D x j) U volume := by
    rw [locallyIntegrableOn_iff hU.isLocallyClosed]
    intro K hKU hK
    exact integrable_finset_sum Finset.univ fun j _ =>
      (hD j).2.1.integrableOn_compact_subset hKU hK
  refine ⟨fun j => (hD j).1, hsum, ?_⟩
  intro φ hφ
  have hleft (j : Fin d) :
      IntegrableOn (fun x => F x j * coordinateDerivative j φ x) U volume :=
    integrableOn_mul_spatialTest (hD j).1 (coordinateDerivative_isSpatialTest hφ j)
  have hright (j : Fin d) : IntegrableOn (fun x => D x j * φ x) U volume :=
    integrableOn_mul_spatialTest (hD j).2.1 hφ
  change (∫ x in U, ∑ j, F x j * coordinateDerivative j φ x) = _
  rw [integral_finset_sum _ fun j _ => hleft j]
  rw [Finset.sum_congr rfl fun j _ => (hD j).2.2 φ hφ]
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ fun j _ => hright j, Finset.sum_neg_distrib]

/-- The pointwise divergence expression of Lipschitz components is
bounded everywhere, including the points where `fderiv` is zero by
definition. Source: `paper/main.tex:840–842`. -/
theorem abs_divergence_le_of_lipschitz_components {d : ℕ} {L : ℝ≥0}
    {F : Vec d → Vec d} (hF : ∀ j : Fin d, LipschitzWith L (fun x => F x j))
    (x : Vec d) : |divergence F x| ≤ (d : ℝ) * L := by
  have he (j : Fin d) : |coordinateDerivative j (fun y => F y j) x| ≤ L := by
    rw [coordinateDerivative, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fun y => F y j) x‖ * ‖unitVector j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ (hF j))
        (by simp [unitVector, Pi.norm_single]) (norm_nonneg _) (by positivity)
      _ = L := mul_one _
  calc
    _ ≤ ∑ j, |coordinateDerivative j (fun y => F y j) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, (L : ℝ) := Finset.sum_le_sum fun j _ => he j
    _ = (d : ℝ) * L := by simp

end EinsteinRelation.Correctors
