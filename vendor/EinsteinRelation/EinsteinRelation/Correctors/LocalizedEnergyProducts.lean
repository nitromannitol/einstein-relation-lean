import EinsteinRelation.Correctors.SpatialWeakLocalization
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Integrability of the actual localized energy test products.
Source: `paper/main.tex:792`; time-slice energy testing in AKM Lemma 8.2.
Use compact smooth multipliers in L∞, finite sums and L² Cauchy–Schwarz. -/
theorem localized_H1_energy_products_integrable {d : ℕ} {U : Set (Vec d)}
    {χ v : Vec d → ℝ} {F G : Vec d → Vec d}
    (hχ : IsSpatialTest U χ) (hv : MemLp v 2 (volume.restrict U))
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict U))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict U)) :
    MemLp (fun x => dot (F x) (gradient χ x)) 2 (volume.restrict U) ∧
    Integrable (fun x => χ x ^ 2 * v x ^ 2) (volume.restrict U) ∧
    Integrable (fun x => χ x * v x * dot (F x) (gradient χ x)) (volume.restrict U) ∧
    Integrable (fun x => χ x ^ 2 * dot (F x) (G x)) (volume.restrict U) := by
  have hm := hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 (volume.restrict U)
  have hm2 : MemLp (fun x => χ x ^ 2) ⊤ (volume.restrict U) := by
    simpa only [pow_two] using hm.mul' hm
  have hw : MemLp (fun x => dot (F x) (gradient χ x)) 2 (volume.restrict U) := by
    unfold dot gradient
    have hi (i : Fin d) : MemLp (fun x => F x i * coordinateDerivative i χ x) 2
        (volume.restrict U) := by
      have hD : MemLp (coordinateDerivative i χ) ⊤ (volume.restrict U) :=
        (isSpatialTest_coordinateDerivative hχ i).1.continuous.memLp_top_of_hasCompactSupport
          (isSpatialTest_coordinateDerivative hχ i).2.1 _
      simpa only [mul_comm] using (hF i).mul' (r := 2) hD
    exact memLp_finset_sum Finset.univ (fun i _ => hi i)
  have hcv : MemLp (fun x => χ x * v x) 2 (volume.restrict U) := by
    simpa only [mul_comm] using hv.mul' hm
  refine ⟨hw, ?_, ?_, ?_⟩
  · simpa only [mul_pow] using hcv.integrable_sq
  · exact hcv.integrable_mul hw
  · have hi (i : Fin d) : Integrable (fun x => χ x ^ 2 * (F x i * G x i))
        (volume.restrict U) := by
      have hp : MemLp (fun x => χ x ^ 2 * F x i) 2 (volume.restrict U) := by
        simpa only [mul_comm] using (hF i).mul' hm2
      simpa only [Pi.mul_def, mul_assoc] using hp.integrable_mul (hG i)
    simpa only [dot, Finset.mul_sum] using
      integrable_finset_sum Finset.univ (fun i _ => hi i)

end EinsteinRelation.Correctors
