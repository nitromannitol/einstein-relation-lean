import EinsteinRelation.Correctors.ScalarCorrectedGenerator
import EinsteinRelation.Correctors.HomogenizedMatrixBounds

/-! # The local skew-divergence source is square integrable

Source: `paper/main.tex:1044–1054`. The actual local flux identity defines
the row source; its second moment follows from those of the local gradient
and refined flux error and boundedness of the coefficient.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The explicit row-divergence source is square integrable
(`paper/main.tex:1044–1054`). -/
theorem memLp_localCorrector_rowSource
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {V F : FieldPair d → Vec d} (hV : ∀ k, MemLp (fun ω => V ω k) 2 Q)
    (hF : ∀ k, MemLp (fun ω => F ω k) 2 Q)
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    (abar : Mat d) (j i : Fin d) :
    MemLp (fun ω => (∑ k, ω.1 0 i k * (unitVector j k + V ω k)) -
      abar i j - F ω i) 2 Q := by
  obtain ⟨C, hC⟩ := hA
  apply MemLp.sub _ (hF i)
  apply MemLp.sub _ (memLp_const (abar i j))
  apply memLp_finset_sum Finset.univ
  intro k _
  have h := memLp_mul_of_ae_bound ((memLp_const (unitVector j k)).add (hV k))
    (measurable_coeff_entry i k).aestronglyMeasurable (hC.mono fun _ hω => hω i k)
  simpa only [Pi.add_apply, mul_comm] using h

/-- The residual row source gives the actual local corrector flux identity
without any extra assumption (`paper/main.tex:1044–1054`). -/
theorem localCorrector_flux_identity {d : ℕ} (a abar : Mat d)
    (V F : Fin d → Vec d) :
    ∀ j, a.mulVec (unitVector j + V j) = abar.mulVec (unitVector j) +
      ((fun i => (∑ k, a i k * (unitVector j k + V j k)) - abar i j - F j i) + F j) := by
  intro j
  ext i
  have he : abar.mulVec (unitVector j) i = abar i j := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  simp only [Matrix.mulVec, dotProduct] at he
  rw [he]
  ring

end EinsteinRelation.Correctors
