import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Uniqueness of actual spatial weak gradients

Source: `paper/main.tex:699-704,808-816`. Equality follows coordinatewise
from equality of the distributions of locally integrable functions.
-/
open MeasureTheory
namespace EinsteinRelation

/-- Two actual locally integrable weak gradients of the same potential
coincide almost everywhere. Source: `paper/main.tex:808-816`. -/
theorem HasWeakGradient.ae_eq_of_same_potential {d : ℕ}
    {u : Vec d → ℝ} {G H : Vec d → Vec d}
    (hG : HasWeakGradient Set.univ u G) (hH : HasWeakGradient Set.univ u H) :
    G =ᵐ[volume] H := by
  have hi : ∀ i, (fun x => G x i) =ᵐ[volume] (fun x => H x i) := by
    intro i
    apply ae_eq_of_integral_contDiff_smul_eq
      (by simpa only [locallyIntegrableOn_univ] using (hG i).2.1)
      (by simpa only [locallyIntegrableOn_univ] using (hH i).2.1)
    intro ψ hψ hψc
    have htest : IsSpatialTest Set.univ ψ := ⟨hψ, hψc, Set.subset_univ _⟩
    have he := (hG i).2.2 ψ htest
    rw [(hH i).2.2 ψ htest] at he
    simpa only [Measure.restrict_univ, neg_inj, smul_eq_mul, mul_comm] using he.symm
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact funext hx

end EinsteinRelation
