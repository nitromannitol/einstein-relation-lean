import EinsteinRelation.Correctors.AKMHeatKernelUniqueness
import EinsteinRelation.External.AKMKernelSemigroup

/-! # Identification of the represented AKM flow

Source: `paper/main.tex:787–792,850`; AKM (9.2), printed p. 347.
The existing representation predicate may choose different E.1 kernels.
Their uniqueness identifies the continuous positive-time flows.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
open Environment.AKMTestIntegralSupport

/-- Two continuous flows with the existing canonical kernel representation
for the same datum agree at every positive time and every spatial point.
Source: `paper/main.tex:787–792,850`. -/
theorem canonicalKernelRepresentations_eq {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d} {u v : ℝ × Vec d → ℝ}
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    (hv : ContinuousOn v (Set.Ioi 0 ×ˢ Set.univ))
    (hurep : HasCanonicalKernelRepresentation A g u)
    (hvrep : HasCanonicalKernelRepresentation A g v) :
    ∀ t : ℝ, 0 < t → ∀ x : Vec d, u (t,x) = v (t,x) := by
  obtain ⟨_,_,_,_,_,_,hP,hup⟩ := hurep
  obtain ⟨_,_,_,_,_,_,hQ,hvp⟩ := hvrep
  exact akm_kernel_represented_flows_eq hK hP hQ hu hv
    (fun t ht x => (hup t ht x).2) (fun t ht x => (hvp t ht x).2)

end EinsteinRelation.Correctors
