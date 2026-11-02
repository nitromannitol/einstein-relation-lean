import EinsteinRelation.Calculus.WeakRepresentativeOperations

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- A measure dominating Lebesgue null sets gives representative-independent weak derivatives. -/
theorem hasWeakPartialDerivative_congr_of_absolutelyContinuous {d : ℕ}
    (m : Measure (Vec d)) (hm : (volume : Measure (Vec d)) ≪ m)
    (i : Fin d) {f g f' g' : Vec d → ℝ}
    (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') :
    HasWeakPartialDerivative Set.univ i f g ↔
      HasWeakPartialDerivative Set.univ i f' g' := by
  have hfv : f =ᵐ[volume.restrict Set.univ] f' := ae_restrict_of_ae (s := Set.univ) (hm.ae_eq hf)
  have hgv : g =ᵐ[volume.restrict Set.univ] g' := ae_restrict_of_ae (s := Set.univ) (hm.ae_eq hg)
  exact ⟨fun h => h.congr_ae hfv hgv, fun h => h.congr_ae hfv.symm hgv.symm⟩

end EinsteinFull
