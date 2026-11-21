import PDEFoundation.Sobolev.H1.ZeroBoundaryLimit

/-!
# Gradients of zero-boundary representatives

The gradient of a zero-boundary representative agrees almost everywhere with
that of any Sobolev representative of the same function on an open domain.
-/

open Filter MeasureTheory PDE

namespace EinsteinFull.Regeneration

/-- A zero-boundary witness has the same weak gradient as the original
Sobolev representative, almost everywhere. -/
theorem exists_h10_with_ae_gradient {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : IsOpen U) (u : PDE.H1Function U) (hu : PDE.MemH10 U u.toFun) :
    ∃ v : PDE.H10Function U, v.toH1Function.toFun = u.toFun ∧
      ∀ᵐ x ∂(PDE.volumeOn U), v.toH1Function.grad x = u.grad x := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨v, hv, ?_⟩
  have hloc (w : PDE.H1Function U) (i : Fin d) :
      LocallyIntegrableOn (fun x => w.grad x i) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((w.gradMemL2 i).locallyIntegrable (by norm_num))
  have hcoord (i : Fin d) : (fun x => v.toH1Function.grad x i) =ᵐ[PDE.volumeOn U]
      (fun x => u.grad x i) := by
    have hw := v.toH1Function.hasWeakGradient i
    rw [hv] at hw
    exact PDE.HasWeakPartialDerivOn.ae_eq hU (hloc v.toH1Function i) (hloc u i) hw
      (u.hasWeakGradient i)
  filter_upwards [Filter.eventually_all.2 hcoord] with x hx
  funext i
  exact hx i

end EinsteinFull.Regeneration
