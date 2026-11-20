import EinsteinFull.Regeneration.GMPWeightedHarnack
import PDEFoundation.PDE.DGNM.ClassAlgebra

/-!
# Complements of homogeneous elliptic solutions

On a finite-volume domain, subtracting a homogeneous elliptic solution from a
constant preserves its `L²` weak equation.
-/

open MeasureTheory

namespace EinsteinFull.Regeneration

/-- A constant minus a homogeneous `L²` weak solution is again a weak solution. -/
theorem elliptic_l2_solution_const_sub {d : ℕ} {U : Set (PDE.Vec d)}
    [IsFiniteMeasure (volume.restrict U : Measure (PDE.Vec d))]
    (a : PDE.CoeffField d) (u : PDE.H1Function U)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0) (c : ℝ) :
    PDE.IsWeakDivergenceFormL2SolutionOn a U ((-u).addConst c) 0 0 := by
  have hsafe := PDE.DGNM.solutionOn_addConst
    (PDE.DGNM.solutionOn_neg hsol.toIsWeakDivergenceFormSolutionOn) c
  refine ⟨⟨?_, hsol.source_memL2, hsol.forcing_memL2⟩, fun φ => (hsafe φ).2⟩
  intro i
  have hi := (hsol.flux_memL2 i).neg
  convert hi using 1
  funext x
  simp only [PDE.H1Function.grad_addConst, PDE.H1Function.neg_grad,
    PDE.DGNM.matVecMul_neg, Pi.neg_apply]

end EinsteinFull.Regeneration
