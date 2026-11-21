import EinsteinFull.Regeneration.WeightedEllipticity
import PDEFoundation.PDE.CoefficientForcingScale

/-!
# Scalar normalization of elliptic weak solutions

A constant scalar multiple of a coefficient field preserves the homogeneous
`L²` divergence-form equation.
-/

open MeasureTheory

namespace EinsteinFull.Regeneration

/-- A homogeneous `L²` weak equation is unchanged by coefficient scaling. -/
theorem elliptic_l2_solution_smul_coefficient {d : ℕ} {U : Set (PDE.Vec d)}
    (a : PDE.CoeffField d) (u : PDE.H1Function U)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0) (c : ℝ) :
    PDE.IsWeakDivergenceFormL2SolutionOn (fun x => c • a x) U u 0 0 := by
  refine ⟨⟨?_, hsol.source_memL2, hsol.forcing_memL2⟩, ?_⟩
  · intro i
    have hi := (hsol.flux_memL2 i).const_mul c
    convert hi using 1
    funext x
    change ((c • a x).mulVec (u.grad x)) i = c * ((a x).mulVec (u.grad x)) i
    rw [Matrix.smul_mulVec]
    rfl
  · intro φ
    have hh := (hsol.toIsWeakDivergenceFormSolutionOn.smul_coefficient_source_forcing c φ).2
    simpa only [Pi.zero_apply, mul_zero, smul_zero] using hh

end EinsteinFull.Regeneration
