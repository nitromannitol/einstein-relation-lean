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

/-- The complementary central-slab solution satisfies the Harnack comparison used in GMP. -/
theorem gmp_central_slab_complement_harnack (d : ℕ) (hd : 0 < d) (lam Λ : ℝ)
    (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (i : Fin d) (z z' : PDE.Vec d),
      z i = 0 → z' i = 0 → PDE.euclideanSqDist z z' ≤ d →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → 1 - u z ≤ H * (1 - u z') := by
  obtain ⟨H, hH, hcomp⟩ := gmp_central_slab_harnack d hd lam Λ hlam hΛ
  refine ⟨H, hH, ?_⟩
  intro i z z' hz hz' hdist
  dsimp only
  intro a hmeas hell u hsol hcont hupper
  let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (8 * d))
  let : IsFiniteMeasure (volume.restrict U : Measure (PDE.Vec d)) := by
    exact isFiniteMeasure_restrict.mpr
      (PDE.volume_euclideanBall_ne_top _ (Real.sqrt_nonneg _))
  let v : PDE.H1Function U := (-u).addConst 1
  have hv : PDE.IsWeakDivergenceFormL2SolutionOn
      (fun x => Real.exp (x i) • a x) U v 0 0 :=
    elliptic_l2_solution_const_sub (fun x => Real.exp (x i) • a x) u hsol 1
  have hval (x : PDE.Vec d) : v x = 1 - u x := by
    simp only [v, PDE.H1Function.addConst_apply, PDE.H1Function.neg_toFun]
    ring
  have hvcont : Continuous v.toFun := by
    have heq : v.toFun = fun x => 1 - u x := funext hval
    rw [heq]
    exact continuous_const.sub hcont
  have hvnonneg : ∀ x, 0 ≤ v x := fun x => by rw [hval]; linarith [hupper x]
  have h := hcomp i z z' hz hz' hdist
  dsimp only at h
  have hh := h a hmeas hell v hv hvcont hvnonneg
  simpa only [hval] using hh

end EinsteinFull.Regeneration
