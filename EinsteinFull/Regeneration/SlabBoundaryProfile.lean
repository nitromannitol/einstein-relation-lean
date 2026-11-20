import EinsteinFull.Regeneration.SlabProfileEnergy
import PDEFoundation.Sobolev.H1.Smooth
import PDEFoundation.Ambient.CoefficientField
import PDEFoundation.Sobolev.W1p.Clamps

/-!
# The width-one slab comparison profile

Clamping the affine force coordinate gives the comparison profile used in
Gantert–Mathieu–Piatnitski, Lemma 4.4.
-/

open Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The affine force coordinate as an `H¹` function on a bounded convex domain. -/
noncomputable def slabAffine {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin d) (L : ℝ) : PDE.H1Function U :=
  PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
    (f := fun x : PDE.Vec d => x i + L) ((contDiff_apply ℝ ℝ i).add contDiff_const)

/-- The continuous width-one profile rising from zero to one. -/
noncomputable def slabBoundaryProfile {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin d) (L : ℝ) : PDE.H1Function U :=
  ((slabAffine hU i L).toW1pFunction.clampConst hU (by norm_num) (by norm_num) 0 1).toH1Function

/-- The comparison profile has the source's literal clamped values. -/
theorem slabBoundaryProfile_apply {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin d) (L : ℝ) (x : PDE.Vec d) :
    slabBoundaryProfile hU i L x = min (max (x i + L) 0) 1 := by
  simp [slabBoundaryProfile, slabAffine]

/-- The profile gradient is supported precisely in its open transition strip. -/
theorem slabBoundaryProfile_grad {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin d) (L : ℝ) :
    (slabBoundaryProfile hU i L).grad =
      {x : PDE.Vec d | -L < x i ∧ x i < -L + 1}.indicator (fun _ => PDE.basisVec i) := by
  have haff : (slabAffine hU i L).grad = fun _ => PDE.basisVec i := by
    rw [slabAffine, PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain_grad]
    funext x
    ext j
    simp only [PDE.classicalGradient_apply]
    have hd : HasFDerivAt (fun y : PDE.Vec d => y i + L)
        ((ContinuousLinearMap.proj i) : PDE.Vec d →L[ℝ] ℝ) x := by
      simpa using (((ContinuousLinearMap.proj i : PDE.Vec d →L[ℝ] ℝ).hasFDerivAt).add_const L)
    rw [hd.fderiv]
    simp [PDE.basisVec_apply, eq_comm]
  change ((slabAffine hU i L).toW1pFunction.clampConst hU
    (by norm_num) (by norm_num) 0 1).grad = _
  rw [PDE.W1pFunction.clampConst_grad]
  simp only [PDE.H1Function.toW1pFunction_toFun, PDE.H1Function.toW1pFunction_grad]
  rw [haff]
  simp only [slabAffine, PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain_toFun]
  have hset : {y : PDE.Vec d | 0 < y i + L ∧ y i + L < 1} =
      {x : PDE.Vec d | -L < x i ∧ x i < -L + 1} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hset]

/-- The weighted profile energy is supported in the strip and bounded by the weight. -/
theorem slabBoundaryProfile_energy_le {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) (i : Fin d) (L s : ℝ)
    (a : PDE.CoeffField d) (lam Λ : ℝ) (x : PDE.Vec d)
    (hA : PDE.IsEllipticMatrix lam Λ (a x)) :
    PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • a x)
      ((slabBoundaryProfile hU i L).grad x)) ((slabBoundaryProfile hU i L).grad x) ≤
      {x : PDE.Vec d | -L < x i ∧ x i < -L + 1}.indicator
        (fun x => Λ * Real.exp (s * x i)) x := by
  rw [slabBoundaryProfile_grad]
  by_cases hx : x ∈ {x : PDE.Vec d | -L < x i ∧ x i < -L + 1}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hm : PDE.matVecMul (Real.exp (s * x i) • a x) (PDE.basisVec i) =
        Real.exp (s * x i) • PDE.matVecMul (a x) (PDE.basisVec i) :=
      Matrix.smul_mulVec _ _ _
    have hb : PDE.matVecMul (a x) (PDE.basisVec i) i = a x i i := by
      unfold PDE.matVecMul PDE.basisVec
      rw [Finset.sum_eq_single i]
      · simp only [Pi.single_eq_same, mul_one]
      · intro k _ hki
        simp only [Pi.single_eq_of_ne hki, mul_zero]
      · simp
    rw [hm, PDE.vecDot_basisVec_right]
    simp only [Pi.smul_apply, smul_eq_mul, hb]
    have hd := (le_abs_self (a x i i)).trans (PDE.abs_apply_le_of_isEllipticMatrix hA i i)
    have h := mul_le_mul_of_nonneg_left hd (Real.exp_pos (s * x i)).le
    nlinarith
  · simp only [Set.indicator_of_notMem hx]
    simp [PDE.matVecMul, PDE.vecDot]

end EinsteinFull.Regeneration
