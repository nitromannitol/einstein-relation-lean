import EinsteinRelation.External.GilbargTrudinger
import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2

/-! Ball Poincaré from the proved bounded convex domain inequality in PDEFoundation.
The native coordinate carriers and Lebesgue measures agree; Euclidean energies
are explicit on both sides. The diameter of a radius R ball is bounded by 2R. -/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.External.AKM

private theorem pdeBall_eq {d : ℕ} (y : Vec d) {R : ℝ} (hR : 0 < R) :
    PDE.euclideanBall y R = ball y R := by
  ext x
  exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR

private def pdeH1OfWeakGradient {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (h : HasWeakGradient U u g) :
    PDE.H1Function U where
  toFun := u
  grad := g
  memL2 := hu
  gradMemL2 := fun i => hg.continuousLinearMap_comp (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)
  hasWeakGradient := by
    intro i φ hφ hc hs
    exact (h i).2.2 φ ⟨hφ, hc, hs⟩

/-- The unnormalized Euclidean ball Poincaré estimate, with a constant
chosen before the center, radius, function and actual weak gradient. -/
theorem ballPoincareEstimate_from_pde :
    EinsteinRelation.External.GilbargTrudinger.BallPoincareEstimate := by
  intro d _hd
  refine ⟨(2 : ℝ) ^ d * 2, by positivity, ?_⟩
  intro y R hR u g hu hg h
  rw [← pdeBall_eq y hR] at hu hg h ⊢
  let v := pdeH1OfWeakGradient hu hg h
  have hp := PDE.centeredPoincare_sq_on_boundedConvexDomain
    (PDE.isOpenBoundedConvexDomain_euclideanBall y hR)
    (PDE.hasEuclideanDiameterLE_euclideanBall y hR)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR.le)
    ⟨y, PDE.center_mem_euclideanBall y hR⟩ v
  have hs := Real.sqrt_le_sqrt hp
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ d)
      (mul_nonneg (by norm_num) hR.le))] at hs
  simpa only [v, pdeH1OfWeakGradient, PDE.integralAverage,
    PDE.vecNormSq, PDE.vecDot, euclideanSq, dot, sq_abs, mul_assoc,
    setAverage_eq, measureReal_def, smul_eq_mul] using hs

end EinsteinFull
