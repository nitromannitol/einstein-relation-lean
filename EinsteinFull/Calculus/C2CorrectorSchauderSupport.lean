import SchauderStatements.C1alpha
import EinsteinRelation.Correctors.SpatialWeakLocalization
import EinsteinRelation.External.GilbargTrudinger
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import PDEFoundation.PDE.DGNM.Scaling
import PDEFoundation.PDE.DGNM.ClassAlgebra
import PDEFoundation.Sobolev.H1.MeanEnergyTriangle
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
Deterministic quantitative Schauder support for the canonical corrector.
The small parameter below is dimensionless, and is chosen before the
coefficient field and weak solution. It is not the physical dependence range.
This module does not yet identify a canonical corrector with the H1 solution.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull

/-- A structural upper bound for the matrix Hölder seminorm determines one
small Schauder parameter, independently of the coefficient field. -/
theorem exists_schauder_half_scale (C M : ℝ) (hC : 0 < C) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧
      ε ^ (1 / 2 : ℝ) * M ≤ C⁻¹ * (1 / 2) * (1 - 1 / 2) := by
  let T := C⁻¹ * (1 / 2 : ℝ) * (1 - 1 / 2)
  have hT : 0 < T := by dsimp only [T]; positivity
  let q := (T / (M + 1)) ^ (2 : ℝ)
  have hMone : 0 < M + 1 := by linarith
  have hq : 0 < q := Real.rpow_pos_of_pos (div_pos hT hMone) _
  refine ⟨min (1 / 4) q, lt_min (by norm_num) hq, min_le_left _ _, ?_⟩
  have hpow : q ^ (1 / 2 : ℝ) = T / (M + 1) := by
    dsimp only [q]
    rw [← Real.rpow_mul (div_nonneg hT.le hMone.le)]
    norm_num
  calc
    (min (1 / 4) q) ^ (1 / 2 : ℝ) * M ≤ q ^ (1 / 2 : ℝ) * M :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (le_min (by norm_num) hq.le) (min_le_right _ _) (by norm_num)) hM
    _ = T / (M + 1) * M := by rw [hpow]
    _ ≤ T / (M + 1) * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hT.le hMone.le)
    _ = T := div_mul_cancel₀ _ hMone.ne'

/-- Quantitative deterministic unit-ball estimate for actual homogeneous
weak solutions. The constant precedes both the field and the solution;
all magnitudes and balls are Euclidean. This is a PDE support theorem,
not a source-facing canonical-corrector assertion. -/
theorem exists_uniform_homogeneous_schauder_halfBall_bound
    (d : ℕ) (hd : 0 < d) (Λ M : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : PDE.CoeffField d),
      (∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
        PDE.IsEllipticMatrix 1 Λ (a x)) →
      PDE.EuclideanMatrixHolderSeminormLE
        (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) M →
      ∀ u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec d) 1),
      PDE.IsWeakDivergenceFormSolutionOn a
        (PDE.euclideanBall (0 : PDE.Vec d) 1) u 0 0 →
      ∀ᵐ x ∂PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)),
        PDE.vecEuclideanNorm (u.grad x) ≤ K *
          Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : PDE.Vec d) 1)
            (fun y => PDE.vecNormSq (u.grad y))) := by
  obtain ⟨C, hC, hs⟩ := PDE.exists_schauderC1alpha_constant hd (Λ := Λ)
  obtain ⟨ε, hε, hεfour, hsmall⟩ := exists_schauder_half_scale C M hC hM
  refine ⟨(C / (1 / 2 : ℝ) ^ 2) * ε ^ (-(d : ℝ) / 2), by positivity, ?_⟩
  intro a hell ha u hsol
  let ha' : ∃ B : ℝ, 0 ≤ B ∧ PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) B := ⟨M, hM, ha⟩
  have hzero : PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1) (0 : PDE.Vec d → PDE.Vec d)
      (1 / 2) 0 := by
    intro x _ y _
    simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
  let hF : ∃ B : ℝ, 0 ≤ B ∧ PDE.EuclideanFieldHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1) (0 : PDE.Vec d → PDE.Vec d)
      (1 / 2) B := ⟨0, le_refl 0, hzero⟩
  have hFzero : PDE.euclideanFieldHolderSeminormOn
      (PDE.euclideanBall (0 : PDE.Vec d) 1) 0 (1 / 2) hF = 0 :=
    le_antisymm (PDE.euclideanFieldHolderSeminormOn_le hF (le_refl 0) hzero)
      (PDE.euclideanFieldHolderSeminormOn_nonneg hF)
  have hsmall' : ε ^ (1 / 2 : ℝ) * PDE.euclideanMatrixHolderSeminormOn
      (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) ha' ≤
      C⁻¹ * (1 / 2) * (1 - 1 / 2) :=
    (mul_le_mul_of_nonneg_left (PDE.euclideanMatrixHolderSeminormOn_le ha' hM ha)
      (Real.rpow_nonneg hε.le _)).trans hsmall
  obtain ⟨G, hG, hgrad, _, hbound⟩ :=
    hs (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      hε hεfour a 0 hell ha' hF hsmall' u hsol
  rw [hFzero, mul_zero, add_zero] at hbound
  have hnorm : PDE.euclideanFieldLpNormOn
      (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)) ∞ u.grad hgrad ≤
      (C / (1 / 2 : ℝ) ^ 2) * (ε ^ (-(d : ℝ) / 2) *
        Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : PDE.Vec d) 1)
          (fun y => PDE.vecNormSq (u.grad y)))) :=
    le_trans (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hε.le _)
      (PDE.euclideanFieldHolderSeminormOn_nonneg hG))) hbound
  filter_upwards [ae_le_lpNorm_exponent_top hgrad] with x hx
  have hx' : PDE.vecEuclideanNorm (u.grad x) ≤
      PDE.euclideanFieldLpNormOn
        (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)) ∞ u.grad hgrad := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _),
      PDE.euclideanFieldLpNormOn, PDE.lpNormOn, PDE.eLpNormOn,
      MeasureTheory.lpNorm] using hx
  exact (hx'.trans hnorm).trans_eq (mul_assoc _ _ _).symm

/-- Removing the affine unit direction gives the precise deterministic
`K * (1 + RMS energy)` form. This still concerns an actual supplied PDE
solution, and does not assert the canonical realization or its smooth bounds. -/
theorem exists_uniform_affine_schauder_halfBall_bound
    (d : ℕ) (hd : 0 < d) (Λ M : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : PDE.CoeffField d),
      (∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
        PDE.IsEllipticMatrix 1 Λ (a x)) →
      PDE.EuclideanMatrixHolderSeminormLE
        (PDE.euclideanBall (0 : PDE.Vec d) 1) a (1 / 2) M →
      ∀ u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec d) 1),
      PDE.IsWeakDivergenceFormSolutionOn a
        (PDE.euclideanBall (0 : PDE.Vec d) 1) u 0 0 → ∀ i : Fin d,
      ∀ᵐ x ∂PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)),
        PDE.vecEuclideanNorm (u.grad x - PDE.basisVec i) ≤ K *
          (1 + Real.sqrt (PDE.integralAverage
            (PDE.euclideanBall (0 : PDE.Vec d) 1)
            (fun y => PDE.vecNormSq (u.grad y - PDE.basisVec i)))) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_homogeneous_schauder_halfBall_bound d hd Λ M hM
  refine ⟨K + 1, by linarith, ?_⟩
  intro a hell ha u hsol i
  let : IsFiniteMeasure (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec d) 1)) :=
    PDE.isFiniteMeasure_volumeOn_euclideanBall 0 (by norm_num)
  have hc : PDE.MemVectorL2On (PDE.euclideanBall (0 : PDE.Vec d) 1)
      (fun _ => PDE.basisVec i) := fun j => memLp_const _
  have hg : PDE.MemVectorL2On (PDE.euclideanBall (0 : PDE.Vec d) 1)
      (fun y => u.grad y - PDE.basisVec i) := fun j =>
    (u.gradMemL2 j).sub (hc j)
  have henergy := PDE.sqrt_integralAverage_vecNormSq_add_le hg hc
  simp only [sub_add_cancel] at henergy
  rw [PDE.sqrt_integralAverage_vecNormSq_const
    (PDE.volume_euclideanBall_pos 0 (by norm_num))
    (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top 0 (by norm_num))),
    PDE.vecEuclideanNorm_basisVec] at henergy
  filter_upwards [hbound a hell ha u hsol] with x hx
  have htriangle : PDE.vecEuclideanNorm (u.grad x - PDE.basisVec i) ≤
      PDE.vecEuclideanNorm (u.grad x) + 1 := by
    simpa only [sub_eq_add_neg, PDE.vecEuclideanNorm_neg,
      PDE.vecEuclideanNorm_basisVec] using
        PDE.vecEuclideanNorm_add_le (u.grad x) (-PDE.basisVec i)
  have hcombined := htriangle.trans (add_le_add
    (hx.trans (mul_le_mul_of_nonneg_left henergy hK.le)) (le_refl 1))
  have hnonneg := Real.sqrt_nonneg (PDE.integralAverage
    (PDE.euclideanBall (0 : PDE.Vec d) 1)
    (fun y => PDE.vecNormSq (u.grad y - PDE.basisVec i)))
  nlinarith only [hcombined, hnonneg]

/-- The deterministic Schauder estimate on a physical ball, using the
normalized pullback `u(R y + z) / R`. Its gradient has no residual scale
factor. The right side is the literal pulled-back Euclidean energy. -/
theorem exists_uniform_affine_schauder_rescaled_ball_bound
    (d : ℕ) (hd : 0 < d) (Λ M : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : PDE.CoeffField d) (z : PDE.Vec d)
      (R : ℝ), 0 < R →
      (∀ x ∈ PDE.euclideanBall z R, PDE.IsEllipticMatrix 1 Λ (a x)) →
      PDE.EuclideanMatrixHolderSeminormLE
        (PDE.euclideanBall (0 : PDE.Vec d) 1)
        (PDE.DGNM.blowUpCoeff a z R) (1 / 2) M →
      ∀ u : PDE.H1Function (PDE.euclideanBall z R),
      PDE.IsWeakDivergenceFormSolutionOn a (PDE.euclideanBall z R) u 0 0 →
      ∀ i : Fin d, ∀ᵐ x ∂PDE.volumeOn (PDE.euclideanBall z (R * (1 / 2))),
        PDE.vecEuclideanNorm (u.grad x - PDE.basisVec i) ≤ K *
          (1 + Real.sqrt (PDE.integralAverage
            (PDE.euclideanBall (0 : PDE.Vec d) 1)
            (fun y => PDE.vecNormSq (u.grad (R • y + z) - PDE.basisVec i)))) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_affine_schauder_halfBall_bound d hd Λ M hM
  refine ⟨K, hK, ?_⟩
  intro a z R hR hell hholder u hsol i
  let v := R⁻¹ • PDE.DGNM.blowUp u z hR (Set.Subset.refl _)
  have hv : ∀ y, v.grad y = u.grad (R • y + z) := by
    intro y
    simp only [v, PDE.H1Function.smul_grad, PDE.DGNM.blowUp_grad,
      smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have hvs := PDE.DGNM.solutionOn_smul
    (PDE.DGNM.solutionOn_blowUp (PDE.isOpen_euclideanBall z R)
      hsol z hR (Set.Subset.refl _)) R⁻¹
  have hvb := hb (PDE.DGNM.blowUpCoeff a z R)
    (PDE.DGNM.blowUpCoeff_elliptic hell z hR (Set.Subset.refl _)) hholder v hvs i
  simp_rw [hv] at hvb
  exact (PDE.DGNM.ae_comp_affineScale_ball_iff z hR (1 / 2)).mp hvb

/-- Retain the literal function and gradient when transporting the spatial
weak-solution interface to PDEFoundation. -/
def pdeH1OfSpatialWeakSolution {d : ℕ} {U : Set (EinsteinRelation.Vec d)}
    {a : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {u : EinsteinRelation.Vec d → ℝ} {g : EinsteinRelation.Vec d → EinsteinRelation.Vec d}
    (h : EinsteinRelation.External.GilbargTrudinger.WeakSolution U a u g) :
    PDE.H1Function U where
  toFun := u
  grad := g
  memL2 := h.1
  gradMemL2 := fun i => h.2.1.continuousLinearMap_comp
    (ContinuousLinearMap.proj i : EinsteinRelation.Vec d →L[ℝ] ℝ)
  hasWeakGradient := by
    intro i φ hφ hc hs
    exact (h.2.2.1 i).2.2 φ ⟨hφ, hc, hs⟩

/-- The locally integrable flux in the spatial interface supplies genuine
integrability against every compact smooth PDE test. -/
theorem pdeH1OfSpatialWeakSolution_isSolution {d : ℕ}
    {U : Set (EinsteinRelation.Vec d)}
    {a : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {u : EinsteinRelation.Vec d → ℝ} {g : EinsteinRelation.Vec d → EinsteinRelation.Vec d}
    (h : EinsteinRelation.External.GilbargTrudinger.WeakSolution U a u g) :
    PDE.IsWeakDivergenceFormSolutionOn a U (pdeH1OfSpatialWeakSolution h) 0 0 := by
  intro φ
  have hφ : EinsteinRelation.IsSpatialTest U φ.toFun :=
    ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  have hi (i : Fin d) : IntegrableOn
      (fun x => ((a x).mulVec (g x)) i * EinsteinRelation.coordinateDerivative i φ x) U :=
    EinsteinRelation.Correctors.integrableOn_mul_spatialTest
      (h.2.2.2.1 i) (EinsteinRelation.Correctors.isSpatialTest_coordinateDerivative hφ i)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact integrable_finsetSum _ fun i _ => hi i
  · simp only [Pi.zero_apply, zero_mul]; exact integrableOn_zero
  · simp only [PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    exact integrableOn_zero
  · have heq := h.2.2.2.2.2 φ.toFun hφ
    simpa only [Pi.zero_apply, zero_mul, integral_zero, neg_zero, sub_zero,
      PDE.vecDot, PDE.WeakTestFunction.grad, PDE.WeakTestFunction.partialDeriv,
      EinsteinRelation.dot, EinsteinRelation.gradient, EinsteinRelation.coordinateDerivative,
      pdeH1OfSpatialWeakSolution, PDE.matVecMul, Matrix.mulVec, dotProduct,
      PDE.basisVec, EinsteinRelation.unitVector, Finset.sum_const_zero] using heq

/-- A global Euclidean operator Lipschitz bound gives a unit-ball matrix
half-Holder bound after physical dilation and coefficient normalization. -/
theorem matrixHolder_half_normalized_pullback {d : ℕ}
    {a : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 < R)
    (ha : EinsteinRelation.IsOperatorLipschitz A a) :
    PDE.EuclideanMatrixHolderSeminormLE
      (PDE.euclideanBall (0 : PDE.Vec d) 1)
      (fun y => B • a (R • y)) (1 / 2) (2 * B * A * R) := by
  intro x hx y hy ξ
  have hx' : PDE.vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hy' : PDE.vecEuclideanNorm y < 1 := by
    simpa only [sub_zero] using
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
  have ht : PDE.vecEuclideanNorm (x - y) ≤ 2 := by
    have ht := PDE.vecEuclideanNorm_add_le x (-y)
    rw [PDE.vecEuclideanNorm_neg] at ht
    exact ht.trans (by linarith)
  have hs := Real.sq_sqrt (PDE.vecEuclideanNorm_nonneg (x - y))
  have hn := Real.sqrt_nonneg (PDE.vecEuclideanNorm (x - y))
  have hh : PDE.vecEuclideanNorm (x - y) ≤
      2 * PDE.vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith
  have hnscale (c : ℝ) (hc : 0 ≤ c) (v : PDE.Vec d) :
      PDE.vecEuclideanNorm (c • v) = c * PDE.vecEuclideanNorm v := by
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hc]
  have hbase := ha (R • x) (R • y) ξ
  change PDE.vecEuclideanNorm (((B • a (R • x)) - (B • a (R • y))).mulVec ξ) ≤ _
  rw [← smul_sub, Matrix.smul_mulVec, hnscale B hB]
  have hdist : EinsteinRelation.euclideanNorm (R • x - R • y) =
      R * PDE.vecEuclideanNorm (x - y) := by
    rw [← smul_sub]
    exact hnscale R hR.le (x - y)
  rw [hdist] at hbase
  change PDE.vecEuclideanNorm ((a (R • x) - a (R • y)).mulVec ξ) ≤ _ at hbase
  calc
    _ ≤ B * (A * (R * PDE.vecEuclideanNorm (x - y)) * PDE.vecEuclideanNorm ξ) :=
      mul_le_mul_of_nonneg_left hbase hB
    _ ≤ B * (A * (R * (2 * PDE.vecEuclideanNorm (x - y) ^ (1 / 2 : ℝ))) *
        PDE.vecEuclideanNorm ξ) := by
      gcongr
      exact PDE.vecEuclideanNorm_nonneg ξ
    _ = _ := by ring

end EinsteinFull
