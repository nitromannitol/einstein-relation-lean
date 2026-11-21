import EinsteinFull.Regeneration.CenteredSlabLocalStep
import EinsteinFull.Regeneration.SlabShellArithmetic

/-!
# Normalized centered slab energy step

A bound on the cutoff gradient at the exponential shell scale turns the
explicit centered energy estimate into the standard affine recurrence.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A centered slab step has exponential error and energy coefficient when the
cutoff gradient has the matching scale. -/
theorem centered_slab_energy_normalized_step_of_local_solution
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ R C : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hR : 0 < R) (hC : 0 ≤ C)
    (hRmax : R ≤ Real.exp (s * L / (n + 1)))
    (hK : (32 * (n + 1 : ℝ)) / (R / 2) ≤ C * Real.exp (-(s * L / (n + 1))))
    (hsource : coordinateSlabBox n i s L ⊆ U)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, -L + δ k < L - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1)
    (hleft : ∀ᵐ z ∂(volume.restrict
      (transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R))),
      u (centralSlabPoint n i (-L, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict
      (transverseClosedBox i (centeredSlabLower i L R) (centeredSlabUpper i L R))),
      u (centralSlabPoint n i (L, z)) = 1)
    (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ)
    (hsol : ∃ hQU : centeredSlabBox i L R ⊆ U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (centeredSlabBox i L R)
        (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) :
    IntegrableOn (slabWeightedEnergy A s i u.grad) (centeredSlabBox i L R) ∧
    IntegrableOn (slabWeightedEnergy A s i u.grad) (centeredSlabBox i L (R / 2)) ∧
    (∫ x in centeredSlabBox i L (R / 2), slabWeightedEnergy A s i u.grad x) ≤
      ((Real.exp s * 2 ^ n) * Λ * (1 + C ^ 2 + 3 * C)) * Real.exp (-(s * L / (n + 1))) +
      (Λ * (4 * C ^ 2 + 6 * C) / lam) * L ^ 2 * Real.exp (-(s * L / (n + 1))) *
        ∫ x in centeredSlabBox i L R, slabWeightedEnergy A s i u.grad x := by
  let ε : ℝ := Real.exp (-(s * L / (n + 1)))
  let K : ℝ := (32 * (n + 1 : ℝ)) / (R / 2)
  let D : ℝ := Real.exp s * 2 ^ n
  have hε : 0 ≤ ε := (Real.exp_pos _).le
  have hε1 : ε ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hd : (0 : ℝ) < n + 1 := by positivity
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg hs (by linarith)) hd.le)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoef := slab_shell_coefficients_le lam Λ C ε K D L hlam hΛ hC hε hε1 hK0 hK hD hL
  dsimp only at hcoef
  have hstep := centered_slab_energy_step_of_local_solution hU u i L s lam Λ R hL hs hlam hΛ hR hRmax
    hsource δ hδ hδpos hthin hr hball hcont hzero hone hleft hright A lam' Λ' hsol hEll hA hsym
  dsimp only at hstep
  have hQsub : centeredSlabBox i L R ⊆ U := by
    have hclosed := centeredSlab_closed_subset_source i s L R hRmax
    have hbox := axisBox_subset_closedCoordinateBox i (centeredSlabLower i L R)
      (centeredSlabUpper i L R)
    have hbox' : centeredSlabBox i L R ⊆
        closedCoordinateBox i (centeredSlabLower i L R) (centeredSlabUpper i L R) (-L) L := by
      simpa only [centeredSlabBox, centeredSlabLower, centeredSlabUpper, ite_true] using hbox
    exact hbox'.trans (hclosed.trans hsource)
  have hnonneg : 0 ≤ ∫ x in centeredSlabBox i L R, slabWeightedEnergy A s i u.grad x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (PDE.isOpen_axisBox _ _).measurableSet] with x hx
    have hell := hEll.elliptic (hQsub hx)
    have h := hell.coercive (u.grad x)
    have h0 := mul_nonneg hell.lam_pos.le (PDE.vecNormSq_nonneg (u.grad x))
    exact h0.trans (by simpa only [slabWeightedEnergy, matrixEnergy, PDE.vecDot_comm] using h)
  have hmul := mul_le_mul_of_nonneg_right hcoef.2 hnonneg
  refine ⟨hstep.1, hstep.2.1, ?_⟩
  dsimp only [ε, K, D] at hcoef hmul
  nlinarith [hstep.2.2, hcoef.1, hmul]

end EinsteinFull.Regeneration
