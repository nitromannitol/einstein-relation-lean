import EinsteinFull.Regeneration.GMPCentralCubeHarnack
import PDEFoundation.PDE.DGNM.Bridge
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Energy minimality for symmetric elliptic equations

Testing a homogeneous weak equation with a zero-boundary perturbation gives
its energy comparison with the perturbed function.
-/

open MeasureTheory

namespace EinsteinFull.Regeneration

/-- A symmetric matrix has symmetric bilinear pairings. -/
theorem symmetric_flux_pairing {d : ℕ} (A : PDE.Mat d) (hA : A.IsSymm)
    (v w : PDE.Vec d) :
    PDE.vecDot (PDE.matVecMul A v) w = PDE.vecDot (PDE.matVecMul A w) v := by
  change dotProduct (A.mulVec v) w = dotProduct (A.mulVec w) v
  rw [dotProduct_comm (A.mulVec v) w, dotProduct_comm (A.mulVec w) v]
  exact hA.dotProduct_mulVec_comm

/-- A symmetric quadratic energy expands along a perturbation. -/
theorem symmetric_energy_add {d : ℕ} (A : PDE.Mat d) (hA : A.IsSymm)
    (v w : PDE.Vec d) :
    PDE.vecDot (PDE.matVecMul A (v + w)) (v + w) =
      PDE.vecDot (PDE.matVecMul A v) v +
      2 * PDE.vecDot (PDE.matVecMul A v) w +
      PDE.vecDot (PDE.matVecMul A w) w := by
  have hm : PDE.matVecMul A (v + w) = PDE.matVecMul A v + PDE.matVecMul A w := by
    exact Matrix.mulVec_add A v w
  rw [hm, PDE.DGNM.vecDot_add_left, PDE.DGNM.vecDot_add_right,
    PDE.DGNM.vecDot_add_right, symmetric_flux_pairing A hA w v]
  ring

/-- A symmetric homogeneous weak solution minimizes energy under zero-boundary perturbations. -/
theorem elliptic_energy_le_of_h10_perturbation {d : ℕ} {U : Set (PDE.Vec d)}
    (a : PDE.CoeffField d) (u : PDE.H1Function U)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0) (φ : PDE.H10Function U)
    (hflux : PDE.MemVectorL2On U (fun x => PDE.matVecMul (a x) (φ.toH1Function.grad x)))
    (hsym : ∀ᵐ x ∂(volume.restrict U), (a x).IsSymm)
    (hpositive : ∀ᵐ x ∂(volume.restrict U),
      0 ≤ PDE.vecDot (PDE.matVecMul (a x) (φ.toH1Function.grad x)) (φ.toH1Function.grad x)) :
    IntegrableOn (fun x => PDE.vecDot (PDE.matVecMul (a x) (u.grad x + φ.toH1Function.grad x))
      (u.grad x + φ.toH1Function.grad x)) U ∧
      (∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (u.grad x)) ≤
        ∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (u.grad x + φ.toH1Function.grad x))
          (u.grad x + φ.toH1Function.grad x) := by
  let G := u.grad
  let W := φ.toH1Function.grad
  let E : PDE.Vec d → ℝ := fun x => PDE.vecDot (PDE.matVecMul (a x) (G x)) (G x)
  let B : PDE.Vec d → ℝ := fun x => PDE.vecDot (PDE.matVecMul (a x) (G x)) (W x)
  let Q : PDE.Vec d → ℝ := fun x => PDE.vecDot (PDE.matVecMul (a x) (W x)) (W x)
  have hE : IntegrableOn E U := PDE.integrableOn_vecDot_of_memVectorL2On
    hsol.flux_memL2 u.gradMemL2
  have hB : IntegrableOn B U := PDE.integrableOn_vecDot_of_memVectorL2On
    hsol.flux_memL2 φ.toH1Function.gradMemL2
  have hQ : IntegrableOn Q U := PDE.integrableOn_vecDot_of_memVectorL2On
    hflux φ.toH1Function.gradMemL2
  have hcross : (∫ x in U, B x) = 0 := by
    have h := (hsol.toH10SolutionOn φ).2
    simpa only [B, G, W, Pi.zero_apply, zero_mul, PDE.vecDot,
      Finset.sum_const_zero, integral_zero, sub_zero] using h
  have hQnonneg : 0 ≤ ∫ x in U, Q x := integral_nonneg_of_ae hpositive
  have hexp : ∀ᵐ x ∂(volume.restrict U),
      PDE.vecDot (PDE.matVecMul (a x) (G x + W x)) (G x + W x) =
        E x + 2 * B x + Q x := by
    filter_upwards [hsym] with x hx
    exact symmetric_energy_add (a x) hx (G x) (W x)
  have hsum : IntegrableOn (fun x => E x + 2 * B x + Q x) U :=
    (hE.add (hB.const_mul 2)).add hQ
  have hpert : IntegrableOn (fun x => PDE.vecDot (PDE.matVecMul (a x) (G x + W x))
      (G x + W x)) U := hsum.congr (hexp.mono fun _ hx => hx.symm)
  refine ⟨hpert, ?_⟩
  change (∫ x in U, E x) ≤ ∫ x in U,
    PDE.vecDot (PDE.matVecMul (a x) (G x + W x)) (G x + W x)
  have hsumEq := integral_add (hE.add (hB.const_mul 2)) hQ
  have hfirstEq := integral_add hE (hB.const_mul 2)
  simp only [Pi.add_apply] at hsumEq hfirstEq
  rw [integral_congr_ae hexp, hsumEq, hfirstEq, integral_const_mul, hcross]
  linarith

/-- Symmetric uniform ellipticity supplies the energy comparison for every `H¹₀` perturbation. -/
theorem elliptic_energy_le_of_symmetric_ellipticity {d : ℕ} {U : Set (PDE.Vec d)}
    {lam Λ : ℝ} (a : PDE.CoeffField d) (u : PDE.H1Function U)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0) (φ : PDE.H10Function U)
    (hEll : PDE.IsEllipticFieldOn lam Λ U a)
    (hsym : ∀ᵐ x ∂(volume.restrict U), (a x).IsSymm) :
    IntegrableOn (fun x => PDE.vecDot (PDE.matVecMul (a x) (u.grad x + φ.toH1Function.grad x))
      (u.grad x + φ.toH1Function.grad x)) U ∧
      (∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (u.grad x)) ≤
        ∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (u.grad x + φ.toH1Function.grad x))
          (u.grad x + φ.toH1Function.grad x) := by
  have hflux := PDE.memVectorL2On_matVecMul_of_isEllipticFieldOn hEll φ.toH1Function.gradMemL2
  apply elliptic_energy_le_of_h10_perturbation a u hsol φ hflux hsym
  filter_upwards [ae_restrict_mem (PDE.measurableSet_of_isEllipticFieldOn hEll)] with x hx
  have hA := hEll.elliptic hx
  have h := hA.coercive (φ.toH1Function.grad x)
  have hp : 0 ≤ lam * PDE.vecNormSq (φ.toH1Function.grad x) :=
    mul_nonneg hA.lam_pos.le (PDE.vecNormSq_nonneg _)
  exact hp.trans (by simpa only [PDE.vecDot_comm] using h)

end EinsteinFull.Regeneration
