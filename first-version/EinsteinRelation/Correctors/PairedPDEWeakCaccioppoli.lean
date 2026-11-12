import EinsteinRelation.Correctors.PairedPDEWeakEnergy
import EinsteinRelation.Correctors.PairedPDECoercivity

/-! # Caccioppoli for the actual energy-class solution

Source: `paper/main.tex:832–840`. The weak cutoff identity and the
anisotropic quadratic bound absorb the actual cross term. No smoothness
of the solution or initial energy trace is assumed.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A compact space-time cutoff gives a genuine weak Caccioppoli estimate,
including integrability of its principal energy and spatial error.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_energy {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U) :
    Integrable (fun z => ζ z ^ 2 * euclideanSq (G z)) (volume.restrict (I ×ˢ U)) ∧
      Integrable (fun z => (u z)^2 *
        euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)))
        (volume.restrict (I ×ˢ U)) ∧
      (∫ z in I ×ˢ U, ζ z ^ 2 * euclideanSq (G z)) ≤
        2 * (∫ z in I ×ˢ U, (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0)) +
          4 * K^2 * ∫ z in I ×ˢ U, (u z)^2 *
            euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) := by
  let μ := volume.restrict (I ×ˢ U)
  let E := fun z => ζ z ^ 2 * euclideanSq (G z)
  let Err := fun z => (u z)^2 * euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j))
  let P := fun z => dot ((A z.2).mulVec (G z))
    (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j))
  have hζm : MemLp ζ ∞ μ := hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  have hD (j : Fin d) : MemLp (fun z => fderiv ℝ ζ z (0, unitVector j)) ∞ μ :=
    ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
      |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (0, unitVector j)) _
  have hE : Integrable E μ := by
    have hi := integrable_finset_sum Finset.univ fun j (_ : j ∈ Finset.univ) =>
      ((parabolicSolution_gradient_coordinate_memLp hsol j).mul' hζm).integrable_sq
    convert hi using 1
    funext z
    simp only [E, euclideanSq, dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hErr : Integrable Err μ := by
    have hi := integrable_finset_sum Finset.univ fun j (_ : j ∈ Finset.univ) =>
      ((hD j).mul' hsol.1).integrable_sq
    convert hi using 1
    funext z
    simp only [Err, euclideanSq, dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hP := parabolicSolution_regularized_cutoff_energy_identity hK hI hU hsol hζ hζc hζsupp
  have hpoint (z : ℝ × Vec d) : E z ≤ 2 * P z + 4 * K^2 * Err z := by
    have h := paired_cutoff_coercivity hK A z.2 (ζ z • G z)
      (fun j => fderiv ℝ ζ z (0, unitVector j)) (u z) 1 (by norm_num) 1 (by norm_num)
    norm_num only [Nat.cast_one, one_pow, one_mul, Nat.mul_one, Nat.reduceSub,
      Nat.cast_ofNat] at h
    rw [euclideanSq_smul, Matrix.mulVec_smul] at h
    have heq : dot (ζ z • G z) (ζ z • (A z.2).mulVec (G z)) =
        ζ z ^ 2 * dot (G z) ((A z.2).mulVec (G z)) := by
      change dotProduct (ζ z • G z) (ζ z • (A z.2).mulVec (G z)) = _
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      change _ = ζ z ^ 2 * dotProduct (G z) ((A z.2).mulVec (G z))
      ring
    rw [heq] at h
    have hc : dot (ζ z • (A z.2).mulVec (G z))
        (fun j => fderiv ℝ ζ z (0, unitVector j)) =
        ζ z * dot ((A z.2).mulVec (G z))
          (fun j => fderiv ℝ ζ z (0, unitVector j)) :=
      smul_dotProduct _ _ _
    rw [hc] at h
    have hp : P z = ζ z ^ 2 * dot (G z) ((A z.2).mulVec (G z)) +
        2 * ζ z * u z * dot ((A z.2).mulVec (G z))
          (fun j => fderiv ℝ ζ z (0, unitVector j)) := by
      have hcomm : dot ((A z.2).mulVec (G z)) (G z) =
          dot (G z) ((A z.2).mulVec (G z)) := dotProduct_comm _ _
      rw [← hcomm]
      simp only [P, dot, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hp]
    dsimp only [E, Err]
    convert h using 1
    ring
  have hle := integral_mono hE ((hP.1.const_mul 2).add (hErr.const_mul (4 * K^2))) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hP.1.const_mul 2) (hErr.const_mul (4 * K^2)),
    integral_const_mul, integral_const_mul, hP.2] at hle
  exact ⟨hE, hErr, hle⟩

end EinsteinRelation.Correctors
