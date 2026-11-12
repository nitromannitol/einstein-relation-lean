import EinsteinRelation.Correctors.PoissonLiftWeakSolution
import EinsteinRelation.Correctors.PoissonLiftSquareIntegral
import EinsteinRelation.Correctors.PoissonLiftSliceBound

/-! Source: `paper/main.tex:735-739`. A local bound for the actual
inhomogeneous scalar equation, derived from the existing homogeneous GT
8.17 input by the explicit dimensional lift. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- A locally bounded divergence source gives a local value bound using
only the frozen homogeneous GT estimate. The constant is chosen before
the solution, the source, and its bound. -/
theorem poisson_local_bound_of_GT
    (h817 : LocalBoundednessEstimate) (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Vec d → ℝ) (g F : Vec d → Vec d),
      HasWeakGradient Set.univ u g →
      HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0) →
      Measurable F → ∀ M : ℝ, 0 < M →
      (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), euclideanNorm (F x) ≤ M) →
      MemLp u 2 (volume.restrict (ball 0 1)) →
      MemLp g 2 (volume.restrict (ball 0 1)) →
      ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) (1 / 4)),
        |u x| ≤ C * (Real.sqrt (∫ y in ball (0 : Vec d) 1, |u y| ^ 2) + M) := by
  obtain ⟨K, hK, hest⟩ := h817 (d + 1) (by omega) (1 / 4)
    (2 * ((d : ℝ) + 1)) 2 (by norm_num) (by positivity) (by norm_num)
  let A : ℝ := K * (1 / 2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ) / 2)
  let D : ℝ := 4 + 4 * (2 : ℝ) ^ d
  have hA : 0 < A := mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨1 + A * D, by positivity, ?_⟩
  intro u g F hw hJ hF M hM hFn hu hg
  let a : Vec (d + 1) → Mat (d + 1) := fun x =>
    poissonLiftMatrix (clippedPoissonSource F M (poissonLiftBase x))
  have hbase : Measurable (poissonLiftBase : Vec (d + 1) → Vec d) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
  have ha : EllipticBound (ball (0 : Vec (d + 1)) 1) a
      (1 / 4) (2 * ((d : ℝ) + 1)) :=
    poissonLiftMatrix_ellipticBound _ _
      ((measurable_clippedPoissonSource F hF M).comp hbase)
      (fun x _ => euclideanNorm_clippedPoissonSource_le F M hM _)
  have hsol := weakSolution_poissonLift u g F hw hJ hF M hM hFn hu hg
  have hopen : IsOpen (ball (0 : Vec (d + 1)) 1) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hlift := hest _ hopen a ha _ _ hsol 0 (1 / 2) (by norm_num)
    (by norm_num) (by simpa only [ENNReal.ofReal_ofNat,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num] using hsol.1)
  have hlift' : ∀ᵐ x ∂volume.restrict (ball (0 : Vec (d + 1)) (1 / 2)),
      |poissonLiftPotential u M x| ≤
        A * Real.sqrt (∫ y in ball (0 : Vec (d + 1)) 1,
          |poissonLiftPotential u M y| ^ 2) := by
    simpa only [A, Real.sqrt_eq_rpow, Real.rpow_two,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num] using hlift
  have humeas : AEStronglyMeasurable u (volume : Measure (Vec d)) := by
    by_cases hd0 : 0 < d
    · exact (locallyIntegrableOn_univ.mp (hw ⟨0, hd0⟩).1).aestronglyMeasurable
    · omega
  have hsliced := ae_abs_le_of_poissonLift_bound u humeas M _ hlift'
  have hI : 0 ≤ ∫ y in ball (0 : Vec d) 1, |u y| ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hsq := integral_sq_poissonLift_le u hu M
  have hroot : Real.sqrt (∫ y in ball (0 : Vec (d + 1)) 1,
      |poissonLiftPotential u M y| ^ 2) ≤
      D * (Real.sqrt (∫ y in ball (0 : Vec d) 1, |u y| ^ 2) + M) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hs := Real.sq_sqrt hI
    have hs0 := Real.sqrt_nonneg (∫ y in ball (0 : Vec d) 1, |u y| ^ 2)
    have hV : 0 ≤ (2 : ℝ) ^ d := by positivity
    have hD2 : 4 ≤ D ^ 2 ∧ 4 * (2 : ℝ) ^ d ≤ D ^ 2 := by
      dsimp [D]
      constructor <;> nlinarith [sq_nonneg ((2 : ℝ) ^ d)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hD2.1) hI,
      mul_nonneg (sub_nonneg.mpr hD2.2) (sq_nonneg M),
      mul_nonneg (sq_nonneg D) (mul_nonneg hs0 hM.le)]
  filter_upwards [hsliced] with x hx
  rw [abs_of_pos hM] at hx
  have hmult := mul_le_mul_of_nonneg_left hroot hA.le
  have hs0 := Real.sqrt_nonneg (∫ y in ball (0 : Vec d) 1, |u y| ^ 2)
  change |u x| ≤ (1 + A * D) *
    (Real.sqrt (∫ y in ball (0 : Vec d) 1, |u y| ^ 2) + M)
  nlinarith

end EinsteinRelation.Correctors
