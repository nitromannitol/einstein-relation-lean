import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.Correctors.EllipticOperatorBound
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integrability in the AKM parabolic weak equation

Source: `paper/main.tex:779–800,812–830`; AKM (8.2), (8.6), printed
pp. 302–303. Joint measurability of the actual gradient, its Euclidean
square integrability and the coefficient bounds make every smooth-test
pairing a genuine integrable function. The weak equation therefore cannot
hold merely because a nonmeasurable Bochner integrand has integral zero.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open Environment.AKMTestIntegralSupport External.AKM

private theorem coordinate_abs_le {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  apply Real.abs_le_sqrt
  change v j ^ 2 ≤ ∑ k : Fin d, v k * v k
  rw [sq]
  exact Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)

/-- Each flux coordinate is square integrable for the corrected parabolic
energy predicate. Source: `paper/main.tex:779–800,812–830`. -/
theorem parabolicSolution_flux_coordinate_memLp {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G) (j : Fin d) :
    MemLp (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j) 2
      (volume.restrict (I ×ˢ U)) := by
  have hAm (i k : Fin d) :
      AEStronglyMeasurable (fun z : ℝ × Vec d => A z.2 i k)
        (volume.restrict (I ×ˢ U)) :=
    (A.locally_integrable i k).aestronglyMeasurable.comp_snd.mono_measure
      Measure.restrict_le_self
  have hGm (k : Fin d) : AEStronglyMeasurable (fun z => G z k)
      (volume.restrict (I ×ˢ U)) :=
    (continuous_apply k).comp_aestronglyMeasurable hsol.2.1
  have hfluxm : AEStronglyMeasurable
      (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j)
      (volume.restrict (I ×ˢ U)) :=
    by simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply] using
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ => (hAm j k).mul (hGm k))
  apply hsol.2.2.1.of_le_mul hfluxm (c := K)
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
    exact (coordinate_abs_le _ j).trans
      (mulVec_euclideanNorm_le_of_quadratic (A z.2) hK (A.symmetric z.2)
        (fun ξ => (by
          change 0 ≤ ∑ k : Fin d, ξ k * ξ k
          exact Finset.sum_nonneg fun k _ => mul_self_nonneg (ξ k) :
          0 ≤ euclideanSq ξ).trans (A.elliptic z.2 ξ).1)
        (fun ξ => (A.elliptic z.2 ξ).2) (G z))

/-- The complete space-time weak-equation integrand is integrable for
every compactly supported smooth test. Source: `paper/main.tex:812–830`.
No finite-volume cylinder assumption or equation-integrability premise is
needed. -/
theorem parabolicSolution_test_integrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ψ : ℝ × Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z : ℝ × Vec d =>
      -(u z) * fderiv ℝ ψ z (1, 0) +
        dot ((A z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j)))
      (volume.restrict (I ×ˢ U)) := by
  have hD (v : ℝ × Vec d) :
      MemLp (fun z => fderiv ℝ ψ z v) 2 (volume.restrict (I ×ˢ U)) := by
    have hc : Continuous (fun z => fderiv ℝ ψ z v) :=
      ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
    exact (hc.memLp_of_hasCompactSupport (hψc.fderiv_apply ℝ v)).mono_measure
      Measure.restrict_le_self
  exact (hsol.1.neg.integrable_mul (hD (1, 0))).add
    (integrable_finset_sum Finset.univ fun j _ =>
      (parabolicSolution_flux_coordinate_memLp hK A hsol j).integrable_mul
        (hD (0, unitVector j)))

end EinsteinRelation.Correctors
