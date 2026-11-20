import EinsteinFull.Homogenization.SourceEnergyMeanConvergence
import Mathlib.Probability.Moments.Variance

/-!
# Dual-energy fluctuations

The bounded dual energies of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, have
vanishing variance on large triadic cubes under finite-range dependence.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The variance of the dual energy tends to zero at large triadic scales. -/
theorem tendsto_variance_sourceDualEnergy
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q : Vec d) :
    Tendsto (fun n : ℕ => ProbabilityTheory.variance
      (fun a => sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q) P)
      atTop (𝓝 0) := by
  let E : ℕ → Coefficient d K → ℝ := fun n a =>
    sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q
  let L : ℝ := ⨅ n : ℕ, ∫ a, E n a ∂P
  let B : ℝ := vecNormSq q
  have hB : 0 ≤ B := vecNormSq_nonneg q
  have hL₀ : 0 ≤ L := by
    apply ge_of_tendsto (tendsto_expected_sourceDualEnergy P hstat q)
    exact Filter.Eventually.of_forall fun n => integral_nonneg fun a =>
      (sourceDualEnergy_originCube_bounds a n q).1
  have hL₁ : L ≤ B := by
    apply le_of_tendsto (tendsto_expected_sourceDualEnergy P hstat q)
    exact Filter.Eventually.of_forall fun n => by
      have h := integral_mono (integrable_sourceDualEnergy_originCube P n q)
        (integrable_const B) (fun a => (sourceDualEnergy_originCube_bounds a n q).2)
      simpa only [integral_const, probReal_univ, one_smul] using h
  have hlim : Tendsto (fun n : ℕ => ∫ a, |E n a - L| ∂P) atTop (𝓝 0) :=
    tendsto_integral_abs_sourceDualEnergy_sub_limit hK P hP hstat q
  have hlim' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => B) atTop (𝓝 B)).mul hlim
  simp only [mul_zero] at hlim'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun n => ProbabilityTheory.variance_nonneg _ _) ?_
  intro n
  have hint : Integrable (E n) P := integrable_sourceDualEnergy_originCube P n q
  have hd : Integrable (fun a => E n a - L) P := hint.sub (integrable_const L)
  have hpoint (a : Coefficient d K) : (E n a - L) ^ 2 ≤ B * |E n a - L| := by
    have hb := sourceDualEnergy_originCube_bounds a n q
    have hbound : |E n a - L| ≤ B := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
    nlinarith [abs_nonneg (E n a - L), sq_abs (E n a - L)]
  have hsquare : Integrable (fun a => (E n a - L) ^ 2) P := by
    apply (hd.abs.const_mul B).mono' (by fun_prop)
    filter_upwards [] with a
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint a
  have hv := ProbabilityTheory.variance_le_expectation_sq hd.aestronglyMeasurable
  rw [ProbabilityTheory.variance_sub_const hint.aestronglyMeasurable] at hv
  calc
    _ ≤ ∫ a, (E n a - L) ^ 2 ∂P := hv
    _ ≤ ∫ a, B * |E n a - L| ∂P :=
      integral_mono hsquare (hd.abs.const_mul B) hpoint
    _ = B * ∫ a, |E n a - L| ∂P := integral_const_mul B _

end EinsteinFull.Homogenization
