import EinsteinFull.Regeneration.WeightedEllipticHarnack

/-!
# Harnack comparison on the central slab

The exponential coefficient weight in Gantert–Mathieu–Piatnitski, Lemma 4.4,
is uniformly bounded on the comparison ball around two central-slab points.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The central-slab exponential weight gives uniform pointwise comparison. -/
theorem gmp_central_slab_harnack (d : ℕ) (hd : 0 < d) (lam Λ : ℝ)
    (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (i : Fin d) (z z' : PDE.Vec d),
      z i = 0 → z' i = 0 → PDE.euclideanSqDist z z' ≤ d →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, 0 ≤ u.toFun x) → u z ≤ H * u z' := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let R : ℝ := Real.sqrt (8 * d)
  have hR : 0 < R := by dsimp [R]; positivity
  let m : ℝ := Real.exp (-R)
  let M : ℝ := Real.exp R
  have hm : 0 < m := Real.exp_pos _
  have hM : m ≤ M := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨H, hH, hcomp⟩ := weighted_elliptic_pointwise_harnack d hd lam Λ m M
    hlam hm hΛ hM
  refine ⟨H, hH, ?_⟩
  intro i z z' hz hz' hdist
  dsimp only
  intro a hmeas hell u hsol hcont hnonneg
  let center : PDE.Vec d := (1 / 2 : ℝ) • (z + z')
  let U := PDE.euclideanBall center R
  have hcenter : center i = 0 := by simp [center, hz, hz']
  have hweight : ∀ᵐ x ∂(volume.restrict U), m ≤ Real.exp (x i) ∧ Real.exp (x i) ≤ M := by
    filter_upwards [ae_restrict_mem (PDE.measurableSet_euclideanBall center R)] with x hx
    have hxnorm : PDE.vecEuclideanNorm (x - center) < R :=
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx
    have hcoord : |x i| < R := by
      have h := (PDE.abs_apply_le_vecEuclideanNorm (x - center) i).trans_lt hxnorm
      simpa only [Pi.sub_apply, hcenter, sub_zero] using h
    have hbounds := abs_lt.mp hcoord
    exact ⟨Real.exp_le_exp.mpr hbounds.1.le, Real.exp_le_exp.mpr hbounds.2.le⟩
  have hθ : (0 : ℝ) < 4 * d := by positivity
  have hdist' : PDE.euclideanSqDist z z' ≤ (4 * (d : ℝ)) / 4 := by linarith
  have hrad : Real.sqrt (2 * (4 * (d : ℝ))) = R := by congr 1; ring
  have h := hcomp (4 * (d : ℝ)) hθ z z' hdist'
  dsimp only at h
  rw [hrad] at h
  exact h a (fun x => Real.exp (x i)) hmeas
    ((Real.continuous_exp.comp (continuous_apply i)).measurable.aemeasurable)
    hell hweight u hsol hcont hnonneg

end EinsteinFull.Regeneration
