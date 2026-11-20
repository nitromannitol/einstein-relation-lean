import EinsteinFull.Regeneration.GMPCentralCubeHarnack

/-!
# Central-slab Harnack comparison for a positive force

A positive exponential force weight gives the same central-slab comparison,
with constants depending on the force as well as dimension and ellipticity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- A positive exponential force gives uniform Harnack comparison on the central slab. -/
theorem gmp_central_slab_harnack_of_force (d : ℕ) (hd : 0 < d) (lam Λ s : ℝ)
    (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (i : Fin d) (z z' : PDE.Vec d),
      z i = 0 → z' i = 0 → PDE.euclideanSqDist z z' ≤ d →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, 0 ≤ u.toFun x) → u z ≤ H * u z' := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let R : ℝ := Real.sqrt (8 * d)
  have hR : 0 < R := by dsimp [R]; positivity
  let m : ℝ := Real.exp (-(s * R))
  let M : ℝ := Real.exp (s * R)
  have hm : 0 < m := Real.exp_pos _
  have hM : m ≤ M := Real.exp_le_exp.mpr (by nlinarith [mul_pos hs hR])
  obtain ⟨H, hH, hcomp⟩ := weighted_elliptic_pointwise_harnack d hd lam Λ m M
    hlam hm hΛ hM
  refine ⟨H, hH, ?_⟩
  intro i z z' hz hz' hdist
  dsimp only
  intro a hmeas hell u hsol hcont hnonneg
  let center : PDE.Vec d := (1 / 2 : ℝ) • (z + z')
  let U := PDE.euclideanBall center R
  have hcenter : center i = 0 := by simp [center, hz, hz']
  have hweight : ∀ᵐ x ∂(volume.restrict U),
      m ≤ Real.exp (s * x i) ∧ Real.exp (s * x i) ≤ M := by
    filter_upwards [ae_restrict_mem (PDE.measurableSet_euclideanBall center R)] with x hx
    have hxnorm : PDE.vecEuclideanNorm (x - center) < R :=
      (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx
    have hcoord : |x i| < R := by
      have h := (PDE.abs_apply_le_vecEuclideanNorm (x - center) i).trans_lt hxnorm
      simpa only [Pi.sub_apply, hcenter, sub_zero] using h
    have hbounds := abs_lt.mp hcoord
    exact ⟨Real.exp_le_exp.mpr (by nlinarith), Real.exp_le_exp.mpr (by nlinarith)⟩
  have hθ : (0 : ℝ) < 4 * d := by positivity
  have hdist' : PDE.euclideanSqDist z z' ≤ (4 * (d : ℝ)) / 4 := by linarith
  have hrad : Real.sqrt (2 * (4 * (d : ℝ))) = R := by congr 1; ring
  have h := hcomp (4 * (d : ℝ)) hθ z z' hdist'
  dsimp only at h
  rw [hrad] at h
  exact h a (fun x => Real.exp (s * x i)) hmeas
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).measurable.aemeasurable)
    hell hweight u hsol hcont hnonneg

/-- The complementary central-slab solution satisfies force-dependent Harnack comparison. -/
theorem gmp_central_slab_complement_harnack_of_force (d : ℕ) (hd : 0 < d)
    (lam Λ s : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ H : ℝ, 2 ≤ H ∧ ∀ (i : Fin d) (z z' : PDE.Vec d),
      z i = 0 → z' i = 0 → PDE.euclideanSqDist z z' ≤ d →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → 1 - u z ≤ H * (1 - u z') := by
  obtain ⟨H, hH, hcomp⟩ := gmp_central_slab_harnack_of_force d hd lam Λ s hlam hΛ hs
  refine ⟨H, hH, ?_⟩
  intro i z z' hz hz' hdist
  dsimp only
  intro a hmeas hell u hsol hcont hupper
  let U := PDE.euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (8 * d))
  let : IsFiniteMeasure (volume.restrict U : Measure (PDE.Vec d)) :=
    isFiniteMeasure_restrict.mpr (PDE.volume_euclideanBall_ne_top _ (Real.sqrt_nonneg _))
  let v : PDE.H1Function U := (-u).addConst 1
  have hv : PDE.IsWeakDivergenceFormL2SolutionOn
      (fun x => Real.exp (s * x i) • a x) U v 0 0 :=
    elliptic_l2_solution_const_sub (fun x => Real.exp (s * x i) • a x) u hsol 1
  have hval (x : PDE.Vec d) : v x = 1 - u x := by
    simp only [v, PDE.H1Function.addConst_apply, PDE.H1Function.neg_toFun]
    ring
  have hvcont : Continuous v.toFun := by
    have heq : v.toFun = fun x => 1 - u x := funext hval
    rw [heq]
    exact continuous_const.sub hcont
  have hvnonneg : ∀ x, 0 ≤ v x := fun x => by rw [hval]; linarith [hupper x]
  have h := hcomp i z z' hz hz' hdist
  dsimp only at h
  have hh := h a hmeas hell v hv hvcont hvnonneg
  simpa only [hval] using hh

/-- A central value below `2 / 3` gives a uniform positive complement on the unit cube. -/
theorem gmp_central_cube_complement_lower_of_force (d : ℕ) (hd : 0 < d)
    (lam Λ s : ℝ) (hlam : 0 < lam) (hΛ : lam ≤ Λ) (hs : 0 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (z : PDE.Vec d), z i = 0 →
      (∀ j, |z j| ≤ 1) →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • ((0 : PDE.Vec d) + z))
        (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 → c ≤ 1 - u z := by
  obtain ⟨H, hH, hcomp⟩ :=
    gmp_central_slab_complement_harnack_of_force d hd lam Λ s hlam hΛ hs
  have hHpos : 0 < H := by linarith
  refine ⟨1 / (3 * H), by positivity, ?_⟩
  intro i z hzi hz
  dsimp only
  intro a hmeas hell u hsol hcont hupper hsmall
  have h := hcomp i 0 z (by simp) hzi (euclideanSqDist_zero_le_dim_of_abs_le_one z hz)
  dsimp only at h
  have hh := h a hmeas hell u hsol hcont hupper
  apply (div_le_iff₀ (by positivity : 0 < 3 * H)).2
  nlinarith

end EinsteinFull.Regeneration
