import EinsteinRelation.Correctors.GTRegularCoefficientSupport

/-!
# GT coefficient hypotheses on the doubled ball

Source: `paper/main.tex:198-207,727-729`. The local regular representative
on the unit ball comes from the weak equation on the doubled ball. The
actual reduced coefficient satisfies the same bounded half-Hölder estimate
on that doubled ball, with constants independent of the environment law.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- Global ellipticity and operator Lipschitz control imply the full
bounded half-Hölder coefficient norm on the ball of radius two. -/
theorem holderBound_half_twoBall_of_isElliptic_lipschitz {d : ℕ}
    {a : Vec d → Mat d} {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A)
    (ha : IsElliptic B a) (hlip : IsOperatorLipschitz A a) (i j : Fin d) :
    HolderBound (ball 0 2) (1 / 2) (fun x => a x i j) (B + 2 * A) := by
  refine ⟨B, 2 * A, hB.le, by positivity, le_rfl,
    fun x _ => IsElliptic.entry_abs_le hB ha x i j, ?_⟩
  intro x hx y hy
  have hx' : euclideanNorm x < 2 := by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hx
  have hy' : euclideanNorm y < 2 := by simpa only [ball, Set.mem_setOf_eq, sub_zero] using hy
  have hneg : euclideanNorm (-y) = euclideanNorm y := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp, TimeChange.euclideanNorm_eq_norm_toLp]
    exact norm_neg _
  have ht : euclideanNorm (x - y) ≤ 4 := by
    have htriangle := TimeChange.euclideanNorm_add_le x (-y)
    rw [hneg] at htriangle
    change euclideanNorm (x - y) ≤ euclideanNorm x + euclideanNorm y at htriangle
    exact htriangle.trans (by linarith only [hx', hy'])
  have hs : euclideanNorm (x - y) ≤ 2 * euclideanNorm (x - y) ^ (1 / (2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt (euclideanNorm (x - y)) ^ 2 = euclideanNorm (x - y) :=
      Real.sq_sqrt (Real.sqrt_nonneg (euclideanSq (x - y)))
    have hpos := Real.sqrt_nonneg (euclideanNorm (x - y))
    have hroot : Real.sqrt (euclideanNorm (x - y)) ≤ 2 := by
      have hfour : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
        norm_num
      simpa only [hfour] using Real.sqrt_le_sqrt ht
    nlinarith only [hsq, mul_nonneg hpos (sub_nonneg.mpr hroot)]
  calc |a x i j - a y i j| ≤ A * euclideanNorm (x - y) := hlip.entry_bound i j x y
    _ ≤ A * (2 * euclideanNorm (x - y) ^ (1 / (2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs hA
    _ = _ := by ring

/-- The doubled-ball coefficient hypotheses needed by GT Corollary 8.36
hold on the actual reduced image, with the same law-uniform constants. -/
theorem reduced_gt_twoBall_coefficient_hypotheses {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      EllipticBound (ball 0 2) ω.1 (sourceReducedBound L)⁻¹
        (((d : ℝ) + 1) * sourceReducedBound L) ∧
      ∀ i j, HolderBound (ball 0 2) (1 / 2) (fun x => ω.1 x i j)
        (sourceReducedBound L + 2 * (Real.exp (2 * L) * (L + 2 * L ^ 2))) := by
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q] with ω hω
  rcases hω with ⟨η, hη, rfl⟩
  have hb := sourceReducedBound_support Q.ellipticity_parameter hη
  have hB : 0 < sourceReducedBound L := zero_lt_one.trans_le hb.1
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  refine ⟨ellipticBound_of_isElliptic hB hb.2.1 ?_ _, ?_⟩
  · intro i j
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (reduce η).1.continuous)).measurable
  · exact holderBound_half_twoBall_of_isElliptic_lipschitz hB (by positivity)
      hb.2.1 hb.2.2.2.1

end EinsteinRelation.Correctors
