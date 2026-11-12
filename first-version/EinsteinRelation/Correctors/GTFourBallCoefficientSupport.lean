import EinsteinRelation.Correctors.GTRegularCoefficientSupport

/-! Source: `paper/main.tex:727-731`. Uniform coefficient hypotheses
on the radius-four balls used in the repaired corrector proof. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- Global operator Lipschitz control bounds the half-Hölder norm on
every Euclidean radius-four ball, uniformly in its center. -/
theorem holderBound_half_of_isElliptic_lipschitz_ball_four {d : ℕ}
    {a : Vec d → Mat d} {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A)
    (ha : IsElliptic B a) (hlip : IsOperatorLipschitz A a)
    (z : Vec d) (i j : Fin d) :
    HolderBound (ball z 4) (1 / 2) (fun x => a x i j) (B + 3 * A) := by
  refine ⟨B, 3 * A, hB.le, by positivity, le_rfl,
    fun x _ => IsElliptic.entry_abs_le hB ha x i j, ?_⟩
  intro x hx y hy
  change euclideanNorm (x - z) < 4 at hx
  change euclideanNorm (y - z) < 4 at hy
  have hdist : euclideanNorm (x - y) < 8 := by
    have hnorm : euclideanNorm (-(y - z)) = euclideanNorm (y - z) := by
      rw [TimeChange.euclideanNorm_eq_norm_toLp, TimeChange.euclideanNorm_eq_norm_toLp]
      simp [norm_sub_rev]
    have h := TimeChange.euclideanNorm_add_le (x - z) (-(y - z))
    rw [hnorm, show x - z + -(y - z) = x - y by abel] at h
    exact h.trans_lt (by linarith)
  have hs := Real.sq_sqrt (show 0 ≤ euclideanNorm (x - y) from Real.sqrt_nonneg _)
  have hn := Real.sqrt_nonneg (euclideanNorm (x - y))
  have hroot : euclideanNorm (x - y) ≤ 3 *
      euclideanNorm (x - y) ^ (1 / (2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith
  calc
    _ ≤ A * euclideanNorm (x - y) := hlip.entry_bound i j x y
    _ ≤ A * (3 * euclideanNorm (x - y) ^ (1 / (2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hroot hA
    _ = _ := by ring

/-- The deterministic GT constants precede the law and every local
center, including centers selected in the large-radius integration. -/
theorem reduced_gt_coefficient_hypotheses_ball_four {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ z : Vec d,
      EllipticBound (ball z 4) ρ.1 (sourceReducedBound L)⁻¹
        (((d : ℝ) + 1) * sourceReducedBound L) ∧
      ∀ i j, HolderBound (ball z 4) (1 / 2) (fun x => ρ.1 x i j)
        (sourceReducedBound L + 3 * (Real.exp (2 * L) * (L + 2 * L ^ 2))) := by
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ρ hρ
  obtain ⟨η, hη, rfl⟩ := hρ
  have hb := sourceReducedBound_support Q.ellipticity_parameter hη
  have hB : 0 < sourceReducedBound L := zero_lt_one.trans_le hb.1
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  intro z
  refine ⟨ellipticBound_of_isElliptic hB hb.2.1 ?_ _, ?_⟩
  · intro i j
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (reduce η).1.continuous)).measurable
  · exact holderBound_half_of_isElliptic_lipschitz_ball_four hB
      (by positivity) hb.2.1 hb.2.2.2.1 z

end EinsteinRelation.Correctors
