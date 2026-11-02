import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Environment.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

namespace EinsteinRelation.Correctors

private theorem euclideanNorm_eq_toLp_norm {d : ℕ} (v : Vec d) :
    euclideanNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (v i)).symm

private theorem euclideanNorm_add_le {d : ℕ} (v w : Vec d) :
    euclideanNorm (v+w) ≤ euclideanNorm v + euclideanNorm w := by
  simp only [euclideanNorm_eq_toLp_norm]
  exact norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 w)

private theorem euclideanNorm_smul {d : ℕ} (c : ℝ) (v : Vec d) :
    euclideanNorm (c • v) = |c| * euclideanNorm v := by
  simp only [euclideanNorm_eq_toLp_norm]
  change ‖c • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ = _
  rw [norm_smul, Real.norm_eq_abs]

/-- Quantitative clock Lipschitz bound from the actual bounded potential. -/
theorem clockDensity_lipschitz_bound {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hω : IsRegular L ω) (x y : Vec d) :
    |clockDensity ω x - clockDensity ω y| ≤
      (2 * Real.exp (2*L) * L) * euclideanNorm (x-y) := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (-2*r))
      (Real.exp (-2*s) * (-2)) s := by
    have hlin : HasDerivAt (fun r : ℝ => -2*r) (-2) s := by
      have h : HasDerivAt (fun r : ℝ => -2*r) (-2*1) s := (hasDerivAt_id s).const_mul (-2)
      rw [mul_one] at h
      exact h
    exact (Real.hasDerivAt_exp (-2*s)).comp s hlin
  have hbd : ∀ s ∈ Set.Icc (-L) L, ‖deriv (fun r : ℝ => Real.exp (-2*r)) s‖ ≤
      2 * Real.exp (2*L) := by
    intro s hs
    rw [(hd s).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [show |(-2 : ℝ)| = 2 by norm_num]
    have he : Real.exp (-2*s) ≤ Real.exp (2*L) := Real.exp_le_exp.mpr (by linarith [hs.1])
    linarith
  have hx := abs_le.mp (hω.2.1 x)
  have hy := abs_le.mp (hω.2.1 y)
  have hv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun r : ℝ => Real.exp (-2*r)) (s := Set.Icc (-L) L)
    (fun s _ => (hd s).differentiableAt) hbd (convex_Icc (-L) L) hy hx
  change |Real.exp (-2*ω.2 x) - Real.exp (-2*ω.2 y)| ≤ _
  have hv' : |Real.exp (-2*ω.2 x) - Real.exp (-2*ω.2 y)| ≤
      (2 * Real.exp (2*L)) * |ω.2 x - ω.2 y| := by simpa only [Real.norm_eq_abs] using hv
  calc _ ≤ (2 * Real.exp (2*L)) * |ω.2 x - ω.2 y| := hv'
    _ ≤ (2 * Real.exp (2*L)) * (L * euclideanNorm (x-y)) :=
      mul_le_mul_of_nonneg_left (hω.2.2.2 x y) (by positivity)
    _ = _ := by ring

/-- The source reduced coefficient has an operator Lipschitz constant depending only on L,
with no dimension factor or isotropy. Source paper/main.tex:198–207. -/
theorem reducedCoefficient_operatorLipschitz {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hL : 1 ≤ L) (hω : IsRegular L ω) :
    IsOperatorLipschitz (Real.exp (2*L) * (L + 2*L^2)) (reducedCoefficient ω) := by
  intro x y ξ
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hnxy : 0 ≤ euclideanNorm (x-y) := Real.sqrt_nonneg _
  have hdecomp : (reducedCoefficient ω x - reducedCoefficient ω y).mulVec ξ =
      clockDensity ω x • ((ω.1 x - ω.1 y).mulVec ξ) +
      (clockDensity ω x - clockDensity ω y) • ((ω.1 y).mulVec ξ) := by
    simp only [reducedCoefficient, Matrix.sub_mulVec, Matrix.smul_mulVec]
    module
  rw [hdecomp]
  calc _ ≤ euclideanNorm (clockDensity ω x • ((ω.1 x - ω.1 y).mulVec ξ)) +
        euclideanNorm ((clockDensity ω x - clockDensity ω y) • ((ω.1 y).mulVec ξ)) :=
      euclideanNorm_add_le _ _
    _ = clockDensity ω x * euclideanNorm ((ω.1 x - ω.1 y).mulVec ξ) +
        |clockDensity ω x - clockDensity ω y| * euclideanNorm ((ω.1 y).mulVec ξ) := by
      rw [euclideanNorm_smul, euclideanNorm_smul, abs_of_pos (clockDensity_pos ω x)]
    _ ≤ Real.exp (2*L) * (L * euclideanNorm (x-y) * euclideanNorm ξ) +
        ((2 * Real.exp (2*L) * L) * euclideanNorm (x-y)) * (L * euclideanNorm ξ) :=
      add_le_add
        (mul_le_mul (clockDensity_bounds ω x L (hω.2.1 x)).2 (hω.2.2.1 x y ξ)
          (Real.sqrt_nonneg _) (Real.exp_pos _).le)
        (mul_le_mul (clockDensity_lipschitz_bound hω x y)
          (isElliptic_mulVec_euclideanNorm_le hL0 hω.1 y ξ)
          (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (by positivity) hL0.le) hnxy))
    _ = _ := by ring
end EinsteinRelation.Correctors
