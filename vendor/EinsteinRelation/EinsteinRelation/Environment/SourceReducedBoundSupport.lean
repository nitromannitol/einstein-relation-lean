import EinsteinRelation.Environment.Bounds
import EinsteinRelation.Correctors.ReducedOperatorLipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace EinsteinRelation

/-- A concrete value of the reduced-field bound `Λ(L)` in
`paper/main.tex`, equation `eq.reduced-bounds`, depending only on the original
coefficient and potential bound `L`. -/
noncomputable def sourceReducedBound (L : ℝ) : ℝ :=
  Real.exp (2 * L) * (3 * L^2 + L + 1)

/-- The same source bound controls reduced ellipticity, the clock density, and the
sum of the Euclidean Lipschitz constants of the reduced coefficient and clock. -/
theorem sourceReducedBound_support {d : ℕ} {L : ℝ} {ω : FieldPair d}
    (hL : 1 ≤ L) (hω : IsRegular L ω) :
    1 ≤ sourceReducedBound L ∧
    IsElliptic (sourceReducedBound L) (reducedCoefficient ω) ∧
    (∀ x, (sourceReducedBound L)⁻¹ ≤ clockDensity ω x ∧
      clockDensity ω x ≤ sourceReducedBound L) ∧
    IsOperatorLipschitz (Real.exp (2 * L) * (L + 2 * L^2)) (reducedCoefficient ω) ∧
    (∀ x y, |clockDensity ω x - clockDensity ω y| ≤
      (Real.exp (2 * L) * (2 * L)) * euclideanNorm (x - y)) ∧
    Real.exp (2 * L) * (L + 2 * L^2) + Real.exp (2 * L) * (2 * L) ≤
      sourceReducedBound L := by
  let K := sourceReducedBound L
  have hpoly : L ≤ 3 * L^2 + L + 1 := by
    nlinarith [sq_nonneg L]
  have hKone : 1 ≤ K := by
    have he : 1 ≤ Real.exp (2 * L) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hp : 1 ≤ 3 * L^2 + L + 1 := by
      nlinarith [sq_nonneg L, hL]
    dsimp [K, sourceReducedBound]
    calc
      1 = 1 * 1 := by ring
      _ ≤ Real.exp (2 * L) * (3 * L^2 + L + 1) :=
        mul_le_mul he hp (by norm_num) (Real.exp_pos _).le
  have hKpos : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg L, hL]
  have hKL : Real.exp (2 * L) * L ≤ K := by
    dsimp [K, sourceReducedBound]
    exact mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
  have hKexp : Real.exp (2 * L) ≤ K := by
    calc
      Real.exp (2 * L) = Real.exp (2 * L) * 1 := by ring
      _ ≤ Real.exp (2 * L) * (3 * L^2 + L + 1) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg L, hL])
          (Real.exp_pos _).le
      _ = K := by rfl
  have hKinv : K⁻¹ ≤ Real.exp (-2 * L) * L⁻¹ := by
    calc
      K⁻¹ ≤ (Real.exp (2 * L) * L)⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div hKpos (mul_pos (Real.exp_pos _) (by linarith))).2 hKL
      _ = Real.exp (-2 * L) * L⁻¹ := by
        rw [mul_inv, ← Real.exp_neg, neg_mul]
  have hsum :
      Real.exp (2 * L) * (L + 2 * L^2) + Real.exp (2 * L) * (2 * L) ≤ K := by
    have hgap : 2 * L^2 + 3 * L ≤ 3 * L^2 + L + 1 := by
      nlinarith [sq_nonneg (L - 1)]
    calc
      _ = Real.exp (2 * L) * (2 * L^2 + 3 * L) := by ring
      _ ≤ Real.exp (2 * L) * (3 * L^2 + L + 1) :=
        mul_le_mul_of_nonneg_left hgap (Real.exp_pos _).le
      _ = K := by rfl
  refine ⟨hKone, ?_, ?_, ?_, ?_, hsum⟩
  · intro x
    constructor
    · exact reducedCoefficient_transpose ω x (hω.1 x).1
    · intro ξ
      have hsq : 0 ≤ euclideanSq ξ := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (ξ i))
      have hb := reducedCoefficient_energy_bounds ω x ξ L hL hω
      constructor
      · calc
          K⁻¹ * euclideanSq ξ ≤
              (Real.exp (-2 * L) * L⁻¹) * euclideanSq ξ :=
            mul_le_mul_of_nonneg_right hKinv hsq
          _ ≤ dot ξ ((reducedCoefficient ω x).mulVec ξ) := hb.1
      · calc
          dot ξ ((reducedCoefficient ω x).mulVec ξ) ≤
              (Real.exp (2 * L) * L) * euclideanSq ξ := hb.2
          _ ≤ K * euclideanSq ξ := mul_le_mul_of_nonneg_right hKL hsq
  · intro x
    have hc := clockDensity_bounds ω x L (hω.2.1 x)
    constructor
    · calc
        K⁻¹ ≤ Real.exp (-2 * L) * L⁻¹ := hKinv
        _ ≤ Real.exp (-2 * L) := by
          calc
            Real.exp (-2 * L) * L⁻¹ ≤ Real.exp (-2 * L) * 1 :=
              mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hL)
                (Real.exp_pos (-2 * L)).le
            _ = Real.exp (-2 * L) := by ring
        _ ≤ clockDensity ω x := hc.1
    · exact hc.2.trans hKexp
  · exact Correctors.reducedCoefficient_operatorLipschitz hL hω
  · intro x y
    calc
      |clockDensity ω x - clockDensity ω y| ≤
          (2 * Real.exp (2 * L) * L) * euclideanNorm (x - y) :=
        Correctors.clockDensity_lipschitz_bound hω x y
      _ = (Real.exp (2 * L) * (2 * L)) * euclideanNorm (x - y) := by ring

end EinsteinRelation
