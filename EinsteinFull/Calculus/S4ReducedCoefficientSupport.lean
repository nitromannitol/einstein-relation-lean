import EinsteinFull.Calculus.S4GeneratorBridgeSupport
import EinsteinRelation.Environment.Reduction
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hypotheses of the textbook well-posedness theorem for the reduced coefficient

For a regular environment `ω` (`IsRegular Λ₀ ω`, `0 < Λ₀`) the reduced coefficient
`ã = exp(-2V) a₀` is symmetric, continuous, entrywise bounded, entrywise Lipschitz and
uniformly elliptic in the Euclidean quadratic form; the drift `forcedDrift ã i lam` is Borel
and bounded.  Consequently the clean second-order operator `svGenerator ã (forcedDrift ã i lam)`
satisfies every hypothesis of `External.Draft.svWellPosedStmt`.
-/

open scoped BigOperators NNReal

namespace EinsteinFull
open EinsteinRelation

theorem dot_eq_dotProduct {d : ℕ} (u v : Vec d) : dot u v = u ⬝ᵥ v := rfl

theorem abs_apply_le_euclideanNorm {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  exact (sq (x i)).le.trans h

theorem euclideanNorm_le_sqrt_mul_norm {d : ℕ} (x : Vec d) :
    euclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
  unfold euclideanNorm euclideanSq dot
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  calc ∑ j, x j * x j ≤ ∑ _j : Fin d, ‖x‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := norm_le_pi_norm x j
        rw [Real.norm_eq_abs] at h
        have h2 : |x j| ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        rw [sq_abs] at h2
        calc x j * x j = x j ^ 2 := (sq _).symm
          _ ≤ ‖x‖ ^ 2 := h2
    _ = d * ‖x‖ ^ 2 := by simp

theorem euclideanNorm_unitVector {d : ℕ} (j : Fin d) : euclideanNorm (unitVector j) = 1 := by
  unfold euclideanNorm euclideanSq dot unitVector
  simp [Pi.single_apply]

theorem abs_entry_sub_le {d : ℕ} {L : ℝ} {a : Vec d → Mat d} (h : IsOperatorLipschitz L a)
    (x y : Vec d) (k j : Fin d) :
    |a x k j - a y k j| ≤ L * euclideanNorm (x - y) := by
  have h1 := h x y (unitVector j)
  rw [euclideanNorm_unitVector, mul_one] at h1
  have e : ((a x - a y).mulVec (unitVector j)) k = a x k j - a y k j := by
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  rw [← e]
  exact (abs_apply_le_euclideanNorm _ k).trans h1

theorem abs_exp_sub_exp_le {c s t : ℝ} (hs : s ≤ c) (ht : t ≤ c) :
    |Real.exp s - Real.exp t| ≤ Real.exp c * |s - t| := by
  have h := (convex_Iic c).norm_image_sub_le_of_norm_deriv_le (f := Real.exp)
    (C := Real.exp c) (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 hx) ht hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

theorem quad_unit_add {d : ℕ} (a : Mat d) (k j : Fin d) (s : ℝ) :
    dot (unitVector k + s • unitVector j) (a.mulVec (unitVector k + s • unitVector j)) =
      a k k + s * a k j + s * a j k + s ^ 2 * a j j := by
  rw [dot_eq_dotProduct]
  simp only [unitVector, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, Matrix.mulVec_single_one,
    single_dotProduct, Matrix.col_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  ring

theorem euclideanSq_unit_add {d : ℕ} {k j : Fin d} (hkj : k ≠ j) (s : ℝ) :
    euclideanSq (unitVector k + s • unitVector j) = 1 + s ^ 2 := by
  unfold euclideanSq
  rw [dot_eq_dotProduct]
  simp [unitVector, add_dotProduct, dotProduct_add, Pi.single_apply, hkj, hkj.symm]
  ring

theorem euclideanSq_unitVector {d : ℕ} (k : Fin d) : euclideanSq (unitVector k) = 1 := by
  unfold euclideanSq dot unitVector
  simp [Pi.single_apply]

theorem dot_unitVector_mulVec {d : ℕ} (a : Mat d) (k : Fin d) :
    dot (unitVector k) (a.mulVec (unitVector k)) = a k k := by
  simp [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]

/-- Entries of a symmetric elliptic matrix field are bounded by the ellipticity constant. -/
theorem abs_apply_le_of_isElliptic {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {a : Vec d → Mat d}
    (h : IsElliptic Λ a) (x : Vec d) (k j : Fin d) : |a x k j| ≤ Λ := by
  obtain ⟨hsym, hq⟩ := h x
  have hΛi : 0 < Λ⁻¹ := inv_pos.2 hΛ
  have hΛ1 : Λ⁻¹ ≤ Λ ∨ Λ ≤ Λ⁻¹ := le_total _ _
  have hdiag : ∀ l : Fin d, Λ⁻¹ ≤ a x l l ∧ a x l l ≤ Λ := by
    intro l
    have := hq (unitVector l)
    rw [euclideanSq_unitVector, dot_unitVector_mulVec] at this
    constructor <;> linarith [this.1, this.2]
  by_cases hkj : k = j
  · subst hkj
    obtain ⟨h1, h2⟩ := hdiag k
    rw [abs_of_pos (lt_of_lt_of_le hΛi h1)]
    exact h2
  · have hs : a x j k = a x k j := by
      have := congrFun (congrFun hsym k) j
      rwa [Matrix.transpose_apply] at this
    have hp := hq (unitVector k + (1 : ℝ) • unitVector j)
    have hm := hq (unitVector k + (-1 : ℝ) • unitVector j)
    rw [euclideanSq_unit_add hkj, quad_unit_add] at hp hm
    obtain ⟨hk1, hk2⟩ := hdiag k
    obtain ⟨hj1, hj2⟩ := hdiag j
    rw [hs] at hp hm
    rw [abs_le]
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2]

theorem reducedCoefficient_apply {d : ℕ} (ω : FieldPair d) (y : Vec d) (k j : Fin d) :
    reducedCoefficient ω y k j = Real.exp (-2 * ω.2 y) * ω.1 y k j := by
  simp [reducedCoefficient, clockDensity]

theorem reducedCoefficient_symm {d : ℕ} {Λ₀ : ℝ} {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (y : Vec d) : (reducedCoefficient ω y).transpose = reducedCoefficient ω y := by
  rw [reducedCoefficient, Matrix.transpose_smul, (hω.1 y).1]

theorem continuous_reducedCoefficient {d : ℕ} (ω : FieldPair d) :
    Continuous (reducedCoefficient ω) :=
  (reduce ω).1.continuous

theorem abs_reducedCoefficient_le {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (y : Vec d) (k j : Fin d) :
    |reducedCoefficient ω y k j| ≤ Real.exp (2 * Λ₀) * Λ₀ := by
  rw [reducedCoefficient_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul ?_ (abs_apply_le_of_isElliptic hΛ hω.1 y k j) (abs_nonneg _)
    (Real.exp_pos _).le
  refine Real.exp_le_exp.2 ?_
  have := (abs_le.1 (hω.2.1 y)).1
  linarith

theorem reducedCoefficient_lipschitz {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (k j : Fin d) :
    LipschitzWith (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d))
      (fun z => reducedCoefficient ω z k j) := by
  have hK : 0 ≤ Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d := by positivity
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [Real.coe_toNNReal _ hK, Real.dist_eq, dist_eq_norm]
  simp only [reducedCoefficient_apply]
  set e1 := Real.exp (-2 * ω.2 y) with he1
  set e2 := Real.exp (-2 * ω.2 z) with he2
  set euc := euclideanNorm (y - z) with heuc
  have hVy := abs_le.1 (hω.2.1 y)
  have hVz := abs_le.1 (hω.2.1 z)
  have hexp : |e1 - e2| ≤ Real.exp (2 * Λ₀) * (2 * (Λ₀ * euc)) := by
    have h := abs_exp_sub_exp_le (c := 2 * Λ₀) (s := -2 * ω.2 y) (t := -2 * ω.2 z)
      (by linarith) (by linarith)
    have h2 : |(-2 * ω.2 y) - (-2 * ω.2 z)| ≤ 2 * (Λ₀ * euc) := by
      have : (-2 * ω.2 y) - (-2 * ω.2 z) = -2 * (ω.2 y - ω.2 z) := by ring
      rw [this, abs_mul]
      have h3 := hω.2.2.2 y z
      have : |(-2 : ℝ)| = 2 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    exact h.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  have he2le : |e2| ≤ Real.exp (2 * Λ₀) := by
    rw [he2, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith)
  have hay := abs_apply_le_of_isElliptic hΛ hω.1 y k j
  have hdiff : |ω.1 y k j - ω.1 z k j| ≤ Λ₀ * euc := abs_entry_sub_le hω.2.2.1 y z k j
  have heuc0 : 0 ≤ euc := Real.sqrt_nonneg _
  have heuc1 : euc ≤ Real.sqrt d * ‖y - z‖ := euclideanNorm_le_sqrt_mul_norm _
  have hsplit : e1 * ω.1 y k j - e2 * ω.1 z k j =
      (e1 - e2) * ω.1 y k j + e2 * (ω.1 y k j - ω.1 z k j) := by ring
  rw [hsplit]
  calc |(e1 - e2) * ω.1 y k j + e2 * (ω.1 y k j - ω.1 z k j)|
      ≤ |(e1 - e2) * ω.1 y k j| + |e2 * (ω.1 y k j - ω.1 z k j)| := abs_add_le _ _
    _ = |e1 - e2| * |ω.1 y k j| + |e2| * |ω.1 y k j - ω.1 z k j| := by
        rw [abs_mul, abs_mul]
    _ ≤ Real.exp (2 * Λ₀) * (2 * (Λ₀ * euc)) * Λ₀ + Real.exp (2 * Λ₀) * (Λ₀ * euc) := by
        refine add_le_add (mul_le_mul hexp hay (abs_nonneg _) (by positivity))
          (mul_le_mul he2le hdiff (abs_nonneg _) (Real.exp_pos _).le)
    _ = Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * euc := by ring
    _ ≤ Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * (Real.sqrt d * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left heuc1 (by positivity)
    _ = Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d * ‖y - z‖ := by ring

theorem dot_smul_mulVec {d : ℕ} (c : ℝ) (M : Mat d) (ξ : Vec d) :
    dot ξ ((c • M).mulVec ξ) = c * dot ξ (M.mulVec ξ) := by
  rw [Matrix.smul_mulVec]
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem reducedCoefficient_elliptic {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ (y ξ : Vec d),
      c * euclideanSq ξ ≤ dot ξ ((reducedCoefficient ω y).mulVec ξ) := by
  refine ⟨Real.exp (-(2 * Λ₀)) * Λ₀⁻¹, mul_pos (Real.exp_pos _) (inv_pos.2 hΛ), ?_⟩
  intro y ξ
  rw [reducedCoefficient, clockDensity, dot_smul_mulVec]
  have h1 : Real.exp (-(2 * Λ₀)) ≤ Real.exp (-2 * ω.2 y) := by
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hω.2.1 y)).2
    linarith
  have h2 := ((hω.1 y).2 ξ).1
  have h3 : 0 ≤ euclideanSq ξ := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  calc Real.exp (-(2 * Λ₀)) * Λ₀⁻¹ * euclideanSq ξ
      = Real.exp (-(2 * Λ₀)) * (Λ₀⁻¹ * euclideanSq ξ) := by ring
    _ ≤ Real.exp (-2 * ω.2 y) * dot ξ ((ω.1 y).mulVec ξ) :=
        mul_le_mul h1 h2 (mul_nonneg (inv_pos.2 hΛ).le h3) (Real.exp_pos _).le

/-- Every hypothesis of `External.Draft.svWellPosedStmt` holds for the reduced coefficient of a
regular environment and the drift `forcedDrift`. -/
theorem reduced_svHypotheses {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) :
    Continuous (reducedCoefficient ω) ∧
    (∀ x, (reducedCoefficient ω x).transpose = reducedCoefficient ω x) ∧
    (∃ M : ℝ, ∀ x i j, |reducedCoefficient ω x i j| ≤ M) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ x ξ, c * euclideanSq ξ ≤
      dot ξ ((reducedCoefficient ω x).mulVec ξ)) ∧
    Measurable (forcedDrift (reducedCoefficient ω) i lam) ∧
    (∃ M : ℝ, ∀ x k, |forcedDrift (reducedCoefficient ω) i lam x k| ≤ M) := by
  refine ⟨continuous_reducedCoefficient ω, reducedCoefficient_symm hω,
    ⟨_, abs_reducedCoefficient_le hΛ hω⟩, reducedCoefficient_elliptic hΛ hω,
    measurable_forcedDrift _ (continuous_reducedCoefficient ω) i lam,
    ⟨_, fun x k => abs_forcedDrift_le (reducedCoefficient ω)
      (reducedCoefficient_lipschitz hΛ hω) (abs_reducedCoefficient_le hΛ hω) i lam x k⟩⟩

/-- Well-posedness of the clean reduced martingale problem for a regular environment, from the
textbook input. -/
theorem exists_unique_clean_reduced_solution {d : ℕ} (hwp : External.Draft.svWellPosedStmt)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    (x : Vec d) :
    ∃! P : MeasureTheory.Measure (Path d), SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam))
      x P := by
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ := reduced_svHypotheses hΛ hω i lam
  exact hwp d (Fin.pos i) (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)
    hc hs hb he hm hbd x

end EinsteinFull
