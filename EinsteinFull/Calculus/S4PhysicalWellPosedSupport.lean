import EinsteinFull.Calculus.S4GeneratorRegularitySupport

/-!
# Well-posedness of the physical martingale problem for smooth regular environments

`physicalGenerator = (clockDensity)⁻¹ • reducedGenerator` is the textbook operator with diffusion
matrix `ω.1` (the physical coefficient) and drift `(clockDensity)⁻¹ • forcedDrift`.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace EinsteinFull
open EinsteinRelation

theorem svGenerator_smul {d : ℕ} (A : Vec d → Mat d) (b : Vec d → Vec d) (c : Vec d → ℝ)
    (f : Vec d → ℝ) (x : Vec d) :
    External.Draft.svGenerator (fun y => c y • A y) (fun y j => c y * b y j) f x =
      c x * External.Draft.svGenerator A b f x := by
  unfold External.Draft.svGenerator
  simp only [Matrix.smul_apply, smul_eq_mul]
  have h1 : ∑ i, ∑ j, c x * A x i j *
        fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) =
      c x * ∑ i, ∑ j, A x i j *
        fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, c x * b x i * fderiv ℝ f x (unitVector i) =
      c x * ∑ i, b x i * fderiv ℝ f x (unitVector i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  ring

/-- The drift of the physical operator in the form `½ Σ a₀ᵢⱼ ∂ᵢ∂ⱼ + Σ bᵢ ∂ᵢ`. -/
noncomputable def physicalDrift {d : ℕ} (ω : FieldPair d) (i : Fin d) (lam : ℝ)
    (y : Vec d) : Vec d :=
  fun j => (clockDensity ω y)⁻¹ * forcedDrift (reducedCoefficient ω) i lam y j

theorem physicalGenerator_eq_svGenerator {d : ℕ} {ω : FieldPair d} (hs : IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec d) :
    physicalGenerator i ω lam f x =
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f x := by
  rw [physicalGenerator_eq_inv_mul, reducedGenerator_eq_svGenerator hs i lam hf x]
  have e1 : (⇑ω.1 : Vec d → Mat d) =
      fun y => (clockDensity ω y)⁻¹ • reducedCoefficient ω y := by
    funext y
    rw [reducedCoefficient, inv_smul_smul₀ (clockDensity_pos ω y).ne']
  rw [e1]
  exact (svGenerator_smul (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)
    (fun y => (clockDensity ω y)⁻¹) f x).symm

theorem abs_clockDensity_inv_le {d : ℕ} {Λ₀ : ℝ} {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (x : Vec d) : |(clockDensity ω x)⁻¹| ≤ Real.exp (2 * Λ₀) := by
  have hinv : (clockDensity ω x)⁻¹ = Real.exp (2 * ω.2 x) := by
    rw [clockDensity, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by have := (abs_le.1 (hω.2.1 x)).2; linarith)

theorem physical_svHypotheses {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) :
    Continuous (⇑ω.1) ∧
    (∀ x, (ω.1 x).transpose = ω.1 x) ∧
    (∃ M : ℝ, ∀ x i j, |ω.1 x i j| ≤ M) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ x ξ, c * euclideanSq ξ ≤ dot ξ ((ω.1 x).mulVec ξ)) ∧
    Measurable (physicalDrift ω i lam) ∧
    (∃ M : ℝ, ∀ x k, |physicalDrift ω i lam x k| ≤ M) := by
  obtain ⟨_, _, _, _, hm, ⟨Mb, hMb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hμ : Continuous (clockDensity ω) := (reduce ω).2.continuous
  have hμi : Continuous fun y => (clockDensity ω y)⁻¹ :=
    hμ.inv₀ fun y => (clockDensity_pos ω y).ne'
  refine ⟨ω.1.continuous, fun x => (hω.1 x).1,
    ⟨Λ₀, fun x i j => abs_apply_le_of_isElliptic hΛ hω.1 x i j⟩,
    ⟨Λ₀⁻¹, inv_pos.2 hΛ, fun x ξ => ((hω.1 x).2 ξ).1⟩, ?_,
    ⟨Real.exp (2 * Λ₀) * Mb, fun x k => ?_⟩⟩
  · refine measurable_pi_iff.2 fun j => ?_
    exact hμi.measurable.mul ((measurable_pi_apply j).comp hm)
  · unfold physicalDrift
    rw [abs_mul]
    exact mul_le_mul (abs_clockDensity_inv_le hω x) (hMb x k) (abs_nonneg _)
      (Real.exp_pos _).le

/-- Existence and uniqueness of the physical martingale problem for a smooth regular
environment, from the draft textbook input. -/
theorem exists_unique_physical_solution {d : ℕ} (hwp : External.Draft.svWellPosedStmt)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ) (x : Vec d) :
    ∃! P : Measure (Path d), SolvesMartingaleProblem (physicalGenerator i ω lam) x P := by
  obtain ⟨hc, hsy, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hω i lam
  have h := hwp d (Fin.pos i) (⇑ω.1) (physicalDrift ω i lam) hc hsy hb he hm hbd x
  refine (existsUnique_congr fun P => ?_).2 h
  refine solvesMartingaleProblem_congr (fun f hf _ => ?_) x P
  funext y
  exact physicalGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hf) y

end EinsteinFull
