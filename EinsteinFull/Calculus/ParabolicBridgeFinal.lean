import EinsteinFull.Calculus.ParabolicBridgeAssembly4
import EinsteinFull.Calculus.ParabolicBridgeMolFromStmt
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinRelation.Environment.Basic

/-!
# The interior Hölder decay of the mean oscillation, in the original coordinates
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

/-- The explicit Euclidean-norm ball of the statement is the library round ball. -/
theorem euclideanNorm_ball_eq {d : ℕ} (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    {y : Vec d | EinsteinRelation.euclideanNorm (y - x) < ρ} = euclideanBall x ρ := by
  ext y
  change Real.sqrt (EinsteinRelation.euclideanSq (y - x)) < ρ ↔ vecNormSq (y - x) < ρ ^ 2
  rw [Real.sqrt_lt' hρ]
  rfl

theorem avg_cyl_transfer {d : ℕ} (τ K : ℝ) (hK : 0 < K) (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ)
    (F : ℝ × Vec d → ℝ) :
    ⨍ z in Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x ρ, F z =
      ⨍ z in euclideanBall x ρ ×ˢ Ioo (-ρ ^ 2 / K) 0, F (Tm τ K z) := by
  rw [setAverage_Tm τ K hK F (measurableSet_Ioo.prod (isOpen_euclideanBall x ρ).measurableSet),
    Tm_preimage_cyl τ K hK ρ]

theorem holder_interior_core (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ α₀ C : ℝ, 0 < α₀ ∧ α₀ < 1 ∧ 1 ≤ C ∧
    ∀ (ω1 : Vec d → Mat d), (∀ j k, Measurable fun y => ω1 y j k) →
      (∀ y, (ω1 y).transpose = ω1 y ∧
        (∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (ω1 y) ξ)) ∧
        (∀ ξ : Vec d, vecDot ξ (matVecMul (ω1 y) ξ) ≤ Λ * vecNormSq ξ)) →
    ∀ (τ : ℝ) (x : Vec d) (r : ℝ), 0 < r →
    ∀ (v : ℝ × Vec d → ℝ) (g : Fin d → ℝ × Vec d → ℝ), Measurable v → (∀ j, Measurable (g j)) →
      MemLp v 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)) →
      (∀ j, MemLp (g j) 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r))) →
      (∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r → ∀ j : Fin d,
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (0, Pi.single j 1) =
          -∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, g j z * φ z) →
      (∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r →
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (1, 0) =
          (1 / 2) * ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, ∑ j : Fin d,
            (∑ k : Fin d, ω1 z.2 j k * g k z) * fderiv ℝ φ z (0, Pi.single j 1)) →
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      Real.sqrt (⨍ z in Ioo (τ - (θ * r) ^ 2) τ ×ˢ euclideanBall x (θ * r),
          |v z - ⨍ w in Ioo (τ - (θ * r) ^ 2) τ ×ˢ euclideanBall x (θ * r), v w| ^ 2) ≤
        C * θ ^ α₀ * Real.sqrt (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r,
          |v z - ⨍ w in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v w| ^ 2) := by
  have hΛ0 : 0 < Λ := by linarith
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  have hK : 1 ≤ 2 * Λ := by linarith
  obtain ⟨α, C₁, hα0, hα1, hC₁, hdec⟩ := scaled_decay d hd (Λ ^ 2) hΛ2 (2 * Λ) hK
  refine ⟨α / 2, C₁, by positivity, by linarith, hC₁, ?_⟩
  intro ω1 hmeas hell τ x r hr v g hvm hgm hv hg H1 H2 θ hθ hθ2
  have hK0 : 0 < 2 * Λ := by linarith
  have hA : ∀ y, IsEllipticMatrix 1 (Λ ^ 2) (Λ • ω1 y) := fun y =>
    isEllipticMatrix_smul_of_symm_bounds hΛ (hell y).1 (hell y).2.1 (hell y).2.2
  have hAm : ∀ j k, Measurable fun y => (Λ • ω1 y) j k := fun j k => by
    have : (fun y => (Λ • ω1 y) j k) = fun y => Λ * ω1 y j k := by
      funext y
      simp [Matrix.smul_apply]
    rw [this]
    exact (hmeas j k).const_mul Λ
  have hAω : ∀ y j k, (Λ • ω1 y) j k = (2 * Λ / 2) * ω1 y j k := by
    intro y j k
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hMol := molData_of_stmt (τ := τ) (x := x) hr hK0 (fun y => Λ • ω1 y) ω1 hA hAm hAω
    v g hvm hgm hv hg H1 H2
  have hmain := hdec x r hr (fun y => Λ • ω1 y) (fun z => v (Tm τ (2 * Λ) z))
    (fun k z => g k (Tm τ (2 * Λ) z)) hMol
    (⨍ w, (fun z => v (Tm τ (2 * Λ) z)) w ∂(volume.restrict
      (euclideanBall x r ×ˢ Ioo (-r ^ 2 / (2 * Λ)) 0))) θ hθ hθ2
  have hθr0 : 0 < θ * r := mul_pos hθ hr
  have e1 : ∀ ρ : ℝ, 0 < ρ → ⨍ w in Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x ρ, v w =
      ⨍ w, (fun z => v (Tm τ (2 * Λ) z)) w ∂(volume.restrict
        (euclideanBall x ρ ×ˢ Ioo (-ρ ^ 2 / (2 * Λ)) 0)) := fun ρ hρ =>
    avg_cyl_transfer τ (2 * Λ) hK0 x hρ v
  have e2 : ∀ ρ : ℝ, 0 < ρ →
      ⨍ z in Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x ρ,
        |v z - ⨍ w in Ioo (τ - ρ ^ 2) τ ×ˢ euclideanBall x ρ, v w| ^ 2 =
      ⨍ z, |(fun z => v (Tm τ (2 * Λ) z)) z - ⨍ w, (fun z => v (Tm τ (2 * Λ) z)) w ∂(volume.restrict
        (euclideanBall x ρ ×ˢ Ioo (-ρ ^ 2 / (2 * Λ)) 0))| ^ 2 ∂(volume.restrict
        (euclideanBall x ρ ×ˢ Ioo (-ρ ^ 2 / (2 * Λ)) 0)) := by
    intro ρ hρ
    rw [e1 ρ hρ]
    exact avg_cyl_transfer τ (2 * Λ) hK0 x hρ
      (fun z => |v z - ⨍ w, (fun z => v (Tm τ (2 * Λ) z)) w ∂(volume.restrict
        (euclideanBall x ρ ×ˢ Ioo (-ρ ^ 2 / (2 * Λ)) 0))| ^ 2)
  rw [e2 (θ * r) hθr0, e2 r hr]
  refine hmain.trans ?_
  have hθ1 : θ ≤ 1 := by linarith
  have hexp : θ ^ α ≤ θ ^ (α / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by linarith)
  have hC0 : 0 ≤ C₁ := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC0) (Real.sqrt_nonneg _)

end EinsteinFull.ParabolicBridge
