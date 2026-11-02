import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Work.W7.ClockFiniteRangeSupport

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:covariance#clock-blocks`, `paper/main.tex:927–932`.
The clock is the literal centered reduced clock, convolved with the actual
anisotropic homogenized Gaussian at time r² (a fixed normalization of Phi_r).
Truncation is unrenormalized at the Euclidean radius r^(1+delta).
All constants and the positive scale-change exponent precede the law.
Squared integrals are accompanied by MemLp, so totalized integrals cannot
stand in for the asserted L2 estimates. The scalar bound b expresses the
supremum bound of the deterministic test on the cube. -/
def node_p_u3A_covariance_u23_clock_u2D_blocksStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (D : StructuralData d)
    (δ η β : ℝ), 0 < δ → 1 / 2 < η → η * (1 + δ) < β → β < 1 →
    ∃ C κ₀ : ℝ, 0 < C ∧ 0 < κ₀ ∧ κ₀ ≤ (1 - β) / 2 ∧
    (∀ p : ℝ, ∃ Cₚ : ℝ, 0 < Cₚ ∧
        ∀ (Q' : EnvironmentLaw d D.ellipticity D.dependenceRange),
          HasSmoothBounds D Q' → ∀ (r : ℝ), 1 ≤ r →
          ∀ᵐ ω ∂reducedLaw Q', ∀ y : Vec d,
            |(∫ z : Vec d,
              anisotropicGaussian (homogenizedCoefficient Q') (r ^ 2) z *
                centeredClockField Q' (y - z) ω) -
              ∫ z in {z : Vec d | euclideanNorm z < r ^ (1 + δ)},
                anisotropicGaussian (homogenizedCoefficient Q') (r ^ 2) z *
                  centeredClockField Q' (y - z) ω| ≤ Cₚ * r ^ (-p)) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
      let K := fun (r : ℝ) (z : Vec d) =>
        anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z
      let Mloc := fun (r : ℝ) (y : Vec d) (ω : FieldPair d) =>
        ∫ z in {z : Vec d | euclideanNorm z < r ^ (1 + δ)},
          K r z * centeredClockField Q (y - z) ω
      let block := fun (r L : ℝ) (x : Vec d) (f : Vec d → ℝ) =>
        fun ω : FieldPair d => L ^ (-(d : ℝ) / 2) *
          ∫ y in clockBlockCube x L, f y * Mloc r y ω
      (∀ (L : ℝ), 1 ≤ L → ∀ (x : Vec d) (f : Vec d → ℝ) (b : ℝ),
        Measurable f → 0 ≤ b → (∀ y ∈ clockBlockCube x L, |f y| ≤ b) →
        (∀ (r : ℝ), L ^ η ≤ r → r ≤ L →
          MemLp (block r L x f) 2 (reducedLaw Q) ∧
          (∫ ω, (block r L x f ω) ^ 2 ∂reducedLaw Q) ≤ (C * b) ^ 2) ∧
        ((∀ y ∈ clockBlockCube x (L - L ^ β), f y = 0) →
          MemLp (block (L ^ η) L x f) 2 (reducedLaw Q) ∧
          (∫ ω, (block (L ^ η) L x f ω) ^ 2 ∂reducedLaw Q) ≤
            (C * L ^ (-(1 - β) / 2) * b) ^ 2)) ∧
      (∀ (L : ℝ), 1 ≤ L → ∀ (x : Vec d) (r : ℝ),
        L ^ η ≤ r → r ≤ L ^ β →
        MemLp (fun ω => block r L x (fun _ => 1) ω -
          block (L ^ η) L x (fun _ => 1) ω) 2 (reducedLaw Q) ∧
        (∫ ω, (block r L x (fun _ => 1) ω -
          block (L ^ η) L x (fun _ => 1) ω) ^ 2 ∂reducedLaw Q) ≤
            (C * L ^ (-κ₀)) ^ 2) ∧
      (∀ (L : ℝ), 1 ≤ L → ∀ (x : Vec d) (r : ℝ), 1 ≤ r → r ≤ L →
        let mask := (clockBlockCube x L).indicator (fun _ => (1 : ℝ))
        let error := fun y : Vec d => (∫ z : Vec d, K r z * mask (y + z)) - mask y
        MemLp error 2 (volume : Measure (Vec d)) ∧
        (∫ y : Vec d, error y ^ 2) ≤ C ^ 2 * L ^ (d - 1) * r) ∧
      (∀ (L : ℝ), 1 ≤ L → ∀ (x : Vec d) (f : Vec d → ℝ) (b : ℝ),
        Measurable f → 0 ≤ b → (∀ y ∈ clockBlockCube x L, |f y| ≤ b) →
        ∀ (r : ℝ), 1 ≤ r →
        let smooth := fun y : Vec d => ∫ z : Vec d,
          K r z * (clockBlockCube x L).indicator f (y + z)
        MemLp smooth 2 (volume : Measure (Vec d)) ∧
        (∫ y : Vec d, smooth y ^ 2) ≤ ∫ y in clockBlockCube x L, (f y) ^ 2)

end EinsteinFull.Blueprint
