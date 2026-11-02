import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `p:covariance#test-blocks`, `paper/main.tex:966–978`.
DRAFT. The trimmed variables in the literal infinite tiling are jointly
independent. Summability and L² membership are explicit; covariance is
bilinear for complex tests and includes every joint coordinate.
The covariance limit is the actual dyadic one used in the rate contract.
Theta may be any structural exponent in the replacement window. -/
def node_p_u3A_covariance_u23_test_u2D_blocksStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∀ (N : ℕ), 2 * d + 10 < N → ∀ θ : ℝ,
      0 < θ → θ < 1 → (d : ℝ) / 2 < θ * η * γ → 1 / 2 < θ * η →
    ∃ C R₀ κ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧ 0 < κ ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ (R : ℝ), R₀ ≤ R →
      let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
      let A := covarianceDyadicLimit d hd D s δ γ η β h Q
      let children := fun j : Fin d → ℤ =>
        covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
          (covarianceTileCenter L j) (fun _ => 1)
      iIndepFun children (reducedLaw Q) ∧
      ∀ F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      let YF := covarianceTestBlocks d hd D s δ γ η β h Q R L F
      let YG := covarianceTestBlocks d hd D s δ γ η β h Q R L G
      (∀ᵐ ω ∂reducedLaw Q, Summable (fun j : Fin d → ℤ =>
        ∑ a, F (R⁻¹ • covarianceTileCenter L j) a * (children j ω a : ℂ))) ∧
      MemLp YF 2 (reducedLaw Q) ∧ MemLp YG 2 (reducedLaw Q) ∧
      covarianceComplexL2Size (reducedLaw Q) YF ≤ C * schwartzTestNorm N F ∧
      covarianceComplexL2Size (reducedLaw Q)
        (fun ω => covarianceLocalizedPairing d hd D s δ γ η β h Q R (L ^ η) F ω -
          YF ω) ≤ C * schwartzTestNorm N F *
            (L / R + L ^ (-(1 - β) / 2)) ∧
      ‖(∫ ω, YF ω * YG ω ∂reducedLaw Q) -
        ∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
          F x a * (A a b : ℂ) * G x b‖ ≤
        C * schwartzTestNorm N F * schwartzTestNorm N G * (L ^ (-κ) + L / R)

end EinsteinFull.Blueprint
