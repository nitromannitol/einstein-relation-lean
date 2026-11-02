import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Graph node `p:covariance#test-replacement`, `paper/main.tex:957–964`.
DRAFT. Complex tests use bilinear pairing. The isotropic source kernel is used
literally in smoothing, rather than identified with the homogenized kernel.
Theta, the constant and the large-scale threshold precede the law.
The two errors are stated separately, with actual L² membership. -/
def node_p_u3A_covariance_u23_test_u2D_replacementStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β),
    ∀ N : ℕ, 2 * d + 10 < N →
    ∃ θ C R₀ : ℝ, 0 < θ ∧ θ < 1 ∧
      (d : ℝ) / 2 < θ * η * γ ∧ 1 / 2 < θ * η ∧ 0 < C ∧ 2 ≤ R₀ ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q),
        IsJointObservation Q Z → ∀ (R : ℝ) (hR : 2 ≤ R), R₀ ≤ R →
        ∀ (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))),
      let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
      let r := L ^ η
      let smooth := covarianceSmoothedPairing Q Z R r F
      let localized := covarianceLocalizedPairing d hd D s δ γ η β h Q R r F
      2 * D.dependenceRange ≤ r ∧
      MemLp smooth 2 (reducedLaw Q) ∧ MemLp localized 2 (reducedLaw Q) ∧
      covarianceComplexL2Size (reducedLaw Q)
        (fun ω => scaledJointPairing Q R (by linarith) Z F ω - smooth ω) ≤
          C * schwartzTestNorm N F * (r / R) ^ 2 ∧
      covarianceComplexL2Size (reducedLaw Q) (fun ω => smooth ω - localized ω) ≤
        C * schwartzTestNorm N F * R ^ ((d : ℝ) / 2) *
          (r ^ (-(d : ℝ)) + r ^ (-γ))

end EinsteinFull.Blueprint
