import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.ReducedClockRate

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:integration#uniform-profile-bounds`, `paper/main.tex:1218–1244`.
The literal contractions use the full homogenized matrix. Common positive
bounds precede the law, actual covariance and coordinate/clock index. -/
def node_p_u3A_integration_u23_uniform_u2D_profile_u2D_boundsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsJointObservation Q Z → IsJointCovariance Q Z covariance →
      let first : Fin d := ⟨0, by omega⟩
      let A := homogenizedCoefficient Q
      let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
      let γ : ℝ := A first first / 2
      let u₀ : Option (Fin d) → ℝ := fun κ => match κ with
        | none => 0
        | some i => p₀ / 4 * ∑ j, ∑ k,
            (A⁻¹) j k * covariance (.inl (j, first)) (.inl (k, i))
      let u₂ : Option (Fin d) → ℝ := fun κ => match κ with
        | none => p₀ / 2 * covariance (.inl (first, first)) (.inr ())
        | some i => p₀ / 4 * covariance (.inl (first, first)) (.inl (first, i))
      c ≤ γ ∧ γ ≤ C ∧ ∀ κ : Option (Fin d),
        |u₀ κ| + |u₂ κ| ≤ C ∧ ∀ z : ℂ,
          (match κ with
            | none => clockGaussianProfile hd Q covariance z
            | some i => velocityGaussianProfile hd Q covariance i z) =
          complexGaussianProfile (u₀ κ) (u₂ κ) γ z

end EinsteinFull.Blueprint
