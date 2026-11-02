import EinsteinRelation.Clock.PhysicalClock
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Environment.Reduction

/-! # Internal step statements for the rate bound in Theorem 1.2

Source: `paper/main.tex`, Theorem 1.2 (`t.main`, lines 93-99) and its proof (lines 1187-1196).
The three propositions below are the internal estimates consumed by that proof, stated for the
GMP Section 7 families of `EinsteinRelation.Diffusion.GMPFamily`:

* `VelocityRateStep`: the reduced velocity rate (`eq.reduced-velocity-rate`, line 1149);
* `ClockEstimateStep`: the clock estimate (`eq.clock-estimate`, line 1178);
* `CovarianceIdentityStep`: the covariance identity of the time change
  (`eq.time-change-identities`, line 229).

The first homogenized column `ā e₁`, the homogenized matrix `ā`, and the mean clock `𝔼μ` are
named here. All norms are the Euclidean norm `euclideanNorm`.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinRelation

/-- The first homogenized column `ā e₁ = E[a(e₁ + ∇χ₁)]`, the expected flux of the first
corrector under the reduced law (`paper/main.tex` 698). The direction `e₁` is the index
`⟨0, _⟩ : Fin d`, which exists since `2 ≤ d`. -/
noncomputable def abarE1 {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) :
    Vec d :=
  WithLp.ofLp (Correctors.expectedCorrectorFlux Q (⟨0, by omega⟩ : Fin d))

/-- The homogenized matrix `ā`, whose `i`-th column is the expected corrector flux
`E[a(e_i + ∇χ_i)]` (`paper/main.tex` 698). -/
noncomputable def abar {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) : Mat d :=
  Matrix.of fun (j i : Fin d) => WithLp.ofLp (Correctors.expectedCorrectorFlux Q i) j

/-- The mean clock density `𝔼μ = ∫ exp(-2V(0)) dℚ` under the environment law, where
`μ = clockDensity` is the reduced clock density (`paper/main.tex` 1178). -/
noncomputable def meanMu {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) : ℝ :=
  ∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure

/-- Step 1, the reduced velocity rate (`paper/main.tex` 1149). There are constants `C` and
`0 < lamStar ≤ 1`, depending only on `d`, `Λ₀` and `r₀`, such that every quenched velocity `v` of
the reduced family at force `0 < lam ≤ lamStar` satisfies `|lam⁻¹ v - ā e₁| ≤ C lam`. -/
def VelocityRateStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
      IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
      ∀ lam : ℝ, 0 < lam → lam ≤ lamStar → ∀ v : Vec d,
        HasQuenchedVelocity Q.measure (originLaw (P' lam)) v →
          euclideanNorm (lam⁻¹ • v - abarE1 hd Q) ≤ C * lam

/-- Step 2, the clock estimate (`paper/main.tex` 1178). With the same quantifier prefix as
`VelocityRateStep`, every limit `eta` of the clock rate `t⁻¹ physicalPathClock` along almost every
path of the reduced family at force `lam` satisfies `|eta - 𝔼μ| ≤ C lam`. -/
def ClockEstimateStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
      IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
      ∀ lam : ℝ, 0 < lam → lam ≤ lamStar → ∀ eta : ℝ,
        (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
          Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 eta)) →
        |eta - meanMu Q| ≤ C * lam

/-- Step 3, the covariance identity of the time change (`paper/main.tex` 229-232). For the
physical family, every diffusivity `cov` of the origin law at zero force equals `(𝔼μ)⁻¹ ā`. -/
def CovarianceIdentityStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ cov : Mat d, HasDiffusivity Q.measure (originLaw (P 0)) cov →
      cov = (meanMu Q)⁻¹ • abar Q

end EinsteinRelation
