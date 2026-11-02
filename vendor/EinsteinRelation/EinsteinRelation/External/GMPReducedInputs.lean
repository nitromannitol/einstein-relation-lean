import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Carriers.RegenerationCorrectorTwins

/-! # Cited inputs for the Gantert, Mathieu and Piatnitski Section 7 diffusion families

Five named propositions for the families of `EinsteinRelation.Diffusion.GMPFamily`, whose origin
laws are fixed-environment realizations of the heat-kernel construction of Gantert, Mathieu and
Piatnitski (2012), Section 7. Each proposition restates one input of
`EinsteinRelation.External.ReducedDiffusionLiterature`,
`EinsteinRelation.External.ReducedLimitTheorems` or `EinsteinRelation.External.TimeChangeInputs`
with the GMP families in place of the
martingale-problem families, and with every quantifier over the force `lam` restricted to
`lam ≤ 1`, GMP's standing convention.

The environment hypotheses are those of `EnvironmentLaw` and `IsRegular`, the Lipschitz class of
the paper. GMP's standing Assumption 2 is stated for smooth `V` and `σ`; this class gap is recorded
here and not resolved.

These are externally cited inputs and are not proved in this development.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinRelation.External

/-- Existence of the reduced GMP family. For every environment law `Q` there is a family `P`
that is a reduced GMP Section 7 family for `Q` (`IsGMPReducedFamily`). The reduced process `Y` is
the zero-potential model with coefficient `exp(-2V) a₀` (GMP 2012, Section 7, p. 32; equations
(3.8)-(3.9), p. 10). -/
def GMPReducedFamilyExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    ∃ P : DiffusionFamily d, IsGMPReducedFamily hd Q.ellipticity_parameter Q P

/-- Law of large numbers with positive force component for the reduced GMP family. For every
force `0 < λ ≤ 1`, some velocity `v` is the quenched velocity of the origin law `P λ`, and its
first component is strictly positive. GMP 2012, pp. 5 and 10; the reduced generator is the
zero-potential model of equations (3.8)-(3.9), p. 10. Used at main.tex 220-227 and 230. -/
def GMPReducedVelocityExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∃ v : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P lam)) v ∧
        0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) v

/-- Annealed invariance principle for the unforced reduced GMP family, with covariance the
homogenized matrix `ā` of `-∇·a∇`, where `a = exp(-2V) a₀` (GMP 2012, Section 2.2, p. 4, and
p. 10). The environment law is `Q.measure`, the physical law: `IsGMPReducedFamily` indexes the
family by the physical fields `(a₀, V)`, and the reduced coefficient enters only through
`EinsteinRelation.Carriers.homogenizedCoefficientColumn`. Used at main.tex 231-233.

Conclusion (`HasDiffusivity`): there is a centered Brownian law `W` with covariance `ā`, and for
every bounded continuous `F` on path space, the annealed integrals of `F(ε ·)` converge to `∫ F dW`
as `ε ↓ 0`. -/
def GMPReducedInvarianceAbar : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P →
    HasDiffusivity Q.measure (originLaw (P 0))
      (Matrix.of fun (j i : Fin d) =>
        WithLp.ofLp
          (@EinsteinRelation.Carriers.homogenizedCoefficientColumn d ⟨hd⟩ Λ₀ r₀ Q i) j)

/-- Time change between the GMP physical and reduced families. For every force `0 ≤ λ ≤ 1`,
`Q`-almost every environment `ω`, and every regularity witness `hω`, the physical quenched law from
the origin is the image of the reduced quenched law from the origin under the inverse clock
`inverseClockPath`. The clock is `A(t) = ∫₀ᵗ μ(Y_u) du` with `μ = clockDensity ω`. GMP 2012,
Section 3, p. 10 ('X_0 has the same law as Y((A)^-1)'), and Section 7, p. 32. Used at main.tex
218-233, 957 and 1185. -/
def GMPTimeChangeLaw : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P P' : DiffusionFamily d),
    IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      P lam (0, ω) = Measure.map
        (fun γ : Path d => EinsteinRelation.Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
        (P' lam (0, ω))

/-- Long-time clock rate of the unforced reduced GMP family. The clock of a path `γ` is
`A⁰(t) = physicalPathClock ω γ t`, the integral of `μ = clockDensity ω` along `γ`. For
`Q`-almost every `ω` and `P' 0 (0, ω)`-almost every path `γ`, the rate `t⁻¹ A⁰(t)` tends to
`∫ clockDensity ω' 0 dQ(ω')` as `t → ∞`. The limit is the ergodic average of the clock along the
unforced reduced process: GMP 2012, p. 8, and p. 10 (proof of (3.1)). Used at main.tex 233. -/
def GMPEnvironmentProcessErgodic : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' 0 (0, ω)),
      Tendsto (fun t : ℝ≥0 => (EinsteinRelation.Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ))
        atTop (𝓝 (∫ ω', clockDensity ω' (0 : Vec d) ∂Q.measure))

end EinsteinRelation.External
