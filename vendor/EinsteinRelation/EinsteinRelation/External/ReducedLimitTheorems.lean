import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Carriers.RegenerationCorrectorTwins

/-! # Cited limit theorems for the reduced diffusion

Three named propositions for the reduced generator `ℒ^λ = ½ ∇·a∇ + λ a e₁·∇` of
main.tex 209-233, where `a = e^{-2V} a₀` and the clock density is `μ = e^{-2V}`. Each is a bare
statement of an externally cited input, quantified over every environment law and every family
solving the reduced martingale problem. The hypotheses are those of the cited literature statement
as they apply to the carriers: the dimension bound `2 ≤ d`, the environment law
`EnvironmentLaw d Λ₀ r₀`, and the martingale problem. None of them is proved in this development.
-/

open MeasureTheory

namespace EinsteinRelation.External

/-- Law of large numbers with positive force component for the reduced diffusion
(main.tex 220-227 and 230).

Used at main.tex 220-227: the velocity `ℓ(λ)` of `Y^λ` exists, and the clock rate
`η(λ) = e₁·ℓ(λ) / e₁·ℓ_X(λ)` is a quotient whose denominator must be positive. Used again at
main.tex 230 for `ℓ_X(λ) = η(λ)⁻¹ ℓ(λ)`.

Cited: Gantert, Mathieu and Piatnitski (2012, Comm. Pure Appl. Math. 65), Section 5, in the
force-dependent form of the regeneration law of large numbers of Shen (2003, 2004), as cited at
main.tex 220 and 91. Their Section 2.3 states the same almost-sure limit and `λ̂·ℓ(λ) > 0`
(with `λ̂ = λ e₁`) for their drifted model; the reduced generator is that model with potential
zero and coefficient `a`.

Hypotheses, for every instance:
* `2 ≤ d`;
* `Q : EnvironmentLaw d Λ₀ r₀`: a probability law with `1 ≤ Λ₀`, `1 ≤ r₀`, invariant under all
  translations, with joint finite range `r₀`, and almost surely with `a₀` symmetric and
  `Λ₀`-elliptic, `|V| ≤ Λ₀`, and `(a₀, V)` `Λ₀`-Lipschitz. The reduced coefficient
  `a = reducedCoefficient ω` then satisfies the reduced bounds of main.tex 205-207 with a constant
  depending only on `Λ₀`;
* `P : DiffusionFamily d` with `IsReducedDiffusionFamily e₁ Q P`, where `e₁` is the coordinate
  `⟨0, _⟩`: for every `λ ≥ 0`, `P λ (0, ω)` solves the martingale problem of
  `reducedGenerator e₁ ω λ` for `Q`-almost every `ω`;
* `0 < lam`, the force magnitude.

Conclusion: some velocity `v` satisfies `HasQuenchedVelocity` for the origin law `P lam`, that is,
for `Q`-almost every environment, `P`-almost surely `t⁻¹ γ(t) → v` as `t → ∞`, and `0 < e₁·v`.

Hypothesis gaps, recorded and not resolved here:
* GMP's standing model assumes smooth `V` and `σ` (their Assumption 2). Their introduction says
  Section 7 relaxes this to bounded measurable environments; the paper's Lipschitz class is not
  literally GMP's, and the paper cites Section 5 only.
* GMP's standing convention is `λ ≤ 1`; the paper states the law for every `λ > 0`.
* GMP's Assumption 1 (ergodicity) is not a field of `EnvironmentLaw`. It follows from stationarity
  and finite range, which give mixing; this is not formalized here.
* The statement quantifies over every solution family. It equals the cited law for the unique
  solution under `ReducedFamilyUniqueness` (`ReducedDiffusionLiterature`), which is cited
  separately.
-/
def ReducedVelocityExistence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsReducedDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P →
    ∀ lam : ℝ, 0 < lam → ∃ v : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P lam)) v ∧
        0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) v

/-- Positive first velocity component of the physical diffusion (main.tex 220-225).

Used at main.tex 220 ("both velocities have a strictly positive first component") and at
main.tex 222-225, where the denominator `e₁·ℓ_X(λ)` of the clock-rate limit must be nonzero.

Cited: Gantert, Mathieu and Piatnitski (2012), Section 5, as cited at main.tex 220. Their
Section 2.3 states `λ̂·ℓ(λ) > 0` (with `λ̂ = λ e₁`) for the physical drifted model.

Hypotheses, for every instance: `2 ≤ d`; `Q : EnvironmentLaw d Λ₀ r₀` as in
`ReducedVelocityExistence`; `P : DiffusionFamily d` with `IsPhysicalDiffusionFamily e₁ Q P`,
whose generator is `½ e^{2V} ∇·(e^{-2V} a ∇ f) + λ a e₁·∇ f` (main.tex 58-66); `0 < lam`.
The conclusion quantifies over every quenched velocity at force `lam`; the cited law identifies
these with `ℓ_X(λ)`. The hypothesis gaps listed for `ReducedVelocityExistence` apply here too.
-/
def PhysicalVelocityPositive : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsPhysicalDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P →
    ∀ lam : ℝ, 0 < lam → ∀ v : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P lam)) v →
        0 < dot (unitVector (⟨0, by omega⟩ : Fin d)) v

/-- Annealed invariance principle for the unforced reduced diffusion, with covariance the
homogenized matrix `ā` of `-∇·a∇` (main.tex 228-233).

Used at main.tex 231-233: `Σ_X = (E μ)⁻¹ ā` follows because the limiting covariance of `Y⁰` is
`ā`, and the time change multiplies it by `(E μ)⁻¹`. The matrix `ā` has columns
`ā e_i = E[a(e_i + ∇φ_i)]` (main.tex 698), which are the production column
`EinsteinRelation.Carriers.homogenizedCoefficientColumn Q i`. Here `a = e^{-2V} a₀` is the reduced
coefficient and `Q` is the environment law.

Annealed law: the law is `Q.measure`, the physical environment law, and not
`reducedEnvironmentLaw Q`. `IsReducedDiffusionFamily` indexes the family by physical fields
`(a₀, V)`. Evaluating `P 0` at reduced fields `reduce ω` would use the coefficient
`e^{-2μ} a` rather than `a`. The reduced law enters only through the expectation that defines
`homogenizedCoefficientColumn`.

Cited: De Masi, Ferrari, Goldstein and Wick (1989, J. Statist. Phys. 55, 787-855), an invariance
principle for reversible Markov processes applied to diffusions in random media. The paper cites
it at main.tex 82-86 for the physical family, and it is used for the reduced generator at main.tex
233. The identification of the covariance with the variational (corrector) formula is not cited at
main.tex 228-233. The paper's corrector characterization at main.tex 693-698 and the standard
corrector theory of AKM2019book supply it. Hypothesis gap: the exact hypothesis list of DFGW was
checked against the abstract only, not line by line.

Hypotheses, for every instance: `2 ≤ d`; `Q : EnvironmentLaw d Λ₀ r₀` as in
`ReducedVelocityExistence`; `P : DiffusionFamily d` with `IsReducedDiffusionFamily e₁ Q P`, which
is used at `λ = 0`.

Conclusion (`HasDiffusivity`): there is a centered Brownian law `W` with covariance `ā` (symmetric,
nonnegative, with Gaussian finite-dimensional characteristic functions of covariance `min(s,t) ā`),
and for every bounded continuous `F` on path space, the annealed integrals of `F(ε ·)` converge to
`∫ F dW` as `ε ↓ 0`.
-/
def ReducedInvarianceAbar : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
    IsReducedDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P →
    HasDiffusivity Q.measure (originLaw (P 0))
      (Matrix.of fun (j i : Fin d) =>
        WithLp.ofLp
          (@EinsteinRelation.Carriers.homogenizedCoefficientColumn d ⟨hd⟩ Λ₀ r₀ Q i) j)

end EinsteinRelation.External
