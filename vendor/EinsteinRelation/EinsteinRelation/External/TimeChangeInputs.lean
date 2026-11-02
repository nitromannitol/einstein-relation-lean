import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Diffusion.Basic

/-! # Cited time-change and ergodic inputs for the reduced diffusion

Two named propositions on the carriers of `EinsteinRelation.Diffusion.Basic`. The first
relates the physical and reduced diffusion families by the pathwise time change of the
clock identity (main.tex 215-218), using the clock `physicalPathClock` and the inverse time
change `inverseClockPath` of the existing clock development. The second gives the long-time
clock rate of the unforced reduced diffusion (main.tex 233). Each is a bare statement whose
hypotheses are recorded in its docstring. These are externally cited inputs and are not
proved in this development.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinRelation.External

/-- Time change between the physical and reduced diffusion families (main.tex 215-218 and
228-233). For a reduced path `Y`, the clock is `A(t) = ∫₀ᵗ μ(Y_u) du` with `μ = clockDensity ω`,
and the inverse time change `inverseClockPath ω Y` is the physical path `X` satisfying
`X(A(t)) = Y(t)`, the pathwise relation of main.tex 218. The statement says that, for every
force `lam ≥ 0` and `Q`-a.e. environment `ω`, the physical quenched law from the origin is the
image of the reduced quenched law from the origin under this inverse time change. The
direction is that of the existing inverse clock, which takes the reduced path as input.

Hypotheses, as they apply to the carriers:
* `2 ≤ d`; the force direction is the coordinate `e₁ = ⟨0, _⟩`.
* `Q : EnvironmentLaw d Λ₀ r₀`: a probability law with `1 ≤ Λ₀`, `1 ≤ r₀`, stationarity,
  finite range, and `IsRegular Λ₀ ω` for `Q`-a.e. `ω` (so `|V| ≤ Λ₀`, `V` and `a₀` are
  Lipschitz, and `a₀` is uniformly elliptic). Under these, `μ` is continuous with
  `exp(-2Λ₀) ≤ μ ≤ exp(2Λ₀)`, the bounds the inverse clock needs (main.tex 199-208).
* `P : DiffusionFamily d` is a physical family (`IsPhysicalDiffusionFamily`): for every
  `lam ≥ 0` and `Q`-a.e. `ω`, `P lam (0, ω)` solves the martingale problem of the physical
  generator `½ e^{2V} ∇·(e^{-2V} a₀ ∇) + λ a₀ e₁·∇` (main.tex 59-65).
* `P' : DiffusionFamily d` is a reduced family (`IsReducedDiffusionFamily`): for every
  `lam ≥ 0` and `Q`-a.e. `ω`, `P' lam (0, ω)` solves the martingale problem of the reduced
  generator `μ L_X^λ` (main.tex 210-212).
* `hω : IsRegular Λ₀ ω` is the regularity witness required by the inverse clock. It is
  quantified inside the a.e. statement because the inverse clock is defined only for
  regular fields.

Used at main.tex 218-233, 957 and 1185.

Source: standard, not cited: SOURCE_GAP. The paper cites nothing for this identity. The
standard time-change theorem for martingale problems is Ethier and Kurtz (1986), *Markov
Processes: Characterization and Convergence*, Theorem 6.1.3. Passing from the solution
property to equality of the laws also uses uniqueness of the physical martingale problem
(Stroock and Varadhan 1979, Theorem 7.2.1), which is the input `PhysicalFamilyUniqueness`
in `EinsteinRelation.External.DiffusionLiterature`. -/
def TimeChangeLaw : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P P' : DiffusionFamily d),
    IsPhysicalDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P →
    IsReducedDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P' →
    ∀ lam : ℝ, 0 ≤ lam → ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      P lam (0, ω) = Measure.map
        (fun γ : Path d => EinsteinRelation.Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
        (P' lam (0, ω))

/-- Long-time clock rate of the unforced reduced diffusion (main.tex 233: `A⁰(t)/t → E_Q μ`
for the unforced reduced family, from the stationarity and ergodicity of the unforced
environment process, main.tex 257). The clock of a path `γ` is
`A⁰(t) = physicalPathClock ω γ t`, the integral of `μ = clockDensity ω` along `γ`. The limit
is `E_Q μ = ∫ clockDensity ω' 0 dQ(ω')`, since a stationary field is identified with its value
at the origin (main.tex 241).

Hypotheses, as they apply to the carriers:
* `2 ≤ d`; the force direction is the coordinate `e₁ = ⟨0, _⟩`.
* `Q : EnvironmentLaw d Λ₀ r₀`, as in `TimeChangeLaw`: a probability law with `1 ≤ Λ₀`,
  `1 ≤ r₀`, `IsRegular Λ₀ ω` for `Q`-a.e. `ω`, stationarity under translations, and finite
  range.
* `P' : DiffusionFamily d` is a reduced family (`IsReducedDiffusionFamily`). Only its
  force-zero member is used: for `Q`-a.e. `ω`, `P' 0 (0, ω)` is the quenched law of the
  unforced reduced diffusion from the origin.

Conclusion: for `Q`-a.e. `ω` and `P' 0 (0, ω)`-a.e. path `γ`, the rate `t⁻¹ A⁰(t)` tends to
`E_Q μ` as `t → ∞`.

Used at main.tex 233 and in the time-change identity for `η(λ)` and `Σ_X` (main.tex 228-233).

Source: standard, not cited: SOURCE_GAP. The paper cites nothing for this limit. It follows
from the Birkhoff ergodic theorem for the stationary, ergodic unforced environment process
`T_{Y⁰(t)} ω` (main.tex 257), whose observable at the origin is `μ`. -/
def EnvironmentProcessErgodic : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
    IsReducedDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P' →
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' 0 (0, ω)),
      Tendsto (fun t : ℝ≥0 => (EinsteinRelation.Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ))
        atTop (𝓝 (∫ ω', clockDensity ω' (0 : Vec d) ∂Q.measure))

end EinsteinRelation.External
