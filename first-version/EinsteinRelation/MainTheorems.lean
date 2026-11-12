import EinsteinRelation.Closure.CitedInputsChain
import EinsteinRelation.Closure.EntropyDivergenceV2Twin
import EinsteinRelation.Closure.EntropyFisherV2Twin
import EinsteinRelation.Closure.EntropyResolventV2Twin
import EinsteinRelation.Correctors.CorrectorMomentsFromLiterature
import EinsteinRelation.Correctors.DeGiorgiGTBallPoincare
import EinsteinRelation.Correctors.DeGiorgiGTLocalBoundedness
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.Velocity
import EinsteinRelation.Environment.Smooth
import EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinRelation.External.AKMHeatKernel
import EinsteinRelation.External.AKMKernelSemigroup
import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.External.GMPLocalityInput
import EinsteinRelation.External.GMPPhysicalInputs
import EinsteinRelation.External.GMPReducedInputs
import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Frozen.Correctors.HeatSelectedSkewCorrectorColumn
import EinsteinRelation.Frozen.Correctors.HomogenizedCoefficientColumn
import EinsteinRelation.Frozen.Correctors.IsScalarAveragingField
import EinsteinRelation.Frozen.Correctors.NormalizedScalarCorrector
import EinsteinRelation.Frozen.Correctors.ReducedCoefficientObservationSigma
import EinsteinRelation.Frozen.DensityCarriers.IsReducedLaplaceDensity
import EinsteinRelation.Frozen.DensityCarriers.ReducedLaplaceObservedLaw
import EinsteinRelation.Frozen.DensityCarriers.ReducedObservationAt
import EinsteinRelation.Frozen.DensityCarriers.ReducedReferenceLaw
import EinsteinRelation.Frozen.EnvironmentAdmissible
import EinsteinRelation.Frozen.Regeneration.CycleConditionedLaw
import EinsteinRelation.Frozen.ValidAnnealedLawCarriers.AnnealedCoordinateJoint
import EinsteinRelation.Frozen.ValidAnnealedLawCarriers.CoordinatePathLawInput
import EinsteinRelation.Frozen.ValidAnnealedLawCarriers.CoupledPathLawInput
import EinsteinRelation.Mobility.AKMFluxDecaySplit
import EinsteinRelation.Mobility.CorrectorLocalFromConstruction
import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import EinsteinRelation.Regeneration.FirstRewardSteps
import EinsteinRelation.Regeneration.OccupationFromGMPInputs
import EinsteinRelation.Regeneration.RenewalCarriers

/-!
# The numbered results of the paper

This file states every numbered result of the paper *Quantitative Einstein relation for
reversible diffusions in a random environment* (Bou-Rabee and Xu), except Conjecture 1.3,
and proves it.

**Form of each statement.** Each theorem has two groups of arguments.

1. *Literature inputs.* The leading hypotheses `h45`, `h46`, ..., `hW` are Prop-valued
   statements of results from the literature: results that the paper cites, and the Fukushima
   decomposition of Dirichlet-form theory, which the paper uses through Gantert, Mathieu and
   Piatnitski (2012, Section 7). Each is a named
   proposition defined under `EinsteinRelation/External/`, `EinsteinRelation/Mobility/` or
   `EinsteinRelation/Regeneration/`, whose docstring records the citation (theorem or equation
   and page). They are hypotheses of the theorems, not axioms: nothing in this repository
   asserts them. A theorem takes exactly the inputs that its proof uses. The README lists every
   input with its citation.
2. *The statement.* After the inputs comes the statement of the result, copied verbatim from
   the statement fixed in advance for that result (the definitions it uses are under
   `EinsteinRelation/Frozen/` and in the modules those import). The theorems are declared
   inside `namespace EinsteinRelation.Frozen` with the same `open` commands as the fixed
   statements, so that every name in a statement resolves as it does there.

Two inputs cited in the paper are not hypotheses here because they are proved, from the
De Giorgi–Nash–Moser library `DeGiorgi`: the Poincaré inequality on balls (Gilbarg and
Trudinger, (7.45)) by `EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi`, and local
boundedness of weak solutions (Gilbarg and Trudinger, Theorem 8.17) by
`EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi`.

The names of the hypotheses follow the cited results: `h45`, `h46`, `h47` are (4.5), (4.6),
(4.7) of Armstrong, Kuusi and Mourrat (2019); `h68`, `h614`, `h615`, `h616` are their Lemma 6.1
and (6.14), (6.15), (6.16); `h832` and `h836` are Theorem 8.32 and Corollary 8.36 of Gilbarg and
Trudinger; `hdecay`, `hreg`, `hEll`, `hE1`, `hH2` and `hAKM` are AKM Theorem 9.1 (9.7),
Remark 8.8 (8.25), Theorem 3.3, Proposition E.1, (4.126) and (4.3); `hFOT` is the Fukushima
decomposition (Fukushima, Oshima and Takeda, Theorem 5.5.5); the hypotheses `hGir`, `hInv`,
`hRF`, `hE`, `hTail`, `hLoc`, `hRV`, `hTC`, `hPos`, `hErg`, `hIP`, `hPF`, `hVX` are results of
Gantert, Mathieu and Piatnitski (2012); `hW` is the existence of white noise (AKM
Proposition 5.14).
-/

section MobilityRate

open MeasureTheory

namespace EinsteinRelation.Frozen

/-- **Theorem 1.2** (`t.main`): the quantitative Einstein relation.

Let `d ≥ 2` and `Λ₀, r₀ ∈ ℝ`. There are `C` and `λ_* > 0` such that, for every environment law
`Q` satisfying Assumption 1.1 with constants `Λ₀`, `r₀` (`EnvironmentLaw d Λ₀ r₀`), every
family `P` of quenched path laws that is the physical diffusion family of Gantert, Mathieu and
Piatnitski for `Q` (`IsGMPPhysicalFamily`), every matrix `Σ_X` for which the unforced
diffusion from the origin satisfies the annealed invariance principle with covariance `Σ_X`
(`HasDiffusivity`), every `λ ∈ (0, λ_*]` and every vector `ℓ_X(λ)` that is the quenched
almost sure velocity of the diffusion with force `λ` (`HasQuenchedVelocity`),
`|ℓ_X(λ) / λ - Σ_X e₁| ≤ C λ` (`eq.main-rate`). The constants `C` and `λ_*` are chosen
before `Q`, `P`, `Σ_X` and `ℓ_X`.

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.mobility_rate
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel)
    (hH2 : EinsteinRelation.External.AKM.CorrectorWeakH2)
    (hAKM : EinsteinRelation.AKMFluxDecayLargeTime)
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality)
    (hRV : EinsteinRelation.External.GMPReducedVelocityExistence)
    (hTC : EinsteinRelation.External.GMPTimeChangeLaw)
    (hPos : EinsteinRelation.External.GMPPhysicalVelocityPositive)
    (hErg : EinsteinRelation.External.GMPEnvironmentProcessErgodic)
    (hIP : EinsteinRelation.External.GMPReducedInvarianceAbar)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam := by
  exact EinsteinRelation.Closure.mobilityRate_of_cited_inputs
    h45 h46 h47 h68 h614 h615 h616 EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi
    EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi h832 h836 hdecay hreg hEll hE1
    hH2 hFOT hGir hInv hRF hE hTail hLoc hAKM hRV hTC hPos hErg hIP d hd Λ₀ r₀

end EinsteinRelation.Frozen

end MobilityRate

section RegenerationRenewal

open MeasureTheory
open EinsteinRelation.Regeneration EinsteinRelation.Regeneration.Renewal
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers

namespace EinsteinRelation.Frozen

/-- **Lemma 3.1** (`regen.renewal`): the regeneration cycles are identically distributed.

For `d ≥ 2` and constants `Λ₀`, `r₀` there is a scale `l₀ > r₀ / 2` such that, for every
`l ≥ l₀`, success probability `δ ∈ (0, 1)`, force `λ ∈ (0, 1]` and environment law `Q`, and
every coupled realization `(P, K)` of the regeneration construction of Gantert, Mathieu and
Piatnitski (`IsGMPCouplingV2`) whose conditioning event `𝒟` has positive probability, the
`k`-th cycle record `𝒴_k`, `k ≥ 1`, satisfies `𝔼[Φ(𝒴_k)] = 𝔼[Φ(𝒴_0) | 𝒟]` for every bounded
measurable function `Φ` of the future state (`regen.marginal`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.regeneration_renewal
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
    ∀ (I : CoupledPathLawInput d hd) (P : QuenchedPathLaws d) (Q : EnvironmentLaw d Λ₀ r₀),
      ∀ hQ : I.Q = Q.measure,
      ∀ hGMP : IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P I.K,
      ∀ hD : (annealedCoupledLaw I.Q I.K) (cycleConditioningEvent hd (l / lam)) ≠ 0,
      ∀ k : ℕ, 1 ≤ k →
        AEMeasurable (cycleRecord hd lam l k) (annealedCoupledLaw I.Q I.K) ∧
        AEMeasurable (cycleRecord hd lam l 0) (annealedCoupledLaw I.Q I.K) ∧
        ∀ Φ : FutureState d (forceCoord hd) (l / lam) → ℝ,
          Measurable Φ → BoundedRealTest Φ →
          (∫ ωz, Φ (cycleRecord hd lam l k ωz) ∂(annealedCoupledLaw I.Q I.K)) =
            ∫ ωz, Φ (cycleRecord hd lam l 0 ωz)
              ∂((@cycleConditionedLaw d I.Q I.Q_probability I.K (hQ ▸ hGMP.1) hd (l / lam)
                hD).1) := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hren⟩ := renewalLemma31Input_of_inputs hLoc
    hTail d hd Λ₀ r₀
  refine ⟨l₀, hl₀, ?_⟩
  intro l hl δ hδ0 hδ1 lam hl0 hl1 I P Q hQ hGMP hD k hk
  have hD' : annealedCoupledLaw Q.measure I.K
      (Carriers.cycleConditioningEvent hd (l / lam)) ≠ 0 := by
    simpa only [hQ] using hD
  simpa only [hQ] using hren Q l hl δ hδ0 hδ1 lam hl0 hl1 P I.K hGMP hD' k hk

end EinsteinRelation.Frozen

end RegenerationRenewal

section RegenerationOccupation

open MeasureTheory
open EinsteinRelation.Frozen.DensityCarriers
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers

namespace EinsteinRelation.Frozen

/-- **Proposition 3.2** (`regen.occupation`): occupation bounds for local functions.

For `d ≥ 2`, `Λ₀ ≥ 1` and `r₀ ≥ 1` there is `l₀ > r₀ / 2` such that for every `l ≥ l₀` there is
`p₀ > 1` such that for every `p ≥ p₀` there is `C ≥ 0` with the following property. For every
environment law `Q`, force `λ ∈ (0, 1]` and reduced diffusion started at the origin with the
law of Gantert, Mathieu and Piatnitski, every function `G` of the environment in `B_{l/λ}` with
`G ∈ L^p`, every `T > 0` and every `s > 0`:
`𝔼 ∫₀ᵀ |G(ω_t)| dt ≤ C (T + λ⁻²) ‖G‖_{L^p}` (`regen.occupation-time`), and every density
`ρ_s` of the environment at an independent exponential time of rate `s` satisfies
`𝔼[ρ_s |G|] ≤ C (1 + s λ⁻²) ‖G‖_{L^p}` (`regen.occupation-resolvent`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.regeneration_occupation
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
    ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
    ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ I : CoordinatePathLawInput d hd,
        (I.Q = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
          (originLaw I.P)) →
      ∀ G : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
        MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
      ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
        (∫⁻ z : FieldPair d × Path d,
            (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (reducedObservationAt t.toNNReal z)|)
          ∂(annealedCoordinateJoint I)) ≤
          ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) ∧
        ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity I s rho →
          (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
            ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
              eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) := by
  intro d hd Λ₀ r₀ hΛ₀ hr₀
  obtain ⟨l₀, hl₀, hocc⟩ :=
    occupationStatement_of_inputs hE
      hTail hGir
      hInv hRF hLoc d hd Λ₀ r₀ hΛ₀ hr₀
  refine ⟨l₀, hl₀, fun l hl => ?_⟩
  obtain ⟨p₀, hp₀, hp⟩ := hocc l hl
  refine ⟨p₀, hp₀, fun p hpp => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hp p hpp
  refine ⟨C, hC, ?_⟩
  intro Q lam hl0 hl1 I hI
  exact hbound Q lam hl0 hl1 I.Q I.P I.origin_probability hI

end EinsteinRelation.Frozen

end RegenerationOccupation

section EntropyFisher

open MeasureTheory
open EinsteinRelation.Frozen.DensityCarriers
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers

namespace EinsteinRelation.Frozen

/-- **Lemma 4.1** (`entropy.fisher`): the Fisher information bound.

For `d ≥ 2`, every environment law `Q` whose reduced reference law is stationary, every force
`λ ∈ (0, 1]`, the reduced diffusion from the origin, every `s > 0` and every density `ρ_s` of
the environment at an independent exponential time of rate `s`, there is a weak horizontal
derivative `Dρ_s` with `|Dρ_s| ∈ L¹` and
`𝔼[Dρ_s · a Dρ_s / ρ_s] ≤ 4 Λ λ²`, with the integrand set to zero on `{ρ_s = 0}`; here
`Λ = sourceReducedBound Λ₀` is the ellipticity constant of the reduced coefficient `a`
(`entropy.fisher.bound`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.entropy_fisher_bound
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ I : CoordinatePathLawInput d hd,
    (I.Q = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw I.P)) →
  ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity I s rho →
    ∃ Drho : FieldPair d → Vec d,
      HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho ∧
      Integrable (fun w => euclideanNorm (Drho w)) (reducedReferenceLaw Q) ∧
      (∫⁻ w, ENNReal.ofReal
          (if rho w = 0 then 0 else dot (Drho w) ((w.1 0).mulVec (Drho w)) / rho w)
          ∂(reducedReferenceLaw Q)) ≤
        ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2) := by
  intro Q hQ lam hl0 hl1 I hyp s rho hrho
  exact EinsteinRelation.Closure.entropyFisherV2Twin_of_inputs hFOT
    hGir hInv hRF d hd Λ₀ r₀ Q hQ lam hl0 hl1 I.Q I.P I.origin_probability hyp s rho hrho

end EinsteinRelation.Frozen

end EntropyFisher

section EntropyDivergence

open MeasureTheory
open EinsteinRelation.Frozen.DensityCarriers
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers

namespace EinsteinRelation.Frozen

/-- **Lemma 4.2** (`entropy.divergence`): the divergence estimate.

For `d ≥ 2`, `Λ₀` and `r₀` there are `l₀ > r₀ / 2`, then for every `l ≥ l₀` an exponent
`p₀ > 1`, and for every `p ≥ p₀` a constant `C ≥ 0`, such that for every environment law `Q`
with stationary reduced reference law, `λ ∈ (0, 1]`, `0 < s ≤ λ²`, density `ρ_s` with weak
horizontal derivative `Dρ_s`, and vector field `F` of the environment in `B_{l/(2λ)}` with
`|F| ∈ L^{2p}`: `Dρ_s · F` is integrable and `|𝔼[Dρ_s · F]| ≤ C λ ‖F‖_{L^{2p}}`
(`entropy.divergence.bound`); and if `h ∈ L^{2p}` is the weak horizontal divergence of `F`,
then `𝔼[ρ_s h] = -𝔼[Dρ_s · F]`.

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.entropy_divergence_bound
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
  ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧
  ∀ p : ℝ, p₀ ≤ p → ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ I : CoordinatePathLawInput d hd,
    (I.Q = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw I.P)) →
  ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
  ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity I s rho →
  ∀ Drho : FieldPair d → Vec d,
    HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
  ∀ F : FieldPair d → Vec d,
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] F →
    MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
    (Integrable (fun w => dot (Drho w) (F w)) (reducedReferenceLaw Q) ∧
      ENNReal.ofReal (abs (∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q))) ≤
        ENNReal.ofReal (C * lam) *
          eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
            (reducedReferenceLaw Q)) ∧
    ∀ h : FieldPair d → ℝ, MemLp h (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
      HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ F h →
      Integrable (fun w => rho w * h w) (reducedReferenceLaw Q) ∧
        (∫ w, rho w * h w ∂(reducedReferenceLaw Q)) =
          -(∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q)) := by
  have H32 := EinsteinRelation.occupationStatement_of_inputs
    hE hTail hGir hInv hRF hLoc
  have H := EinsteinRelation.Closure.entropyDivergenceV2_of_inputs
    hFOT hGir hInv hRF H32 d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hl⟩ := H
  refine ⟨l₀, hl₀, fun l hl' => ?_⟩
  obtain ⟨p₀, hp₀, hp⟩ := hl l hl'
  refine ⟨p₀, hp₀, fun p hp' => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hp p hp'
  refine ⟨C, hC, ?_⟩
  intro Q hQ lam hl0 hl1 I hI s hs rho hrho Drho hDrho F hF hMemF
  exact hbound Q hQ lam hl0 hl1 I.Q I.P I.origin_probability hI s hs rho hrho Drho hDrho F hF
    hMemF

end EinsteinRelation.Frozen

end EntropyDivergence

section EntropyResolvent

open MeasureTheory
open EinsteinRelation.Frozen.DensityCarriers
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers

namespace EinsteinRelation.Frozen

/-- **Lemma 4.3** (`entropy.resolvent`): the resolvent identity and bound.

With the quantifiers of Lemma 4.2: if `f`, `Df`, `h` and `G` are functions of the environment
in `B_{l/(2λ)}` in `L^{2p}` and `𝓛^λ f = h + D · G` weakly, then
`s 𝔼[ρ_s f] - s 𝔼[f] = 𝔼[ρ_s h] - 𝔼[Dρ_s · G]` (`entropy.resolvent.identity`) and
`|𝔼[ρ_s h]| ≤ C s ‖f‖_{L^{2p}} + C λ ‖G‖_{L^{2p}}` (`entropy.resolvent.bound`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.entropy_resolvent_bound
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
  ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧
  ∀ p : ℝ, p₀ ≤ p → ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ I : CoordinatePathLawInput d hd,
    (I.Q = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw I.P)) →
  ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
  ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity I s rho →
  ∀ Drho : FieldPair d → Vec d,
    HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
  ∀ f : FieldPair d → ℝ, ∀ Df : FieldPair d → Vec d,
  ∀ h : FieldPair d → ℝ, ∀ G : FieldPair d → Vec d,
    MemLp f (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
    MemLp (fun w => euclideanNorm (Df w)) (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
    MemLp h (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
    MemLp (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] f →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] Df →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] h →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] G →
    SatisfiesReducedGeneratorEquation (reducedReferenceLaw Q) hQ lam f Df h G
        (⟨0, by omega⟩ : Fin d) →
    (Integrable (fun w => rho w * f w) (reducedReferenceLaw Q) ∧
      Integrable (fun w => rho w * h w) (reducedReferenceLaw Q) ∧
      Integrable (fun w => dot (Drho w) (G w)) (reducedReferenceLaw Q) ∧
      s.1 * (∫ w, rho w * f w ∂(reducedReferenceLaw Q)) -
          s.1 * (∫ w, f w ∂(reducedReferenceLaw Q)) =
        (∫ w, rho w * h w ∂(reducedReferenceLaw Q)) -
          (∫ w, dot (Drho w) (G w) ∂(reducedReferenceLaw Q))) ∧
    ENNReal.ofReal (abs (∫ w, rho w * h w ∂(reducedReferenceLaw Q))) ≤
      ENNReal.ofReal (C * s.1) * eLpNorm f (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) +
        ENNReal.ofReal (C * lam) *
          eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p))
            (reducedReferenceLaw Q) := by
  obtain ⟨l₀, hl₀, hres⟩ :=
    EinsteinRelation.Closure.entropyResolventV2Twin_of_inputs hFOT
      hGir hInv hRF
      (occupationStatement_of_inputs hE hTail hGir
        hInv hRF hLoc)
      d hd Λ₀ r₀
  refine ⟨l₀, hl₀, fun l hl => ?_⟩
  obtain ⟨p₀, hp₀, hp⟩ := hres l hl
  refine ⟨p₀, hp₀, fun p hpp => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hp p hpp
  refine ⟨C, hC, ?_⟩
  intro Q hQ lam hl0 hl1 I hyp s hs rho hrho Drho hDrho f Df h G hf hDf hh hG hmf hmDf hmh hmG hEq
  exact hbound Q hQ lam hl0 hl1 I.Q I.P I.origin_probability hyp s hs rho hrho Drho hDrho
    f Df h G hf hDf hh hG hmf hmDf hmh hmG hEq

end EinsteinRelation.Frozen

end EntropyResolvent

section CorrectorMoments

open MeasureTheory
open EinsteinRelation.Correctors (reducedEnvironmentLaw canonicalCorrectorGradient
  reducedCoefficientObservationSigma HasHeatSelectedSkewCorrectorColumn)
open EinsteinRelation.Correctors.NormalizedScalarCorrectorMeaning
  (IsNormalizedCanonicalScalarCorrector)
open EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport
  (Point SourceMollifier sourceScaledMollifierKernel)
open EinsteinRelation.Correctors.StationarySpatialRealization (spatialRealization)

namespace EinsteinRelation.Frozen

/-- **Lemma 5.1** (`corrector.moments`): moments of the correctors.

For `d ≥ 2`, `Λ₀`, `r₀` and `m ≥ 2` there is `C` such that, for every environment law `Q`
and mollifier `ζ`: `𝔼 |Dφ_i(0)|^m ≤ C` for every `i`; and for every `R ≥ 1`, `y` and `i`,
the normalized scalar corrector `φ_i` and the heat-selected skew corrector `σ_i` satisfy
`𝔼 ⨍_{B_{2R}(y)} (|φ_i - (φ_i)_{B_{2R}(y)}|^m + |σ_i - (σ_i)_{B_{2R}(y)}|^m) ≤ C 𝒜_d(R)^m`
(`eq.corrector-moments`), where `𝒜_d(R)` is `correctorAmplitude d R`.

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.corrector_moments
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative) :
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m → ∃ C : ℝ,
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (ζ : SourceMollifier d),
      (∀ i : Fin d,
        ∫⁻ ω, ENNReal.ofReal
            (euclideanNorm
              ((spatialRealization (canonicalCorrectorGradient Q i :
                  Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                ((0 : Vec d), ω)).ofLp) ^ m)
          ∂(reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) ∧
      ∀ (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
        (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
        IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
        HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
        ∫⁻ ω, (⨍⁻ x in Metric.ball y (2 * R),
            (ENNReal.ofReal (|φ ω x - (⨍ z in Metric.ball y (2 * R), φ ω z ∂volume)| ^ m) +
              ENNReal.ofReal
                (frobeniusNorm
                  (σ ω (WithLp.ofLp x) -
                    Matrix.of (fun (a b : Fin d) =>
                      ⨍ z in Metric.ball y (2 * R), σ ω (WithLp.ofLp z) a b ∂volume)) ^ m))
            ∂volume)
          ∂(reducedEnvironmentLaw Q)
          ≤ ENNReal.ofReal (C * EinsteinRelation.Correctors.correctorAmplitude d R ^ m) := by
  exact EinsteinRelation.Correctors.correctorMoments_of_literature
    h45 h46 h47 h68 h614 h615 h616 EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi
    EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi h832 h836

end EinsteinRelation.Frozen

end CorrectorMoments

section CorrectorConditional

open MeasureTheory
open EinsteinRelation.Correctors (reducedEnvironmentLaw canonicalCorrectorGradient
  reducedCoefficientObservationSigma HasHeatSelectedSkewCorrectorColumn)
open EinsteinRelation.Correctors.NormalizedScalarCorrectorMeaning
  (IsNormalizedCanonicalScalarCorrector)
open EinsteinRelation.Correctors.NormalizedSpatialRepresentativeSupport
  (Point SourceMollifier sourceScaledMollifierKernel)
open EinsteinRelation.Correctors.StationarySpatialRealization (spatialRealization)

namespace EinsteinRelation.Frozen

/-- **Lemma 5.2** (`corrector.conditional`): conditional localization of the correctors.

Assume that, for almost every environment, the scalar corrector `φ_i` and the skew corrector
`σ_i` are continuous. For `d ≥ 2`, `Λ₀`, `r₀`, a mollifier `ζ` and `m ≥ 2` there is `C` such
that for every environment law `Q`, `R ≥ 1`, `y` and `i`:
`‖Dφ_i(y) - 𝔼[Dφ_i(y) | ℱ(B_{8R}(y))]‖_{L^m} ≤ C R^{-d/2}`
(`eq.corrector-gradient-conditional`), and if `d = 2` the same conditional error of the
centered values `[φ_i]_{R,y}(y)` and `[σ_i]_{R,y}(y)` is at most `C`
(`eq.corrector-value-conditional`). Here `ℱ(B)` is the σ-algebra generated by the
coefficient in `B`.

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.corrector_conditional
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel) :
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ) (ζ : SourceMollifier d) (m : ℝ), 2 ≤ m → ∃ C : ℝ,
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
      (φ : FieldPair d → Point d → ℝ) (σ : FieldPair d → Vec d → Mat d),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ →
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) →
      let μ := reducedEnvironmentLaw Q
      let obsSigma := reducedCoefficientObservationSigma
        ((fun x : Vec d => (WithLp.toLp 2 x : Point d)) ⁻¹' Metric.ball y (8 * R))
      let grad : FieldPair d → Vec d := fun ω =>
        (spatialRealization (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 μ) (WithLp.ofLp y, ω)).ofLp
      let cφ : FieldPair d → ℝ := fun ω =>
        φ ω y - (∫ z, sourceScaledMollifierKernel ζ R y z * φ ω z ∂volume)
      let cσ : FieldPair d → Mat d := fun ω =>
        Matrix.of (fun (a b : Fin d) =>
          σ ω (WithLp.ofLp y) a b -
            (∫ z, sourceScaledMollifierKernel ζ R y z * σ ω (WithLp.ofLp z) a b ∂volume))
      eLpNorm (fun ω => euclideanNorm (grad ω - condExp obsSigma μ grad ω))
          (ENNReal.ofReal m) μ
        ≤ ENNReal.ofReal (C * R ^ (-(d : ℝ) / 2)) ∧
      (d = 2 →
        eLpNorm (fun ω => cφ ω - condExp obsSigma μ cφ ω) (ENNReal.ofReal m) μ +
          eLpNorm (fun ω => frobeniusNorm (Matrix.of (fun (a b : Fin d) =>
              cσ ω a b - condExp obsSigma μ (fun ω' => cσ ω' a b) ω)))
            (ENNReal.ofReal m) μ
          ≤ ENNReal.ofReal C) := by
  exact EinsteinRelation.Closure.correctorConditional_of_cited_inputs
    h45 h46 h47 h68 h614 h615 h616 EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi
    EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi h832 h836 hdecay hreg hEll hE1

end EinsteinRelation.Frozen

end CorrectorConditional

section CorrectorLocal

open MeasureTheory
open scoped BigOperators
open EinsteinRelation.Correctors (reducedEnvironmentLaw reducedEnvironmentLaw_stationary
  reducedCoefficientObservationSigma canonicalCorrectorGradient)
open EinsteinRelation.Correctors.StationarySpatialRealization (spatialRealization)

namespace EinsteinRelation.Frozen

/-- **Proposition 5.3** (`corrector.local`): local correctors.

For `d ≥ 2`, `Λ₀` and `r₀` there are, for every environment law `Q`, `R ≥ 1` and `i`, a
scalar field `φ_{i,R}`, a skew-symmetric matrix field `Σ_{i,R}`, a vector field `F_{i,R}` and
a weak horizontal derivative `Dφ_{i,R}`, measurable with respect to the coefficient in
`B_{33R}`, such that `a (e_i + Dφ_{i,R}) - ā e_i - F_{i,R}` is the row-wise weak divergence of
`Σ_{i,R}` (`eq.local-flux`); and for every `m ≥ 2` there is `C`, independent of `Q`, `R` and
`i`, with `‖φ_{i,R}‖_{L^m} + ‖Σ_{i,R}‖_{L^m} ≤ C 𝒜_d(R)` (`eq.local-corrector-bounds`) and
`‖F_{i,R}‖_{L^m} + ‖Dφ_{i,R} - Dφ_i‖_{L^m} ≤ C R⁻¹` (`eq.refined-local-errors`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.corrector_local
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel)
    (hH2 : EinsteinRelation.External.AKM.CorrectorWeakH2) :
  ∀ (d : ℕ) [Fact (2 ≤ d)] (Λ₀ r₀ : ℝ),
    ∃ (phi : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → ℝ)
      (skew : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Mat d)
      (flux : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d)
      (grad : (Q : EnvironmentLaw d Λ₀ r₀) → ℝ → Fin d → FieldPair d → Vec d),
      (∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        (Measurable[reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => phi Q R i ω) ∧
            Measurable[reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => skew Q R i ω) ∧
            Measurable[reducedCoefficientObservationSigma
              {y : Vec d | euclideanNorm (y - 0) < 33 * R}] (fun ω => flux Q R i ω)) ∧
        (∀ ω, (skew Q R i ω).transpose = -(skew Q R i ω)) ∧
        HasWeakHorizontalGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) (phi Q R i) (grad Q R i) ∧
        (∀ j : Fin d,
          HasWeakHorizontalDivergence (reducedEnvironmentLaw Q)
            (reducedEnvironmentLaw_stationary Q)
            (fun (ω : FieldPair d) (k : Fin d) => skew Q R i ω j k)
            (fun ω : FieldPair d =>
              (∑ k, (ω.1 0) j k * (unitVector i k + grad Q R i ω k)) -
                (EinsteinRelation.Frozen.Correctors.homogenizedCoefficientColumn Q i).ofLp j -
                flux Q R i ω j))) ∧
      ∀ m : ℝ, 2 ≤ m → ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 1 ≤ R → ∀ i : Fin d,
        (eLpNorm (phi Q R i) (ENNReal.ofReal m) (reducedEnvironmentLaw Q) +
            eLpNorm (fun ω => EinsteinRelation.frobeniusNorm (skew Q R i ω)) (ENNReal.ofReal m)
              (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * EinsteinRelation.Correctors.correctorAmplitude d R)) ∧
        (eLpNorm (fun ω => euclideanNorm (flux Q R i ω)) (ENNReal.ofReal m)
              (reducedEnvironmentLaw Q) +
            eLpNorm (fun ω : FieldPair d =>
                euclideanNorm (fun j : Fin d =>
                  grad Q R i ω j -
                    (spatialRealization (canonicalCorrectorGradient Q i :
                        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                      ((0 : Vec d), ω)).ofLp j))
              (ENNReal.ofReal m) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (C * R⁻¹)) := by
  exact EinsteinRelation.correctorLocal_of_construction
    (EinsteinRelation.Closure.correctorLocalConstruction_of_cited_inputs
      h45 h46 h47 h68 h614 h615 h616 EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi
      EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi h832 h836 hdecay hreg hEll
      hE1 hH2)

end EinsteinRelation.Frozen

end CorrectorLocal

section ScalarDecomposition

open MeasureTheory
open EinsteinRelation.Frozen.DensityCarriers
open EinsteinRelation.Frozen.ValidAnnealedLawCarriers
open EinsteinRelation.Frozen.Correctors

namespace EinsteinRelation.Frozen

/-- **Proposition 6.1** (`scalar.decomposition`): decomposition of local scalar fields.

For `d ≥ 2`, `Λ₀ ≥ 1` and `r₀ ≥ 1` there is `C₀ > 0`, and with the quantifiers on `l` and
`p` of Proposition 3.2, for every bound `M_{4p}` a constant `C`, such that for every
environment law `Q` with stationary reduced reference law, every dyadic `R ≥ 2` and every
scalar averaging field `f = f_R` with moment bound `M`: there are fields `ψ_R`, `h_R`, `e_R`
(scalar) and `E_R`, `P_R` (vector valued) of the environment in `B_{C₀R}` with
`f_R = 𝓛⁰ ψ_R + D · E_R + e_R` and `a e₁ · Dψ_R = D · P_R + h_R` weakly
(`eq.scalar-decomposition`, `eq.scalar-drift-decomposition`), and the bounds
(`eq.scalar-decomposition-bounds`) `‖ψ_R‖ + ‖P_R‖ ≤ C R`, `‖Dψ_R‖ ≤ C log(2 + R)`,
`‖E_R‖ + ‖h_R‖ ≤ C`, `‖e_R‖ ≤ C R⁻¹` in `L^{2p}`; and if `λ ∈ (0, 1]` and
`C₀ R ≤ l / (2λ)`, then for every `0 < s ≤ λ²` and density `ρ_s`,
`|𝔼[ρ_s f_R]| ≤ C (s R + λ + λ² R + R⁻¹)` (`eq.scalar-response`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.scalar_decomposition
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel)
    (hH2 : EinsteinRelation.External.AKM.CorrectorWeakH2)
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
  ∀ M4p : ℝ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ hQ : IsStationary (reducedReferenceLaw Q),
  ∀ M : ℝ → ℝ, M (4 * p) = M4p →
  ∀ R : ℝ, 2 ≤ R → (∃ k : ℕ, R = 2 ^ k) →
  ∀ f : FieldPair d → ℝ, IsScalarAveragingField Q M R f →
    (∃ (ψ h e : FieldPair d → ℝ) (Dψ E P : FieldPair d → Vec d),
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] ψ ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] h ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] e ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] E ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] P ∧
      SatisfiesReducedGeneratorEquation (reducedReferenceLaw Q) hQ 0 ψ Dψ
        (fun ω => f ω - e ω) (fun ω => -(E ω)) (⟨0, by omega⟩ : Fin d) ∧
      HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ P
        (fun ω =>
          dot ((ω.1 (0 : Vec d)).mulVec (unitVector (⟨0, by omega⟩ : Fin d))) (Dψ ω) - h ω) ∧
      eLpNorm ψ (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) +
          eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
            (reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * R) ∧
      eLpNorm (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * Real.log (2 + R)) ∧
      eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) +
          eLpNorm h (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) ≤
        ENNReal.ofReal C ∧
      eLpNorm e (ENNReal.ofReal (2 * p)) (reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * R⁻¹)) ∧
    (∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1, C₀ * R ≤ l / (2 * lam) →
      ∀ I : CoordinatePathLawInput d hd,
        (I.Q = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
          (originLaw I.P)) →
        ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
        ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity I s rho →
          Integrable (fun w => rho w * f w) (reducedReferenceLaw Q) ∧
          |∫ w, rho w * f w ∂(reducedReferenceLaw Q)| ≤
            C * (s.1 * R + lam + lam ^ 2 * R + R⁻¹)) := by
  have H := EinsteinRelation.Closure.scalarDecomposition_of_cited_inputs
    h45 h46 h47 h68 h614 h615 h616 EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi
    EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi h832 h836 hdecay hreg hEll hE1
    hH2 hFOT hGir hInv hRF hE hTail hLoc
  intro d hd L r₀ hL hr
  obtain ⟨C₀, hC₀, l₀, hl₀, hl⟩ := H d hd L r₀ hL hr
  refine ⟨C₀, hC₀, l₀, hl₀, ?_⟩
  intro l hl'
  obtain ⟨p₀, hp₀, hp⟩ := hl l hl'
  refine ⟨p₀, hp₀, ?_⟩
  intro p hp' M4p
  obtain ⟨C, hC, hQ⟩ := hp p hp' M4p
  refine ⟨C, hC, ?_⟩
  intro Q hstat M hM R hR hdyad f hf
  obtain ⟨hdecomp, hresponse⟩ := hQ Q hstat M hM R hR hdyad f hf
  refine ⟨hdecomp, ?_⟩
  intro lam hl0 hl1 hscale I hI s hs rho hrho
  exact hresponse lam hl0 hl1 hscale I.Q I.Q_probability I.P I.origin_probability
    hI s hs rho hrho

end EinsteinRelation.Frozen

end ScalarDecomposition

section MobilityRateSharp

open MeasureTheory Filter Topology

namespace EinsteinRelation.Frozen

/-- **Proposition 7.1** (`sharp.example`): the rate of Theorem 1.2 is attained.

For every `d ≥ 2` there are constants `Λ₀`, `r₀`, an environment law `Q` satisfying
Assumption 1.1 with these constants whose fields are almost surely smooth
(`IsSmoothFieldPair`), and `c > 0` such that, for every physical diffusion family `P` of
Gantert, Mathieu and Piatnitski for `Q`, every diffusivity `Σ_X` of the unforced diffusion and
every function `λ ↦ ℓ_X(λ)` that gives the quenched velocity for each `λ ∈ (0, 1]`,
`((ℓ_X(λ) / λ - Σ_X e₁) · e₁) / λ → c` as `λ ↓ 0` (`eq.sharp-expansion`).

The hypotheses before the statement are the literature inputs used by the proof;
see the module docstring. -/
theorem _root_.EinsteinRelation.mobility_rate_sharp
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel)
    (hH2 : EinsteinRelation.External.AKM.CorrectorWeakH2)
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality)
    (hRV : EinsteinRelation.External.GMPReducedVelocityExistence)
    (hTC : EinsteinRelation.External.GMPTimeChangeLaw)
    (hPos : EinsteinRelation.External.GMPPhysicalVelocityPositive)
    (hErg : EinsteinRelation.External.GMPEnvironmentProcessErgodic)
    (hIP : EinsteinRelation.External.GMPReducedInvarianceAbar)
    (hPF : EinsteinRelation.External.GMPPhysicalFamilyExistence)
    (hVX : EinsteinRelation.External.GMPVelocityExistence)
    (hW : ∀ d : ℕ, 2 ≤ d → EinsteinRelation.External.WhiteNoiseExistence d)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀),
    (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (P : DiffusionFamily d), IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
    ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
    ∀ (velocity : ℝ → Vec d),
      (∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
      Tendsto (fun lam : ℝ =>
          dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
            (unitVector (⟨0, by omega⟩ : Fin d)) / lam)
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  exact EinsteinRelation.Closure.sharpExample_of_cited_inputs
    h45 h46 h47 h68 h614 h615 h616 EinsteinRelation.Correctors.ballPoincareEstimate_of_deGiorgi
    EinsteinRelation.Correctors.localBoundednessEstimate_of_deGiorgi h832 h836 hdecay hreg hEll hE1
    hH2 hFOT hGir hInv hRF hE hTail hLoc hRV hPF hVX hTC hErg hIP hPos
    d hd (hW d hd)

end EinsteinRelation.Frozen

end MobilityRateSharp
