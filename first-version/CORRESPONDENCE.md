# Paper–Lean correspondence

This document maps the numbered results of the paper
*Quantitative Einstein relation for reversible diffusions in a random environment*
(Bou-Rabee and Xu) to their Lean declarations, together with the objects in their statements
and the results of the literature that the proofs assume. The paper is included under
[`paper/`](paper/); every label and line number below refers to `paper/main.tex`.

**Conventions.**

- Lean names in the tables are relative to the namespace `EinsteinRelation` unless written in
  full. The file column gives the path under the repository root.
- A row names the declaration that formalizes a statement. It is a reading aid: the fact that a
  declaration compiles does not by itself show that it says what the paper says. The statements
  of Theorem 1.2 and Proposition 7.1 are checked separately, by the comparator challenges in
  [`EinsteinRelationAudit/`](EinsteinRelationAudit/).
- The column *Literature inputs* gives the number of inputs that the theorem takes as
  hypotheses and their numbers in the table of literature inputs below (and in the README).

## Numbered results

| Paper | Label | Lean declaration | File | Literature inputs |
| --- | --- | --- | --- | --- |
| Theorem 1.2 | `t.main` | `EinsteinRelation.mobility_rate` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L102) | 27: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27 |
| Lemma 3.1 | `regen.renewal` | `EinsteinRelation.regeneration_renewal` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L167) | 2: 21, 22 |
| Proposition 3.2 | `regen.occupation` | `EinsteinRelation.regeneration_occupation` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L221) | 6: 17, 18, 19, 20, 21, 22 |
| Lemma 4.1 | `entropy.fisher` | `EinsteinRelation.entropy_fisher_bound` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L286) | 4: 16, 17, 18, 19 |
| Lemma 4.2 | `entropy.divergence` | `EinsteinRelation.entropy_divergence_bound` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L333) | 7: 16, 17, 18, 19, 20, 21, 22 |
| Lemma 4.3 | `entropy.resolvent` | `EinsteinRelation.entropy_resolvent_bound` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L402) | 7: 16, 17, 18, 19, 20, 21, 22 |
| Lemma 5.1 | `corrector.moments` | `EinsteinRelation.corrector_moments` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L489) | 9: 1, 2, 3, 4, 5, 6, 7, 8, 9 |
| Lemma 5.2 | `corrector.conditional` | `EinsteinRelation.corrector_conditional` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L556) | 13: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13 |
| Proposition 5.3 | `corrector.local` | `EinsteinRelation.corrector_local` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L627) | 14: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14 |
| Proposition 6.1 | `scalar.decomposition` | `EinsteinRelation.scalar_decomposition` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L715) | 21: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22 |
| Proposition 7.1 | `sharp.example` | `EinsteinRelation.mobility_rate_sharp` | [`MainTheorems.lean`](EinsteinRelation/MainTheorems.lean#L817) | 29: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30 |

Every numbered result of the paper is in this table except:

- Assumption 1.1 (`a.environment`), which is a definition: the structure `EnvironmentLaw`
  (see below);
- Conjecture 1.3 (`conj.expansion`), which is a conjecture and is not formalized.

Each theorem has the form *(literature inputs) → (statement)*. The statement after the inputs
was fixed before the proof was written, and is copied byte for byte from that fixed statement;
the definitions it uses are under [`EinsteinRelation/Frozen/`](EinsteinRelation/Frozen/) and in
the modules these import. The paper writes the intermediate results for fixed constants and
leaves some quantifiers implicit; the Lean statements make the order of quantifiers explicit
(for example "there exist `l₀`, then for every `l ≥ l₀` a `p₀ > 1`, then for every `p ≥ p₀` a
constant `C`"), which implies the paper's formulation.

## Objects in the statements

| Paper | Lean | File | Meaning |
| --- | --- | --- | --- |
| Assumption 1.1 (`a.environment`), (S1)–(S5) | `EnvironmentLaw` | [`Environment/Basic.lean`](EinsteinRelation/Environment/Basic.lean) | structure; (S1)–(S3) are `IsRegular`, (S4) `IsStationary`, (S5) `HasFiniteRange` |
| the fields `(a₀, V)` | `FieldPair` | [`Environment/Basic.lean`](EinsteinRelation/Environment/Basic.lean) | pairs of continuous fields, with the Borel σ-algebra of the compact-open topology |
| the diffusion `X^λ` (`eq.physical-tilt` and line 66) | `IsGMPPhysicalFamily` | [`Diffusion/GMPFamily.lean`](EinsteinRelation/Diffusion/GMPFamily.lean) | the GMP Section 7 process, through `GantertFixedEnvironmentRealization` |
| the fixed-environment GMP process | `External.GantertSection7Support.GantertFixedEnvironmentRealization` | [`External/GantertSection7Support.lean`](EinsteinRelation/External/GantertSection7Support.lean) | path law, Markov semigroup with heat-kernel density, reversibility, closed form |
| the time-changed diffusion `Y^λ` (Section 2) | `IsGMPReducedOriginLaw` | [`Diffusion/GMPFamily.lean`](EinsteinRelation/Diffusion/GMPFamily.lean) | GMP Section 7 process of the zero-potential pair `(e^{−2V} a₀, 0)` |
| the velocity `ℓ_X(λ)` (`eq.velocity-definition`) | `HasQuenchedVelocity` | [`Diffusion/Basic.lean`](EinsteinRelation/Diffusion/Basic.lean) | almost sure limit of `X(t)/t` for almost every environment |
| the diffusivity `Σ_X` | `HasDiffusivity` | [`Diffusion/Basic.lean`](EinsteinRelation/Diffusion/Basic.lean) | annealed invariance principle, with `IsBrownianLaw` and `rescalePath` |
| smooth fields (Proposition 7.1) | `IsSmoothFieldPair` | [`Environment/Smooth.lean`](EinsteinRelation/Environment/Smooth.lean) | `C^∞` entries of `a₀` and `C^∞` potential `V` |
| the law `Q` of the reduced environment (Sections 2–6) | `Frozen.DensityCarriers.reducedReferenceLaw` | [`Frozen/DensityCarriers/ReducedReferenceLaw.lean`](EinsteinRelation/Frozen/DensityCarriers/ReducedReferenceLaw.lean) | image of `Q.measure` under the reduction map `reduce` |
| the density `ρ_s` | `Frozen.DensityCarriers.IsReducedLaplaceDensity` | [`Frozen/DensityCarriers/IsReducedLaplaceDensity.lean`](EinsteinRelation/Frozen/DensityCarriers/IsReducedLaplaceDensity.lean) | density of the environment at an independent exponential time of rate `s` |
| the reduced diffusion from the origin (Sections 3–6) | `Frozen.ValidAnnealedLawCarriers.CoordinatePathLawInput` | [`Frozen/ValidAnnealedLawCarriers/CoordinatePathLawInput.lean`](EinsteinRelation/Frozen/ValidAnnealedLawCarriers/CoordinatePathLawInput.lean) | an environment law with a quenched origin path law; with `IsGMPReducedOriginLaw` |
| local functions, `𝓗_B` | `localSigma` | [`Environment/Basic.lean`](EinsteinRelation/Environment/Basic.lean) | σ-algebra generated by the fields on a set |
| `ℱ(B)` in Lemma 5.2 | `Correctors.reducedCoefficientObservationSigma` | [`Frozen/Correctors/ReducedCoefficientObservationSigma.lean`](EinsteinRelation/Frozen/Correctors/ReducedCoefficientObservationSigma.lean) | σ-algebra generated by the reduced coefficient on a set |
| the derivatives `D` and `D·` | `HasWeakHorizontalGradient` | [`Calculus/EnvironmentWeakCalculus.lean`](EinsteinRelation/Calculus/EnvironmentWeakCalculus.lean) | and `HasWeakHorizontalDivergence`: weak derivatives along translations |
| `𝓛^λ f = h + D·G` (Lemma 4.3) | `SatisfiesReducedGeneratorEquation` | [`Calculus/EnvironmentWeakCalculus.lean`](EinsteinRelation/Calculus/EnvironmentWeakCalculus.lean) | weak form of the generator equation |
| the scalar corrector `φ_i` | `Correctors.NormalizedScalarCorrectorMeaning.IsNormalizedCanonicalScalarCorrector` | [`Frozen/Correctors/NormalizedScalarCorrector.lean`](EinsteinRelation/Frozen/Correctors/NormalizedScalarCorrector.lean) | normalized by a mollified average at scale `R` |
| the flux corrector `σ_i` | `Correctors.HasHeatSelectedSkewCorrectorColumn` | [`Frozen/Correctors/HeatSelectedSkewCorrectorColumn.lean`](EinsteinRelation/Frozen/Correctors/HeatSelectedSkewCorrectorColumn.lean) | skew-symmetric, selected by the heat flow |
| `Dφ_i` | `Correctors.canonicalCorrectorGradient` | [`Correctors/CanonicalVariationalGradientSupport.lean`](EinsteinRelation/Correctors/CanonicalVariationalGradientSupport.lean) | the stationary corrector gradient (variational solution) |
| `𝒜_d(R)` | `Correctors.correctorAmplitude` | [`Correctors/CorrectorAmplitude.lean`](EinsteinRelation/Correctors/CorrectorAmplitude.lean) | `1` if `d ≥ 3`, `√(log(2 + R))` if `d = 2` |
| `ā e_i` | `Frozen.Correctors.homogenizedCoefficientColumn` | [`Frozen/Correctors/HomogenizedCoefficientColumn.lean`](EinsteinRelation/Frozen/Correctors/HomogenizedCoefficientColumn.lean) | column of the homogenized matrix of `a = e^{−2V} a₀` |
| the fields `f_R` (Proposition 6.1) | `Frozen.Correctors.IsScalarAveragingField` | [`Frozen/Correctors/IsScalarAveragingField.lean`](EinsteinRelation/Frozen/Correctors/IsScalarAveragingField.lean) | functions of the environment in `B_{33R}` with `‖H_t f_R‖_{L^m} ≤ M_m ((1+t)^{−1/2} + R⁻¹)` |
| the regeneration coupling (Section 3) | `Regeneration.Renewal.IsGMPCouplingV2` | [`Regeneration/RenewalCarriers.lean`](EinsteinRelation/Regeneration/RenewalCarriers.lean) | coupled path laws of the GMP regeneration construction |
| the coupled laws (Lemma 3.1) | `Frozen.ValidAnnealedLawCarriers.CoupledPathLawInput` | [`Frozen/ValidAnnealedLawCarriers/CoupledPathLawInput.lean`](EinsteinRelation/Frozen/ValidAnnealedLawCarriers/CoupledPathLawInput.lean) | an environment law with a coupled quenched kernel |
| the cycle records `𝒴_k` | `Regeneration.Renewal.cycleRecord` | [`Regeneration/RenewalCarriers.lean`](EinsteinRelation/Regeneration/RenewalCarriers.lean) | the record of the `k`-th regeneration cycle |
| the event `𝒟` and the law conditioned on it | `Regeneration.cycleConditioningEvent` | [`Frozen/Regeneration/CycleConditioningEvent.lean`](EinsteinRelation/Frozen/Regeneration/CycleConditioningEvent.lean) | and `Regeneration.cycleConditionedLaw` (`Frozen/Regeneration/CycleConditionedLaw.lean`) |

## Literature inputs

Abbreviations are those of the README (AKM, GT, FOT, GMP, DFGW, Shen). Page numbers are printed
page numbers. The docstring of each definition records its source and the conventions of its
transcription.

| # | Source | Lean predicate | File | Hypothesis |
| --- | --- | --- | --- | --- |
| 1 | AKM Theorem 4.1, (4.5), p. 124 | `External.AKM.ScalarStationaryEstimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h45` |
| 2 | AKM Theorem 4.1, (4.6), p. 124 (dimension two) | `External.AKM.ScalarPlanarL2Estimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h46` |
| 3 | AKM Theorem 4.1, (4.7), p. 124 | `External.AKM.ScalarHeatDifferenceEstimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h47` |
| 4 | AKM Lemma 6.1, (6.8), p. 246 | `External.AKM.FluxGradientEstimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h68` |
| 5 | AKM Proposition 6.2, (6.14), pp. 249–250 | `External.AKM.FluxStationaryEstimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h614` |
| 6 | AKM Proposition 6.2, (6.15), p. 250, for radii `r ≥ 2` | `External.AKM.FluxPlanarL2Estimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h615` |
| 7 | AKM Proposition 6.2, (6.16), p. 250 | `External.AKM.FluxHeatDifferenceEstimate` | [`External/AKMCorrectorOscillation.lean`](EinsteinRelation/External/AKMCorrectorOscillation.lean) | `h616` |
| 8 | GT Theorem 8.32, (8.86), p. 210 (homogeneous case) | `External.GilbargTrudinger.InteriorGradientEstimate` | [`External/GilbargTrudinger.lean`](EinsteinRelation/External/GilbargTrudinger.lean) | `h832` |
| 9 | GT Corollary 8.36, (8.91), p. 212, with the hypotheses of Theorem 8.32 | `External.GilbargTrudinger.InteriorRegularRepresentative` | [`External/GilbargTrudinger.lean`](EinsteinRelation/External/GilbargTrudinger.lean) | `h836` |
| 10 | AKM Theorem 9.1, (9.7), p. 349, for the flow (9.2), p. 347 | `External.AKM.ParabolicSemigroupKernelDecay` | [`External/AKMKernelSemigroup.lean`](EinsteinRelation/External/AKMKernelSemigroup.lean) | `hdecay` |
| 11 | AKM Remark 8.8, (8.25), p. 315 | `External.AKM.ParabolicLargeScale` | [`External/AKMLocalCorrectors.lean`](EinsteinRelation/External/AKMLocalCorrectors.lean) | `hreg` |
| 12 | AKM Theorem 3.3, (3.15)–(3.19), p. 75 | `External.AKM.EllipticLargeScale` | [`External/AKMLocalCorrectors.lean`](EinsteinRelation/External/AKMLocalCorrectors.lean) | `hEll` |
| 13 | AKM Proposition E.1, (E.1)–(E.4) and (E.7)–(E.11), pp. 499–501 | `External.AKM.ParabolicHeatKernel` | [`External/AKMHeatKernel.lean`](EinsteinRelation/External/AKMHeatKernel.lean) | `hE1` |
| 14 | AKM (4.126), p. 173 (case `d = 2`), accompanying Theorem 4.24 | `External.AKM.CorrectorWeakH2` | [`External/AKMLocalCorrectors.lean`](EinsteinRelation/External/AKMLocalCorrectors.lean) | `hH2` |
| 15 | AKM Theorem 4.1, (4.3), p. 124, at heat times `t ≥ 1` | `AKMFluxDecayLargeTime` | [`Mobility/AKMFluxDecaySplit.lean`](EinsteinRelation/Mobility/AKMFluxDecaySplit.lean) | `hAKM` |
| 16 | FOT Theorem 5.5.5, p. 275, with (5.5.8)–(5.5.11), under (4.2.9), p. 165; for the GMP Section 7 processes (GMP p. 32 and Lemma 7.1, p. 33) | `FukushimaDecompositionInput` | [`Mobility/QuenchedDriftFromFukushima.lean`](EinsteinRelation/Mobility/QuenchedDriftFromFukushima.lean) | `hFOT` |
| 17 | GMP Proposition 7.2 and (7.4), pp. 33–34, with Hölder's inequality | `GirsanovEndpointStep` | [`Regeneration/FirstRewardSteps.lean`](EinsteinRelation/Regeneration/FirstRewardSteps.lean) | `hGir` |
| 18 | GMP pp. 8, 10 and 32; DFGW Section 6, (6.9)–(6.13) | `UnforcedEnvironmentInvarianceStep` | [`Regeneration/FirstRewardSteps.lean`](EinsteinRelation/Regeneration/FirstRewardSteps.lean) | `hInv` |
| 19 | GMP Section 7, p. 32, and (3.8)–(3.9), p. 10 | `External.GMPReducedFamilyExistence` | [`External/GMPReducedInputs.lean`](EinsteinRelation/External/GMPReducedInputs.lean) | `hRF` |
| 20 | GMP Proposition 5.4, p. 23, extended to measurable coefficients in Section 7, p. 32; kernel form of Shen (2003), Theorem 2.1, (2.8)–(2.9) | `GMPCouplingExistsV2Input` | [`Regeneration/OccupationFromRenewal.lean`](EinsteinRelation/Regeneration/OccupationFromRenewal.lean) | `hE` |
| 21 | GMP Lemmas 5.7 (p. 25) and 5.8 (p. 26) and (5.20), p. 25, with Section 7, p. 32 | `GMPCouplingTailsV2Input` | [`Regeneration/OccupationFromRenewal.lean`](EinsteinRelation/Regeneration/OccupationFromRenewal.lean) | `hTail` |
| 22 | GMP proof of Proposition 7.2, pp. 34–35 | `External.GMPKernelLocality` | [`External/GMPLocalityInput.lean`](EinsteinRelation/External/GMPLocalityInput.lean) | `hLoc` |
| 23 | GMP pp. 5 and 10 | `External.GMPReducedVelocityExistence` | [`External/GMPReducedInputs.lean`](EinsteinRelation/External/GMPReducedInputs.lean) | `hRV` |
| 24 | GMP Section 3, p. 10, and Section 7, p. 32 | `External.GMPTimeChangeLaw` | [`External/GMPReducedInputs.lean`](EinsteinRelation/External/GMPReducedInputs.lean) | `hTC` |
| 25 | GMP Section 2.3, p. 5 | `External.GMPPhysicalVelocityPositive` | [`External/GMPPhysicalInputs.lean`](EinsteinRelation/External/GMPPhysicalInputs.lean) | `hPos` |
| 26 | GMP p. 8 and p. 10 | `External.GMPEnvironmentProcessErgodic` | [`External/GMPReducedInputs.lean`](EinsteinRelation/External/GMPReducedInputs.lean) | `hErg` |
| 27 | GMP Section 2.2, pp. 4 and 10 | `External.GMPReducedInvarianceAbar` | [`External/GMPReducedInputs.lean`](EinsteinRelation/External/GMPReducedInputs.lean) | `hIP` |
| 28 | GMP Section 7, p. 32, with the annealed law (2.5), p. 4 | `External.GMPPhysicalFamilyExistence` | [`External/GMPPhysicalInputs.lean`](EinsteinRelation/External/GMPPhysicalInputs.lean) | `hPF` |
| 29 | GMP Section 2.3, p. 5 (citing Shen), and Section 7, p. 32 | `External.GMPVelocityExistence` | [`External/GMPPhysicalInputs.lean`](EinsteinRelation/External/GMPPhysicalInputs.lean) | `hVX` |
| 30 | AKM Definition 5.1, Proposition 5.14 and Remark 5.15, pp. 192 and 201–202 | `∀ d, 2 ≤ d → WhiteNoiseExistence d` | [`External/WhiteNoise.lean`](EinsteinRelation/External/WhiteNoise.lean) | `hW` |

## Results of the literature that are proved here

| Source | Lean predicate | Proof |
| --- | --- | --- |
| GT (7.45), p. 164: Poincaré inequality on balls | `External.GilbargTrudinger.BallPoincareEstimate` | `Correctors.ballPoincareEstimate_of_deGiorgi` ([`Correctors/DeGiorgiGTBallPoincare.lean`](EinsteinRelation/Correctors/DeGiorgiGTBallPoincare.lean)), from the DeGiorgi library |
| GT Theorem 8.17, (8.46), p. 194: local boundedness | `External.GilbargTrudinger.LocalBoundednessEstimate` | `Correctors.localBoundednessEstimate_of_deGiorgi` ([`Correctors/DeGiorgiGTLocalBoundedness.lean`](EinsteinRelation/Correctors/DeGiorgiGTLocalBoundedness.lean)), from the DeGiorgi library |

## Statements without a formal counterpart

Conjecture 1.3. Every other numbered statement of the paper has the counterpart listed above.
