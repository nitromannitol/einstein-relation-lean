import EinsteinRelation.Entropy.FisherBoundAssembly
import EinsteinRelation.Entropy.ResolventFromFisher
import EinsteinRelation.External.GMPReducedInputs
import EinsteinRelation.Mobility.MainTheoremFromPaperInputs
import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import EinsteinRelation.Regeneration.FirstRewardSteps

/-! # Lemma 4.3 (`entropy.resolvent`) over production twins

Source: `paper/main.tex:649-664`. The conclusion is the production Prop
`Entropy.ResolventStatement`. It is the conclusion of `entropyResolventV2` with the
coordinate-path structure replaced by its fields `IQ`, `P` and `origin_probability`.

The cited inputs are `FukushimaDecompositionInput` (FOT Theorem 5.5.5),
`GirsanovEndpointStep`, `UnforcedEnvironmentInvarianceStep` and
`External.GMPReducedFamilyExistence`. Lemma 4.1 is derived
(`Entropy.fisherBoundStatement_of_inputs`). Proposition 3.2 (`H32`,
`Entropy.OccupationStatement`) is an explicit hypothesis.
-/

namespace EinsteinRelation.Closure

/-- Lemma 4.3 (`entropy.resolvent`, `paper/main.tex:649-664`), over the production
twins. Conditional on the cited inputs and on Proposition 3.2. -/
theorem entropyResolventV2Twin_of_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    Entropy.ResolventStatement d hd Λ₀ r₀ :=
  Entropy.resolventStatement_of_fisher_occupation hFOT d hd Λ₀ r₀
    (Entropy.fisherBoundStatement_of_inputs hFOT hGir hInv hRF)
    (occupation_universal_of_statement H32)

end EinsteinRelation.Closure
