import EinsteinRelation.Entropy.DivergenceSecondAssertion
import EinsteinRelation.Entropy.FisherBoundAssembly
import EinsteinRelation.Mobility.MainTheoremFromPaperInputs

/-! # Lemma 4.2 (`entropy.divergence`) from the cited inputs and Proposition 3.2

Source: `paper/main.tex:625-632`. The diffusion is the GMP Section 7 process. The conclusion is
`Entropy.DivergenceStatement`, the production twin of Lemma 4.2 with the coordinate-path law given by
its fields `IQ`, `P` and `origin_probability`.

Lemma 4.1 is derived by `Entropy.fisherBoundStatement_of_inputs` from the cited Fukushima
decomposition, Girsanov endpoint, unforced environment invariance and reduced family existence.
Proposition 3.2 enters as the explicit premise `H32`, since its proof on main depends on the
internal slice-factor premise of Lemma 3.1 (`FirstRegenerationSliceFactorInput`).
-/

namespace EinsteinRelation.Closure

/-- Lemma 4.2 (`entropy.divergence`, `paper/main.tex:625-632`), both assertions, from the cited
Fukushima, Girsanov, invariance and reduced-family inputs, and Proposition 3.2 (`H32`). -/
theorem entropyDivergenceV2_of_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    Entropy.DivergenceStatement d hd Λ₀ r₀ :=
  Entropy.divergenceStatement_of_fisher_occupation d hd Λ₀ r₀
    (Entropy.fisherBoundStatement_of_inputs hFOT hGir hInv hRF)
    (occupation_universal_of_statement H32)

end EinsteinRelation.Closure
