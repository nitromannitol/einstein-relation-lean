import EinsteinRelation.Correctors.ScalarDecompositionGlue
import EinsteinRelation.Entropy.FisherBoundAssembly
import EinsteinRelation.Entropy.ResolventFromFisher
import EinsteinRelation.External.GMPReducedInputs
import EinsteinRelation.Mobility.ClockEstimateFromSteps
import EinsteinRelation.Mobility.MainTheoremFromPaperInputs
import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import EinsteinRelation.Regeneration.FirstRewardSteps

/-! # Proposition 6.1 (scalar.decomposition) over the production twins

Source: `paper/main.tex:978-997`, with the diffusions of the GMP Section 7 process. The conclusion
is `EinsteinRelation.ScalarDecompositionTwin`, the production twin of the frozen statement
`EinsteinRelation.scalar_decomposition`: the carriers are the `Carriers.*` twins, and the
coordinate-path input is replaced by its fields.

The closure takes the cited inputs `FukushimaDecompositionInput` (FOT Theorem 5.5.5),
`GirsanovEndpointStep`, `UnforcedEnvironmentInvarianceStep` and `External.GMPReducedFamilyExistence`,
and the internal results `H32` (Proposition 3.2, `Entropy.OccupationStatement`) and `hCons` (the
decomposition construction of Proposition 6.1, `Correctors.DecompositionConstruction`). The Fisher
bound of Lemma 4.1 is derived from the cited inputs alone, and the resolvent bound of Lemma 4.3 from
those inputs and `H32`. The statement does not use Lemma 5.1 or Proposition 5.3. -/

namespace EinsteinRelation.Closure

/-- Proposition 6.1 (scalar.decomposition, `paper/main.tex` 978-997), over the
production twins. Conditional on the cited inputs and the internal results `H32` and `hCons`. -/
theorem scalarDecompositionV2Twin_of_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀)
    (hCons : Correctors.DecompositionConstruction) : ScalarDecompositionTwin := by
  have H41 := Entropy.fisherBoundStatement_of_inputs hFOT hGir hInv hRF
  have hOcc := occupation_universal_of_statement H32
  have H43 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.ResolventStatement d hd Λ₀ r₀ :=
    fun d hd Λ₀ r₀ => Entropy.resolventStatement_of_fisher_occupation hFOT d hd Λ₀ r₀ H41 hOcc
  exact Correctors.scalarDecompositionTwin_of_construction H41 H43 H32 hCons

end EinsteinRelation.Closure
