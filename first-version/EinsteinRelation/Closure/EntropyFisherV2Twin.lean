import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Calculus.Generator
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Entropy.FisherBoundAssembly
import EinsteinRelation.Environment.Basic
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.External.GMPReducedInputs
import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import EinsteinRelation.Regeneration.FirstRewardSteps

open MeasureTheory

namespace EinsteinRelation.Closure

/-- Lemma 4.1 (entropy.fisher, paper/main.tex:518-524), over the production twins: the
diffusion is the GMP Section 7 process. The coordinate-path structure is replaced by its fields
`Q`, `P` and `origin_probability`, and the probability of `Q` is omitted because the production
Fisher statement does not use it. Conditional on the four cited inputs. -/
theorem entropyFisherV2Twin_of_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (Carriers.reducedReferenceLaw Q)),
    ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
    ∀ (Q' : Measure (FieldPair d)) (P : QuenchedPathLaws d)
      (origin_probability : ∀ᵐ ω ∂Q', IsProbabilityMeasure (originLaw P ω)),
      (Q' = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
        (originLaw P)) →
    ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ,
      Carriers.IsReducedLaplaceDensity Q' P origin_probability s rho →
      ∃ Drho : FieldPair d → Vec d,
        HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho ∧
        Integrable (fun w => euclideanNorm (Drho w)) (Carriers.reducedReferenceLaw Q) ∧
        (∫⁻ w, ENNReal.ofReal
            (if rho w = 0 then 0 else dot (Drho w) ((w.1 (0 : Vec d)).mulVec (Drho w)) / rho w)
            ∂(Carriers.reducedReferenceLaw Q)) ≤
          ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2) := by
  intro Q hQ lam hl0 hl1 Q' P origin_probability hyp s rho hrho
  obtain ⟨rfl, hP⟩ := hyp
  exact Entropy.fisherBoundStatement_of_inputs hFOT hGir hInv hRF d hd Λ₀ r₀ Q hQ lam hl0 hl1
    P origin_probability hP s rho hrho

end EinsteinRelation.Closure
