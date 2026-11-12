import EinsteinRelation.Entropy.DivergenceSecondAssertion
import EinsteinRelation.Entropy.WeakResolventFromDynkin

/-! # Lemmas 4.2 and 4.3 from Lemma 4.1 and Proposition 3.2

Source: `paper/main.tex` 625-681. `divergenceStatement_of_fisher_occupation` proves Lemma 4.2 from
the Fisher bound of Lemma 4.1 and the occupation bound of Proposition 3.2.
`weakResolventStep_of_fukushima` proves the weak resolvent identity from Lemma 4.2, Proposition 3.2
and the FOT input. With `resolvent_of_weak_divergence_occupation`, Lemma 4.3
(`ResolventStatement`) follows from Lemma 4.1, Proposition 3.2 and the FOT input.
-/

open MeasureTheory

namespace EinsteinRelation.Entropy

open EinsteinRelation.Carriers

/-- **Lemma 4.3** (`entropy.resolvent`, `paper/main.tex` 649-681) from the FOT input, the Fisher
bound of Lemma 4.1 and the occupation bound of Proposition 3.2. -/
theorem resolventStatement_of_fisher_occupation (hFOT : FukushimaDecompositionInput) (d : ℕ)
    (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (hFisher : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ,
        IsReducedLaplaceDensity Q.measure P origin_probability s rho →
        ∃ Drho : FieldPair d → Vec d,
          HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho ∧
          Integrable (fun w => euclideanNorm (Drho w)) (reducedReferenceLaw Q) ∧
          (∫⁻ w, ENNReal.ofReal
              (if rho w = 0 then 0 else dot (Drho w) ((w.1 0).mulVec (Drho w)) / rho w)
              ∂(reducedReferenceLaw Q)) ≤
            ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2))
    (hOcc : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
      ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ (P : QuenchedPathLaws d)
          (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
          IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
        ∀ G : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
          MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
        ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
          (∫⁻ z : FieldPair d × Path d,
              (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (reducedObservationAt t.toNNReal z)|)
            ∂(annealedCoordinateJoint Q.measure P origin_probability)) ≤
              ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) ∧
          ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
            (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
              ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q)) :
    ResolventStatement d hd Λ₀ r₀ := by
  have hDiv := divergenceStatement_of_fisher_occupation d hd Λ₀ r₀ hFisher hOcc
  have hOccS : OccupationStatement d hd Λ₀ r₀ := by
    intro hΛ hr
    obtain ⟨l₀, hl₀, H⟩ := hOcc d hd Λ₀ r₀ hΛ hr
    refine ⟨l₀, hl₀, fun l hl => ?_⟩
    obtain ⟨p₀, hp₀, H'⟩ := H l hl
    refine ⟨p₀, hp₀, fun p hp => ?_⟩
    obtain ⟨C, hC, H''⟩ := H' p hp
    refine ⟨C, hC, fun Q lam hl0 hl1 IQ P op hyp => ?_⟩
    obtain ⟨rfl, hGMP⟩ := hyp
    exact H'' Q lam hl0 hl1 P op hGMP
  exact resolvent_of_weak_divergence_occupation d hd Λ₀ r₀
    (weakResolventStep_of_fukushima hFOT d hd Λ₀ r₀ hDiv hOccS) hDiv hOccS

end EinsteinRelation.Entropy
