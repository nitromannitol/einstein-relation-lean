import EinsteinRelation.Correctors.ScalarResponse
import EinsteinRelation.Entropy.ResolventFromWeak
import EinsteinRelation.Mobility.ClockEstimateDischarge

/-! # The decomposition construction behind Proposition 6.1

Source: `paper/main.tex:978-997` (`scalar.decomposition`) and the response in Step 6
(`paper/main.tex:1086-1100`).

`DecompositionConstruction` is the existence part of the scalar decomposition. It has the
quantifier prefix of `EinsteinRelation.ScalarDecompositionTwin` (Proposition 6.1, restated over the
production twins in `EinsteinRelation/Mobility/ClockEstimateFromSteps.lean`). For every averaging
field `f` it supplies data `ψ, h, e, Dψ, E, P` with the localizations, the two generator equations
and the four `L^{2p}` bounds of the first conjunct of that twin, with one constant `C`. It adds two
localizations: `Dψ` and `f - e` are measurable for the localized σ-algebra of the ball `B_{C₀R}`.
The response bound `scalarResponse_of_decomposition` needs them for Lemma 4.3.

The glue theorems combine this construction with the three paper inputs of the response:
the Fisher bound of Lemma 4.1 (`FisherBoundStatement`), the resolvent bound of Lemma 4.3
(`EinsteinRelation.Entropy.ResolventStatement`) and the occupation bound of Proposition 3.2
(`EinsteinRelation.Entropy.OccupationStatement`). `scalarDecompositionTwin_of_construction` proves
`ScalarDecompositionTwin`, and `clockEstimateStep_of_construction` proves the clock estimate
`ClockEstimateStep` through `clockEstimateStep_of_scalarDecompositionTwin`. -/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

/-- The existence part of the scalar decomposition (Proposition 6.1, `paper/main.tex:978-997`),
with the quantifier prefix of `EinsteinRelation.ScalarDecompositionTwin`. The constants `C₀`,
`l₀`, `p₀` and `C` are chosen before the environment law `Q`, the averaging field `f` and the
scale `R`: `C₀` and `l₀` first, then `p₀`, then `C` after `M4p`. The data `ψ, h, e, Dψ, E, P`
satisfy the first conjunct of the twin (with the constant `C`) together with the localizations
of `Dψ` and of `f - e` on `B_{C₀R}`. -/
def DecompositionConstruction : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
  ∀ M4p : ℝ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ hQ : IsStationary (Carriers.reducedReferenceLaw Q),
  ∀ M : ℝ → ℝ, M (4 * p) = M4p →
  ∀ R : ℝ, 2 ≤ R → (∃ k : ℕ, R = 2 ^ k) →
  ∀ f : FieldPair d → ℝ, Carriers.IsScalarAveragingField Q M R f →
    ∃ (ψ h e : FieldPair d → ℝ) (Dψ E P : FieldPair d → Vec d),
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] ψ ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] h ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] e ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] E ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] P ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] Dψ ∧
      Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}]
        (fun ω => f ω - e ω) ∧
      SatisfiesReducedGeneratorEquation (Carriers.reducedReferenceLaw Q) hQ 0 ψ Dψ
        (fun ω => f ω - e ω) (fun ω => -(E ω)) (⟨0, by omega⟩ : Fin d) ∧
      HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ P
        (fun ω =>
          dot ((ω.1 (0 : Vec d)).mulVec (unitVector (⟨0, by omega⟩ : Fin d))) (Dψ ω) - h ω) ∧
      eLpNorm ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) +
          eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
            (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * R) ∧
      eLpNorm (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * Real.log (2 + R)) ∧
      eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) +
          eLpNorm h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal C ∧
      eLpNorm e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * R⁻¹)

/-- The Fisher bound of Lemma 4.1 (`entropy.fisher`, `paper/main.tex:518-524`), with the quantifier
prefix of the premise `hFisher` of `EinsteinRelation.Entropy.divergence_bound_of_fisher_occupation`.
Under the GMP conditioning of Lemma 4.1, every reduced Laplace density `ρ_s` has a weak horizontal
gradient `Drho`, which is integrable in its Euclidean norm and satisfies the bound on the weighted
form `dot (Drho) (a Drho) / ρ`. -/
def FisherBoundStatement : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (Carriers.reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
    IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
  ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ,
    Carriers.IsReducedLaplaceDensity Q.measure P origin_probability s rho →
    ∃ Drho : FieldPair d → Vec d,
      HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho ∧
      Integrable (fun w => euclideanNorm (Drho w)) (Carriers.reducedReferenceLaw Q) ∧
      (∫⁻ w, ENNReal.ofReal
          (if rho w = 0 then 0 else dot (Drho w) ((w.1 (0 : Vec d)).mulVec (Drho w)) / rho w)
          ∂(Carriers.reducedReferenceLaw Q)) ≤
        ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2)

/-- The gradient part of Lemma 4.1: under the GMP conditioning, every reduced Laplace density has
a weak horizontal gradient. This is the premise `hGrad` of `scalarResponse_of_decomposition`. -/
private theorem gradient_of_fisher {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (H41 : FisherBoundStatement) (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) :
    ∀ (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (P' : QuenchedPathLaws d)
      (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P' ω)),
      IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P') →
      ∀ (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ),
      Carriers.IsReducedLaplaceDensity Q.measure P' op s rho →
      ∃ Drho : FieldPair d → Vec d,
        HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho := by
  intro lam hl0 hl1 P' op hG s rho hrho
  obtain ⟨Drho, hW, -, -⟩ := H41 d hd Λ₀ r₀ Q hQ lam hl0 hl1 P' op hG s rho hrho
  exact ⟨Drho, hW⟩

/-- Proposition 6.1 over the production twins (`EinsteinRelation.ScalarDecompositionTwin`), from
the decomposition construction `hCons`, the Fisher bound `H41` of Lemma 4.1, the resolvent bound
`H43` of Lemma 4.3 and the occupation bound `H32` of Proposition 3.2.

The construction gives the data at a constant `C₁`. The resolvent constant `C_R` and the occupation
constant `C_O` are chosen at the scale `l` and the exponents `p` and `2p`, before `M4p`. The twin's
constant is `C = max C₁ ((C_R + 2 C_O) C₁)`: the data bounds hold at `C₁ ≤ C`, and the response
bound `(C_R + 2 C_O) C₁ (sR + λ + λ² R + R⁻¹)` is at most `C (sR + λ + λ² R + R⁻¹)`. -/
theorem scalarDecompositionTwin_of_construction (H41 : FisherBoundStatement)
    (H43 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      EinsteinRelation.Entropy.ResolventStatement d hd Λ₀ r₀)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      EinsteinRelation.Entropy.OccupationStatement d hd Λ₀ r₀)
    (hCons : DecompositionConstruction) : ScalarDecompositionTwin := by
  unfold ScalarDecompositionTwin
  intro d hd Λ₀ r₀ hΛ hr
  obtain ⟨C₀, hC₀, l₀c, hrc, hcons⟩ := hCons d hd Λ₀ r₀ hΛ hr
  obtain ⟨l₀R, -, hres⟩ := H43 d hd Λ₀ r₀
  obtain ⟨l₀O, -, hocc⟩ := H32 d hd Λ₀ r₀ hΛ hr
  have hcL : l₀c ≤ max (max l₀c l₀R) l₀O := le_trans (le_max_left l₀c l₀R) (le_max_left _ l₀O)
  have hRL : l₀R ≤ max (max l₀c l₀R) l₀O := le_trans (le_max_right l₀c l₀R) (le_max_left _ l₀O)
  have hOL : l₀O ≤ max (max l₀c l₀R) l₀O := le_max_right _ l₀O
  refine ⟨C₀, hC₀, max (max l₀c l₀R) l₀O, by linarith, fun l hl => ?_⟩
  obtain ⟨p₀c, hp₀c, hpc⟩ := hcons l (le_trans hcL hl)
  obtain ⟨p₀R, -, hpR⟩ := hres l (le_trans hRL hl)
  obtain ⟨p₀O, hp₀O, hpO⟩ := hocc l (le_trans hOL hl)
  have hpc0 : p₀c ≤ max (max p₀c p₀R) p₀O := le_trans (le_max_left p₀c p₀R) (le_max_left _ p₀O)
  have hpR0 : p₀R ≤ max (max p₀c p₀R) p₀O := le_trans (le_max_right p₀c p₀R) (le_max_left _ p₀O)
  have hpO0 : p₀O ≤ max (max p₀c p₀R) p₀O := le_max_right _ p₀O
  refine ⟨max (max p₀c p₀R) p₀O, by linarith, fun p hp => ?_⟩
  have hpc' : p₀c ≤ p := le_trans hpc0 hp
  have hpR' : p₀R ≤ p := le_trans hpR0 hp
  have hpO1 : p₀O ≤ p := le_trans hpO0 hp
  have hpO2 : p₀O ≤ 2 * p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨CR, hCR, hResP⟩ := hpR p hpR'
  obtain ⟨CO, hCO, hOccP⟩ := hpO (2 * p) hpO2
  intro M4p
  obtain ⟨C₁, hC₁, hdata⟩ := hpc p hpc' M4p
  obtain ⟨C, hC₁C, hCC⟩ : ∃ C : ℝ, C₁ ≤ C ∧ (CR + 2 * CO) * C₁ ≤ C :=
    ⟨max C₁ ((CR + 2 * CO) * C₁), le_max_left _ _, le_max_right _ _⟩
  refine ⟨C, le_trans hC₁ hC₁C, ?_⟩
  intro Q hQ M hM R hR hk f hf
  obtain ⟨ψ, h, e, Dψ, E, P, hψm, hhm, hem, hEm, hPm, hDψL, hfeL, hEq, hDiv, hψP, hDψb, hEh,
    heb⟩ := hdata Q hQ M hM R hR hk f hf
  have hR0 : 0 ≤ R := by linarith
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have hResAt : ResolventAtScale d hd Λ₀ r₀ l p CR := hResP
  have hOccAt : OccupationAtScale d hd Λ₀ r₀ l (2 * p) CO := fun _ _ => hOccP
  refine ⟨⟨ψ, h, e, Dψ, E, P, hψm, hhm, hem, hEm, hPm, hEq, hDiv, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans hψP (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC₁C hR0))
  · exact le_trans hDψb (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC₁C hlog))
  · exact le_trans hEh (ENNReal.ofReal_le_ofReal hC₁C)
  · exact le_trans heb
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC₁C (inv_nonneg.2 hR0)))
  · intro lam hl0 hl1 hCl Q' hprob P' op hyp s hs rho hrho
    have hsum : 0 ≤ s.1 * R + lam + lam ^ 2 * R + R⁻¹ :=
      add_nonneg (add_nonneg (add_nonneg (mul_nonneg s.2.le hR0) hl0.le)
        (mul_nonneg (sq_nonneg lam) hR0)) (inv_nonneg.2 hR0)
    have hresp := scalarResponse_of_decomposition hd hΛ hr Q hQ M C₀ l p C₁ R CR CO hC₀ hR hp1
      hC₁ hCR hCO f hf ψ h e Dψ E P hψm hhm hem hEm hPm hEq hDiv hψP hDψb hEh heb hDψL hfeL
      (gradient_of_fisher hd H41 Q hQ) hResAt hOccAt lam hl0 hl1 hCl Q' hprob P' op hyp s hs rho
      hrho
    exact ⟨hresp.1, hresp.2.trans (mul_le_mul_of_nonneg_right hCC hsum)⟩

/-- **Clock estimate from the scalar decomposition construction** (`paper/main.tex` 1188,
`eq.clock-estimate`). The internal step `ClockEstimateStep` follows from the decomposition
construction and the three inputs `H41`, `H43` and `H32` of
`scalarDecompositionTwin_of_construction`, through `clockEstimateStep_of_scalarDecompositionTwin`. -/
theorem clockEstimateStep_of_construction (H41 : FisherBoundStatement)
    (H43 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      EinsteinRelation.Entropy.ResolventStatement d hd Λ₀ r₀)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      EinsteinRelation.Entropy.OccupationStatement d hd Λ₀ r₀)
    (hCons : DecompositionConstruction) : ClockEstimateStep :=
  EinsteinRelation.clockEstimateStep_of_scalarDecompositionTwin
    (scalarDecompositionTwin_of_construction H41 H43 H32 hCons)

end EinsteinRelation.Correctors

end
