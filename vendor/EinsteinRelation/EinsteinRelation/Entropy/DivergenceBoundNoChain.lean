import EinsteinRelation.Entropy.DensityZeroSetGradient
import EinsteinRelation.Entropy.DivergenceIdentity
import EinsteinRelation.Calculus.WeakChainRule
import EinsteinRelation.Correctors.HorizontalMollifierBounds

/-!
# Lemma 4.2 without the chain-rule premise, and the regularization reduction

Source: `paper/main.tex` lines 619–638 (`entropy.divergence`).

## First assertion, without the chain-rule premise

`divergence_bound_of_fisher_occupation'` takes the weak horizontal chain rule for the truncation
profiles as a premise. `EinsteinRelation.Calculus.hasWeakChainRule_truncProfile` proves that rule
for every stationary probability law, so `divergence_bound_of_fisher_occupation''` keeps only the
Fisher bound of Lemma 4.1 and the occupation bound of Proposition 3.2 as paper inputs.

## Second assertion: reduction of the regularization

`HorizontalSmoothApproximation` (`Entropy/DivergenceIdentity.lean`) asks for horizontally smooth
approximants `T n i` of the components of `F`, with horizontal derivatives `D n i`, such that the
residuals `h - ∑ᵢ D n i` converge to zero in `L^p` and the differences `F - T n` converge in
`L^{2p}`. `horizontalSmoothApproximation_of_horizontalTests` shows that the interface follows from
bounded orbit-core fields `Φ n` (the class `IsHorizontalTest`) with the approximation properties
stated there. Those properties are the remaining analytic input, described at the end of the file.
-/

open MeasureTheory Filter
open scoped Topology
open EinsteinRelation.Carriers

namespace EinsteinRelation.Entropy

/-! ### The first assertion without the chain-rule premise -/

/-- The weak horizontal chain rule for the truncation profiles on every reduced reference law,
from the proved chain rule for `C¹` profiles with bounded derivative. -/
theorem hasWeakChainRule_truncProfile_reduced {d : ℕ} {Λ₀ r₀ : ℝ} :
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (reducedReferenceLaw Q))
      (l : ℝ), 0 ≤ l → HasWeakChainRule (reducedReferenceLaw Q) hQ (truncProfile l) :=
  fun Q hQ l hl => EinsteinRelation.Calculus.hasWeakChainRule_truncProfile
    (reducedReferenceLaw Q) hQ hl

/-- Lemma 4.2, first assertion (`paper/main.tex:619–633`), conditional only on the Fisher bound of
Lemma 4.1 (`hFisher`) and the occupation bound of Proposition 3.2 (`hOcc`). The weak chain rule for
the truncation profiles is proved, so the premise `hchain` of
`divergence_bound_of_fisher_occupation'` is discharged, and the zero-set premise `hzero` is
derived from it. The conclusion is that of `divergence_bound_of_fisher_occupation'`. -/
theorem divergence_bound_of_fisher_occupation'' (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
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
    ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
    ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
      ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
      ∀ Drho : FieldPair d → Vec d,
        HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
      ∀ F : FieldPair d → Vec d,
        Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] F →
        MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
          (reducedReferenceLaw Q) →
        Integrable (fun w => dot (Drho w) (F w)) (reducedReferenceLaw Q) ∧
          (ENNReal.ofReal (abs (∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q))) ≤
            ENNReal.ofReal (C * lam) *
              eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
                (reducedReferenceLaw Q)) :=
  divergence_bound_of_fisher_occupation' d hd Λ₀ r₀ hFisher hOcc hasWeakChainRule_truncProfile_reduced

/-! ### The regularization reduced to bounded orbit-core approximants -/

/-- `HorizontalSmoothApproximation` follows from a sequence of bounded orbit-core fields
`Φ n : FieldPair d → Vec d`, whose components are `IsHorizontalTest`, provided that:

* `F - Φ n` is `localSigma U`-measurable up to null sets (`hloc`), and `|F - Φ n|` is in `L^{2p}`
  with norms tending to zero (`hmem`, `hconv`);
* the residual `h - ∑ᵢ D_i (Φ n · i)` is `localSigma U`-measurable up to null sets (`hresloc`),
  is in `L^p` (`hresmem`), and tends to zero in `L^p` (`hresconv`), where `D_i` is the literal
  horizontal derivative.

The approximants of the interface are the `L²(μ)` classes of the components `Φ n · i` and of their
horizontal derivatives, which exist by `IsHorizontalTest.isHorizontallySmoothTest` and
`IsHorizontalTest.hasHorizontalLpDerivative_toLp`. The listed properties are the analytic remainder. -/
theorem horizontalSmoothApproximation_of_horizontalTests {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) {U : Set (Vec d)} {p : ℝ}
    {F : FieldPair d → Vec d} {h : FieldPair d → ℝ} {Φ : ℕ → FieldPair d → Vec d}
    (hΦ : ∀ n i, IsHorizontalTest (fun ω => Φ n ω i))
    (hloc : ∀ n, ∃ G : FieldPair d → Vec d, Measurable[localSigma U] G ∧
      (fun ω => F ω - Φ n ω) =ᵐ[μ] G)
    (hmem : ∀ n, MemLp (fun ω => euclideanNorm (F ω - Φ n ω)) (ENNReal.ofReal (2 * p)) μ)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => euclideanNorm (F ω - Φ n ω))
      (ENNReal.ofReal (2 * p)) μ) atTop (𝓝 0))
    (hresloc : ∀ n, ∃ g : FieldPair d → ℝ, Measurable[localSigma U] g ∧
      (fun ω => h ω - ∑ i, horizontalDerivative i (fun ω => Φ n ω i) ω) =ᵐ[μ] g)
    (hresmem : ∀ n, MemLp (fun ω => h ω - ∑ i, horizontalDerivative i (fun ω => Φ n ω i) ω)
      (ENNReal.ofReal p) μ)
    (hresconv : Tendsto (fun n => eLpNorm
      (fun ω => h ω - ∑ i, horizontalDerivative i (fun ω => Φ n ω i) ω) (ENNReal.ofReal p) μ)
      atTop (𝓝 0)) :
    HorizontalSmoothApproximation μ hμ U p F h := by
  have key : ∀ n i, ∃ T D : Lp ℝ 2 μ, IsHorizontallySmoothTest μ hμ T ∧
      HasHorizontalLpDerivative μ hμ i T D ∧
      (⇑T =ᵐ[μ] fun ω => Φ n ω i) ∧
      (⇑D =ᵐ[μ] fun ω => horizontalDerivative i (fun ω => Φ n ω i) ω) := by
    intro n i
    refine ⟨((hΦ n i).memLp μ 2).toLp _, ((hΦ n i).memLp_derivative μ 2 i).toLp _,
      ?_, ?_, ?_, ?_⟩
    · exact (hΦ n i).isHorizontallySmoothTest μ hμ
    · exact (hΦ n i).hasHorizontalLpDerivative_toLp μ hμ i
    · exact ((hΦ n i).memLp μ 2).coeFn_toLp
    · exact ((hΦ n i).memLp_derivative μ 2 i).coeFn_toLp
  choose T D hsmooth hderiv hTae hDae using key
  unfold HorizontalSmoothApproximation
  have hTae' : ∀ n, ∀ᵐ ω ∂μ, ∀ i, (T n i) ω = Φ n ω i :=
    fun n => ae_all_iff.2 fun i => hTae n i
  have hDae' : ∀ n, ∀ᵐ ω ∂μ, ∀ i, (D n i) ω = horizontalDerivative i (fun ω => Φ n ω i) ω :=
    fun n => ae_all_iff.2 fun i => hDae n i
  -- The vector differences and their norms agree almost everywhere with those of `Φ`.
  have hvec : ∀ n, ∀ᵐ ω ∂μ, (fun i => F ω i - (T n i) ω) = F ω - Φ n ω := by
    intro n
    filter_upwards [hTae' n] with ω hω
    funext i
    simp only [hω i, Pi.sub_apply]
  have hnorm : ∀ n, (fun ω => euclideanNorm (fun i => F ω i - (T n i) ω)) =ᵐ[μ]
      (fun ω => euclideanNorm (F ω - Φ n ω)) := by
    intro n
    filter_upwards [hvec n] with ω hω
    exact congrArg euclideanNorm hω
  have hresD : ∀ n, (fun ω => h ω - ∑ i, (D n i) ω) =ᵐ[μ]
      (fun ω => h ω - ∑ i, horizontalDerivative i (fun ω => Φ n ω i) ω) := by
    intro n
    filter_upwards [hDae' n] with ω hω
    simp only [hω]
  refine ⟨T, D, fun n i => ⟨hsmooth n i, hderiv n i⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨G, hG, hGae⟩ := hloc n
    refine ⟨G, hG, ?_⟩
    filter_upwards [hvec n, hGae] with ω hωv hω
    exact hωv.trans hω
  · exact fun n => MemLp.ae_eq (hnorm n).symm (hmem n)
  · exact Filter.Tendsto.congr (fun n => (eLpNorm_congr_ae (hnorm n)).symm) hconv
  · intro n
    obtain ⟨g, hg, hgae⟩ := hresloc n
    exact ⟨g, hg, (hresD n).trans hgae⟩
  · exact fun n => MemLp.ae_eq (hresD n).symm (hresmem n)
  · exact Filter.Tendsto.congr (fun n => (eLpNorm_congr_ae (hresD n)).symm) hresconv

/-! ### Admissible approximants for bounded fields -/

/-- For a bounded measurable field, each component of its horizontal smoothing by a smooth
compactly supported kernel `ζ` is an orbit-core test. These mollified components are the candidates
for `Φ n` in `horizontalSmoothApproximation_of_horizontalTests` when `F` is bounded. -/
theorem isHorizontalTest_mollify_component {d : ℕ} {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    {F : FieldPair d → Vec d} (hF : Measurable F) {M : ℝ} (hM : ∀ ω i, |F ω i| ≤ M)
    (i : Fin d) : IsHorizontalTest (fun ω => horizontalMollify ζ (fun ω => F ω i) ω) := by
  have hFi : Measurable (fun ω => F ω i) := (measurable_pi_apply i).comp hF
  exact Correctors.isHorizontalTest_horizontalMollify ζ hζ hζc (fun ω => F ω i) hFi
    ⟨M, fun ω => hM ω i⟩

/-! ### Remaining input for `HorizontalSmoothApproximation`

`horizontalSmoothApproximation_of_horizontalTests` leaves the following open. This file does not
prove them.

1. Localization: for `F` localized on a smaller ball `U₀` (as in `main.tex` Lemma 4.2, where `F`
   depends only on `B_{l/(2λ)}`), the mollified components must be `localSigma U`-measurable up to
   null sets, with `U` containing the `ε`-neighbourhood of `U₀`. The interface requires this:
   `F - Φ n` must be `U`-local, so `F` is `U`-local up to a horizontally smooth part.
2. `L^{2p}` convergence of the mollified components to `F`, from the horizontal mollifier
   convergence `Calculus.tendsto_eLpNorm_horizontalMollify_sub` and
   `Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier`, applied componentwise.
3. The divergence identity `∑ᵢ D_i (S_ε Fᵢ) = S_ε h` almost everywhere, for bounded `F` with weak
   divergence `h`. `Correctors.horizontalMollify_horizontalDerivative_formula` gives the derivative
   of each component. The identity then follows by testing against bounded cores of the form
   `S_ε G`, using stationarity of `μ` and `L¹` uniqueness of the cores
   (`eq_zero_of_horizontalCore_pairing_eq_zero_l1`).
4. `L^p` convergence `S_ε h → h`, from the same mollifier convergence lemmas applied to `h`.

For unbounded `F`, the paper's truncation step (`main.tex` 634–638) is not justified as written.
Truncating the components with `ψ_M` gives divergence `∑ᵢ ψ_M'(Fᵢ) ∂ᵢFᵢ`, which differs from
`h = ∑ᵢ ∂ᵢFᵢ` by `∑ᵢ (1 - ψ_M'(Fᵢ)) ∂ᵢFᵢ`. The hypotheses control only the sum `∑ᵢ ∂ᵢFᵢ`, not the
individual `∂ᵢFᵢ`, so this difference need not tend to zero in `L^p`. Bounded orbit-core fields `Φ n`
with the properties above are therefore not yet constructed for unbounded `F`. -/

end EinsteinRelation.Entropy
