import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Carriers.ScalarAveragingTwin
import EinsteinRelation.Clock.CentredClockField
import EinsteinRelation.Clock.ResolventRateLimit
import EinsteinRelation.Density.LaplaceDensityAbel
import EinsteinRelation.Density.LaplaceDensityExistence
import EinsteinRelation.Density.LaplaceDensityIntegral
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Diffusion.GMPFamilyAPI
import EinsteinRelation.Mobility.MainSteps
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # The clock estimate from the scalar decomposition

Source: `paper/main.tex`, the clock subsection (lines 1153-1181). The clock estimate
`eq.clock-estimate` (line 1178) is `ClockEstimateStep` of `Mobility.MainSteps`. It follows from
three named inputs:

* `ScalarDecompositionTwin`: Proposition 6.1 (`scalar.decomposition`, lines 968-987), written over
  the production twins of the frozen carriers;
* `CentredClockAveragingStep`: the averaging-field bound for the centred clock density
  `f_R = μ - 𝔼μ` (lines 1155-1164);
* `ClockExpectationLimit`: the passage from the quenched clock rate to the time average of the
  expected clock density (lines 1170-1173).

The density limit `Density.tendsto_integral_mul_density` gives `𝔼[ρ_s g] → η` as `s ↓ 0` for the
clamped clock density `g`. The scalar decomposition bounds `|𝔼[ρ_s g] - 𝔼μ|` by
`C (s R + λ + λ² R + R⁻¹)`, and `Clock.clock_rate_of_resolvent` turns this into the linear bound.
The clamp at `K = sourceReducedBound Λ₀` makes the observable bounded everywhere; it agrees with
`μ = w.2 0` almost surely under the reduced law.
-/

open MeasureTheory Filter
open scoped NNReal Topology

noncomputable section

namespace EinsteinRelation

/-- Proposition 6.1 (`scalar.decomposition`, `paper/main.tex` 968-987), restated over the
production twins of the frozen carriers. The body is that of
`EinsteinRelation.Frozen.scalarDecompositionV2` (file `Frozen/ScalarDecompositionV2.lean`) with
these replacements: `reducedReferenceLaw` is `Carriers.reducedReferenceLaw`,
`IsScalarAveragingField` is `Carriers.IsScalarAveragingField`, and the argument
`I : CoordinatePathLawInput d hd` is replaced by its fields: a probability measure `Q'`, a
quenched kernel `P` and the origin-probability proof `op`. The predicate
`IsReducedLaplaceDensity I s rho` becomes `Carriers.IsReducedLaplaceDensity Q' P op s rho`. The
equality `I.Q = Q.measure` becomes `Q' = Q.measure`. The production predicates `IsStationary`,
`localSigma`, `IsGMPReducedOriginLaw`, `SatisfiesReducedGeneratorEquation` and
`HasWeakHorizontalDivergence` are used unchanged. -/
def ScalarDecompositionTwin : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
  ∀ M4p : ℝ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀,
  ∀ hQ : EinsteinRelation.IsStationary (Carriers.reducedReferenceLaw Q),
  ∀ M : ℝ → ℝ, M (4 * p) = M4p →
  ∀ R : ℝ, 2 ≤ R → (∃ k : ℕ, R = 2 ^ k) →
  ∀ f : FieldPair d → ℝ, Carriers.IsScalarAveragingField Q M R f →
    (∃ (ψ h e : FieldPair d → ℝ) (Dψ E P : FieldPair d → Vec d),
      Measurable[EinsteinRelation.localSigma
          {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] ψ ∧
      Measurable[EinsteinRelation.localSigma
          {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] h ∧
      Measurable[EinsteinRelation.localSigma
          {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] e ∧
      Measurable[EinsteinRelation.localSigma
          {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] E ∧
      Measurable[EinsteinRelation.localSigma
          {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] P ∧
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
        ENNReal.ofReal (C * R⁻¹)) ∧
    (∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1, C₀ * R ≤ l / (2 * lam) →
      ∀ Q' : Measure (FieldPair d), IsProbabilityMeasure Q' →
      ∀ (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q', IsProbabilityMeasure (originLaw P ω)),
        (Q' = Q.measure ∧
          IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P)) →
      ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
      ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity Q' P op s rho →
        Integrable (fun w => rho w * f w) (Carriers.reducedReferenceLaw Q) ∧
        |∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)| ≤
          C * (s.1 * R + lam + lam ^ 2 * R + R⁻¹))

/-- The averaging-field input for the centred clock density (`paper/main.tex` 1155-1164). For
every dimension `d ≥ 2` and every `Λ₀, r₀`, there is a family `M` of constants such that the
centred clock `Clock.centredClock Q = μ - 𝔼μ` satisfies `Carriers.IsScalarAveragingField` for
every positive scale `R`. -/
def CentredClockAveragingStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ M : ℝ → ℝ, (∀ m : ℝ, 0 ≤ M m) ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 0 < R →
      Carriers.IsScalarAveragingField Q M R (Clock.centredClock Q)

/-- The clamp of the clock density at the origin to `[-K, K]`. It is a bounded observable on
field pairs, so the density limit applies to it. Where the clock density is at most `K` in
absolute value, the clamp is inactive (`clampedClockAtOrigin_eq_of_abs_le`). -/
def clampedClockAtOrigin {d : ℕ} (K : ℝ) (w : FieldPair d) : ℝ :=
  max (-K) (min K (w.2 (0 : Vec d)))

/-- The clamped clock density at the origin is continuous on field pairs. -/
theorem continuous_clampedClockAtOrigin {d : ℕ} (K : ℝ) :
    Continuous (clampedClockAtOrigin (d := d) K) := by
  show Continuous fun w : FieldPair d => max (-K) (min K (w.2 (0 : Vec d)))
  exact continuous_const.max (continuous_const.min Clock.continuous_clockAtOrigin)

/-- The clamped clock density at the origin is measurable. -/
theorem measurable_clampedClockAtOrigin {d : ℕ} (K : ℝ) :
    Measurable (clampedClockAtOrigin (d := d) K) :=
  (continuous_clampedClockAtOrigin K).measurable

/-- The clamp takes values in `[-K, K]`, so it is bounded by `K` when `K ≥ 0`. -/
theorem abs_clampedClockAtOrigin_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K) (w : FieldPair d) :
    |clampedClockAtOrigin K w| ≤ K := by
  unfold clampedClockAtOrigin
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The clamp is inactive where the clock density at the origin is at most `K` in absolute
value. -/
theorem clampedClockAtOrigin_eq_of_abs_le {d : ℕ} {K : ℝ} {w : FieldPair d}
    (h : |w.2 (0 : Vec d)| ≤ K) : clampedClockAtOrigin K w = w.2 (0 : Vec d) := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold clampedClockAtOrigin
  rw [min_eq_right h2, max_eq_right h1]

/-- The density `ρ` of the reduced Laplace-time law is integrable for the reduced reference law.
Its total mass is finite, since the observed law is a probability measure. -/
private theorem integrable_of_isReducedLaplaceDensity {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ)
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P op s rho) :
    Integrable rho (Measure.map reduce Q.measure) := by
  unfold Carriers.IsReducedLaplaceDensity at hrho
  obtain ⟨hm, hnn, hdens⟩ := hrho
  haveI := laplaceDensity_isProbabilityMeasure_observed Q P op s
  have hmass : Carriers.reducedLaplaceObservedLaw Q.measure P op s Set.univ =
      ∫⁻ w, ENNReal.ofReal (rho w) ∂(Measure.map reduce Q.measure) := by
    rw [hdens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfin : ∫⁻ w, ENNReal.ofReal (rho w) ∂(Measure.map reduce Q.measure) ≠ ⊤ := by
    rw [← hmass]
    exact measure_ne_top _ _
  have hint := integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable hfin
  refine hint.congr (Filter.Eventually.of_forall fun w => ?_)
  exact ENNReal.toReal_ofReal (hnn w)

/-- The mean clock density `𝔼μ` is the integral of the clock at the origin under the reduced
reference law. -/
private theorem meanMu_eq_integral_reducedReferenceLaw {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    meanMu Q = ∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) := by
  have hcont : Continuous (fun w : FieldPair d => w.2 (0 : Vec d)) :=
    Clock.continuous_clockAtOrigin
  have hred : ∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) =
      ∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure := by
    unfold Carriers.reducedReferenceLaw
    exact integral_map Probability.measurable_reduce.aemeasurable hcont.aestronglyMeasurable
  exact hred.symm

/-- The centred clock splits the clock at the origin as `μ = f + 𝔼μ`. -/
private theorem mul_clockAtOrigin_eq {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (rho : FieldPair d → ℝ) (w : FieldPair d) :
    rho w * w.2 (0 : Vec d) = rho w * Clock.centredClock Q w +
      (∫ w', w'.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q)) * rho w := by
  unfold Clock.centredClock
  ring

/-- Under the reduced law, the clamped clock observable minus the mean clock has the integral of
`ρ f`, where `f = μ - 𝔼μ` is the centred clock. -/
private theorem integral_clampedClock_sub_meanMu {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (rho : FieldPair d → ℝ)
    (hint : Integrable rho (Carriers.reducedReferenceLaw Q))
    (hmass : ∫ w, rho w ∂(Carriers.reducedReferenceLaw Q) = 1)
    (hf : Integrable (fun w => rho w * Clock.centredClock Q w) (Carriers.reducedReferenceLaw Q)) :
    (∫ w, rho w * clampedClockAtOrigin (sourceReducedBound Λ₀) w
        ∂(Carriers.reducedReferenceLaw Q)) - meanMu Q =
      ∫ w, rho w * Clock.centredClock Q w ∂(Carriers.reducedReferenceLaw Q) := by
  have hclamp : ∫ w, rho w * clampedClockAtOrigin (sourceReducedBound Λ₀) w
      ∂(Carriers.reducedReferenceLaw Q) =
      ∫ w, rho w * w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) := by
    refine integral_congr_ae ?_
    filter_upwards [Clock.ae_abs_clockAtOrigin_le Q] with w hw
    exact congrArg (fun x => rho w * x) (clampedClockAtOrigin_eq_of_abs_le hw)
  have hsplit : ∫ w, rho w * w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) =
      ∫ w, (rho w * Clock.centredClock Q w +
        (∫ w', w'.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q)) * rho w)
        ∂(Carriers.reducedReferenceLaw Q) :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => mul_clockAtOrigin_eq Q rho w)
  have hsum : ∫ w, (rho w * Clock.centredClock Q w +
      (∫ w', w'.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q)) * rho w)
      ∂(Carriers.reducedReferenceLaw Q) =
      ∫ w, rho w * Clock.centredClock Q w ∂(Carriers.reducedReferenceLaw Q) +
        ∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q) := by
    rw [integral_add hf (hint.const_mul (∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q))),
      integral_const_mul, hmass, mul_one]
  rw [hclamp, hsplit, hsum, meanMu_eq_integral_reducedReferenceLaw Q]
  ring

/-- A bound on the centred integral `𝔼[ρ f]` transfers to the clamped density: the difference of
`𝔼[ρ g]` and `𝔼μ` is `𝔼[ρ f]`, with `g` the clamp of `μ`. -/
private theorem abs_clampedDensity_sub_meanMu_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ)
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P op s rho)
    (hf : Integrable (fun w => rho w * Clock.centredClock Q w) (Carriers.reducedReferenceLaw Q))
    {B : ℝ}
    (hB : |∫ w, rho w * Clock.centredClock Q w ∂(Carriers.reducedReferenceLaw Q)| ≤ B) :
    |(∫ w, rho w * clampedClockAtOrigin (sourceReducedBound Λ₀) w
        ∂(Carriers.reducedReferenceLaw Q)) - meanMu Q| ≤ B := by
  have hint := integrable_of_isReducedLaplaceDensity Q P op s rho hrho
  have hmass := Density.integral_density_eq_one Q.measure P op s rho hrho
  rw [integral_clampedClock_sub_meanMu Q rho hint hmass hf]
  exact hB

/-- The clock expectation limit (`paper/main.tex` 1170-1173). For the reduced GMP family at a force
`0 < lam ≤ 1`, if the quenched clock rates `t⁻¹ physicalPathClock` converge to `eta` for almost
every environment and almost every path, then the time averages `t⁻¹ ∫₀ᵗ E[g(ω_u)] du` of the
clamped clock density `g` converge to `eta`. The observable `g` is the clamp of `w ↦ w.2 0` to
`[-K, K]` with `K = sourceReducedBound Λ₀`. The origin-probability hypothesis `op` is a
proposition, so quantifying over it adds no content; it holds for the reduced origin law by
`isProbabilityMeasure_of_isGMPReducedOriginLaw`. -/
def ClockExpectationLimit : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d)
    (lam : ℝ), 0 < lam → lam ≤ 1 → IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω)) (eta : ℝ),
      (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
        Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 eta)) →
      Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t,
          Density.observationMean Q.measure (P' lam) op
            (clampedClockAtOrigin (sourceReducedBound Λ₀)) u) / t)
        atTop (𝓝 eta)

/-- The clock estimate for fixed `d`, `Λ₀`, `r₀` with `1 ≤ Λ₀` and `1 ≤ r₀`. The constants are
`C = C_p · (1 + l₀ / (2 C₀) + 4 C₀ / l₀)` and `lamStar = min 1 (l₀ / (4 C₀))`, where `C₀`, `l₀`
come from the scalar decomposition, `p₀` is its moment exponent, and `C_p` its constant at
`M(4 p₀)`. The scale `R` of the resolvent bound is chosen inside `Clock.clock_rate_of_resolvent`. -/
private theorem exists_clockEstimate_at (H61 : ScalarDecompositionTwin)
    (hAvg : CentredClockAveragingStep) (hExp : ClockExpectationLimit)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (hr₀ : 1 ≤ r₀) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
        IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
        ∀ lam : ℝ, 0 < lam → lam ≤ lamStar → ∀ eta : ℝ,
          (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' lam (0, ω)),
            Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 eta)) →
          |eta - meanMu Q| ≤ C * lam := by
  obtain ⟨C₀, hC₀, l₀, hr₀l, hH'⟩ := H61 d hd Λ₀ r₀ hΛ₀ hr₀
  have hl₀ : 0 < l₀ := by linarith
  have hC₀l : 0 < 4 * C₀ := by linarith
  obtain ⟨p₀, -, hp⟩ := hH' l₀ le_rfl
  obtain ⟨M, -, hM⟩ := hAvg d hd Λ₀ r₀
  obtain ⟨C, hC0, hHC⟩ := hp p₀ le_rfl (M (4 * p₀))
  refine ⟨C * (1 + l₀ / (2 * C₀) + 4 * C₀ / l₀), min 1 (l₀ / (4 * C₀)),
    lt_min one_pos (div_pos hl₀ hC₀l), min_le_left _ _, ?_⟩
  intro Q P' hGMP lam hl0 hlamle eta hae
  have hlam1 : lam ≤ 1 := hlamle.trans (min_le_left _ _)
  have hsmall : lam ≤ l₀ / (4 * C₀) := hlamle.trans (min_le_right _ _)
  have hGMPlam :=
    (isGMPReducedFamily_iff hd Q.ellipticity_parameter Q P').mp hGMP lam hl0.le hlam1
  have hop : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω) :=
    isProbabilityMeasure_of_isGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hlam1
      (originLaw (P' lam)) hGMPlam
  have hex : ∀ s : {r : ℝ // 0 < r}, ∃ rho : FieldPair d → ℝ,
      Carriers.IsReducedLaplaceDensity Q.measure (P' lam) hop s rho :=
    fun s => exists_reducedLaplaceDensity_of_gmp hd Q hl0 hlam1 (P' lam) hop hGMPlam s
  choose rho hrho using hex
  have hlim := hExp d hd Λ₀ r₀ Q P' lam hl0 hlam1 hGMP hop eta hae
  have hK : 0 ≤ sourceReducedBound Λ₀ := (Clock.sourceReducedBound_pos hΛ₀).le
  have hF_tend := Density.tendsto_integral_mul_density Q.measure (P' lam) hop rho hrho
    (clampedClockAtOrigin (sourceReducedBound Λ₀))
    (measurable_clampedClockAtOrigin (sourceReducedBound Λ₀))
    (abs_clampedClockAtOrigin_le hK) eta hlim
  have hF' : ∀ R : ℝ, 2 ≤ R → (∃ k : ℕ, R = 2 ^ k) → C₀ * R ≤ l₀ / (2 * lam) →
      l₀ / (4 * C₀ * lam) ≤ R → ∀ s : ℝ, 0 < s → s ≤ lam ^ 2 →
      |(if hs : 0 < s then ∫ w, rho ⟨s, hs⟩ w * clampedClockAtOrigin (sourceReducedBound Λ₀) w
          ∂(Carriers.reducedReferenceLaw Q) else 0) - meanMu Q| ≤
        C * (s * R + lam + lam ^ 2 * R + R⁻¹) := by
    intro R hR2 hRk hup _ s hs hsle
    have hRpos : 0 < R := by linarith
    have hHR := hHC Q (Clock.isStationary_reducedReferenceLaw Q) M rfl R hR2 hRk
      (Clock.centredClock Q) (hM Q R hRpos)
    have hb := hHR.2 lam hl0 hlam1 hup Q.measure Q.probability (P' lam) hop
      ⟨rfl, hGMPlam⟩ ⟨s, hs⟩ hsle (rho ⟨s, hs⟩) (hrho ⟨s, hs⟩)
    rw [dif_pos hs]
    exact abs_clampedDensity_sub_meanMu_le Q (P' lam) hop ⟨s, hs⟩ (rho ⟨s, hs⟩) (hrho ⟨s, hs⟩)
      hb.1 hb.2
  exact Clock.clock_rate_of_resolvent C₀ l₀ hC₀ hl₀ lam hl0 hsmall
    (fun s : ℝ => if hs : 0 < s then
      ∫ w, rho ⟨s, hs⟩ w * clampedClockAtOrigin (sourceReducedBound Λ₀) w
        ∂(Carriers.reducedReferenceLaw Q) else 0)
    (meanMu Q) eta C hC0 hF' hF_tend

/-- **Clock estimate from the scalar decomposition** (`paper/main.tex` 1178, `eq.clock-estimate`).
Assuming Proposition 6.1 over the production twins, the centred-clock averaging bound, and the
clock expectation limit, the internal step `ClockEstimateStep` holds. When `Λ₀ < 1` or `r₀ < 1`
no environment law exists, so the statement is vacuous there. -/
theorem clockEstimateStep_of_scalarDecomposition (H61 : ScalarDecompositionTwin)
    (hAvg : CentredClockAveragingStep) (hExp : ClockExpectationLimit) :
    ClockEstimateStep := by
  unfold ClockEstimateStep
  intro d hd Λ₀ r₀
  by_cases hΛ : 1 ≤ Λ₀ ∧ 1 ≤ r₀
  · exact exists_clockEstimate_at H61 hAvg hExp d hd Λ₀ r₀ hΛ.1 hΛ.2
  · refine ⟨0, 1, one_pos, le_rfl, fun Q => ?_⟩
    exact (hΛ ⟨Q.ellipticity_parameter, Q.range_parameter⟩).elim

end EinsteinRelation

end
