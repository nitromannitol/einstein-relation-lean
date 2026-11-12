import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.Probability.ValidAnnealedLawSupport
import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.CycleRewardFactorsDecoder
import EinsteinRelation.Regeneration.OccupationFromSteps
import EinsteinRelation.Regeneration.OccupationLaterIntervals
import EinsteinRelation.Regeneration.RenewalCarriers

/-!
# Proposition 3.2 from the renewal identity and the GMP coupling inputs

Source `paper/main.tex` lines 445–507 (`regen.occupation`). The two step inequalities of
`occupation_of_steps` are derived here. Step 2 comes from the renewal identity (Lemma 3.1,
`RenewalLemma31At`), the positive no-backtracking mass and the record factorization of the cycle
reward, which needs `G` measurable for the local σ-algebra of `B_{l/λ}`. Step 1 (the Girsanov
bound) is taken as the open input `FirstRewardStepFrozen`.

The composite `occupationTwin_of_steps` has the quantifier prefix of the frozen Proposition 3.2
statement `EinsteinRelation.regeneration_occupation`: `∃ l₀ ∀ l ≥ l₀ ∃ p₀ > 1 ∀ p ≥ p₀ ∃ C`, with
the coordinate path law input replaced by a quenched path law `P` and the origin probability
condition. The coupling existence and tail inputs are production twins of the frozen GMP
statements. The coupling existence gives a path law `P'` that need not be the given `P`, so the
bounds are transferred from `P'` to `P` through the origin laws, which agree almost everywhere by
path-law uniqueness of GMP Section 7 realizations.
-/

open MeasureTheory
open scoped NNReal ENNReal

open EinsteinRelation.External.GantertSection7Support (GantertFixedEnvironmentRealization)

noncomputable section

namespace EinsteinRelation

/-! ## Monotonicity of the step inequalities in the constant -/

/-- Step 1 is monotone in its constant: a larger `C` gives a weaker bound. -/
theorem firstRewardStep_mono {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l p C C' : ℝ) (hCC : C ≤ C') (K : Regeneration.CoupledQuenchedLaws d)
    (G : FieldPair d → ℝ) (h : FirstRewardStep hd Q lam l p C K G) :
    FirstRewardStep hd Q lam l p C' K G := by
  unfold FirstRewardStep at h ⊢
  refine h.trans ?_
  gcongr

/-- Step 2 is monotone in its constant: a larger `C` gives a weaker bound. -/
theorem laterIntervalsStep_mono {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l p C C' : ℝ) (hCC : C ≤ C') (K : Regeneration.CoupledQuenchedLaws d)
    (G : FieldPair d → ℝ) (h : LaterIntervalsStep hd Q lam l p C K G) :
    LaterIntervalsStep hd Q lam l p C' K G := by
  unfold LaterIntervalsStep at h ⊢
  intro k hk
  refine (h k hk).trans ?_
  gcongr

/-! ## Proposition 3.2 from the renewal identity and the first-reward step -/

/-- Proposition 3.2 (`regen.occupation`) for one coupling, from the renewal identity
(`RenewalLemma31At`), the positive no-backtracking mass `P̂(D) ≥ c`, the first-reward bound
(`FirstRewardStep`) and the local measurability of `G`. The constant is `max C (C / c)`, which
covers both `FirstRewardStep` with `C` and `LaterIntervalsStep` with `C / c`. -/
theorem occupation_of_renewal {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ p C c : ℝ) (hl : 0 < l) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hC : 0 ≤ C) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ hlam.le hlam1 P K)
    (hcoup : Regeneration.HasNoBacktrackingMass Q.measure (l / lam) c
      (Regeneration.Renewal.forceCoord hd) K)
    (l₀ : ℝ) (hl₀ : l₀ ≤ l) (H31 : RenewalLemma31At hd Q l₀)
    (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (G : FieldPair d → ℝ)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (hfirst : FirstRewardStep hd Q lam l p C K G) :
    ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
      (∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)) ≤
          ENNReal.ofReal (max C (C / c) * (T + (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) ∧
      ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity Q.measure P hP0 s rho →
        (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w|
            ∂(Carriers.reducedReferenceLaw Q)) ≤
          ENNReal.ofReal (max C (C / c) * (1 + s.1 * (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
  have hF := cycleRewardFactors_of_localMeasurable hd Q lam l hlam K G hG
  have hlater := laterIntervals_of_renewal hd Q lam l δ p C c hlam hlam1 hδ0 hδ1 hc P K hK hcoup
    l₀ hl₀ H31 G hfirst hF
  have hfirst' := firstRewardStep_mono hd Q lam l p C (max C (C / c)) (le_max_left _ _) K G hfirst
  have hlater' := laterIntervalsStep_mono hd Q lam l p (C / c) (max C (C / c))
    (le_max_right _ _) K G hlater
  exact occupation_of_steps hd hΛ₀ Q lam l δ p (max C (C / c)) hl hlam hlam1
    (hC.trans (le_max_left _ _)) P K hK hP0 G hG hfirst' hlater'

/-! ## Production twins of the frozen GMP and renewal inputs -/

/-- Lemma 3.1 (`regen.renewal`, `paper/main.tex` lines 348–354) in quantifier form: for every
`d ≥ 2` and environment constants there is a threshold `l₀` with `r₀ < 2 l₀` such that
`RenewalLemma31At` holds for every environment law at `l₀`. This is the production twin of
`EinsteinRelation.regeneration_renewal`. -/
def RenewalLemma31Input : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀, RenewalLemma31At hd Q l₀

/-- Existence of the GMP Section 7 coupling (Gantert–Mathieu–Piatnitski 2012, Proposition 5.4,
p. 23, with the measurable-coefficient extension of Section 7, p. 32). The success
probability `δ` is chosen after `l`,
and the realization `(P, K)` exists for every environment law and force. -/
def GMPCouplingExistsV2Input : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∃ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
        Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K

/-- The no-backtracking mass lower bound and the first regeneration tail (Gantert–Mathieu–Piatnitski
2012, Lemmas 5.7 and 5.8, pp. 25–26, and (5.20), p. 25, with Section 7, p. 32). The
constant `c` depends on
`d`, `Λ₀`, `r₀`, `δ` and `l`, and not on `λ`, the environment law, `P` or `K`. -/
def GMPCouplingTailsV2Input : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ c C : ℝ, 0 < c ∧
        ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ Q : EnvironmentLaw d Λ₀ r₀,
        ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
          Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K →
          Regeneration.HasNoBacktrackingMass Q.measure (l / lam) c
              (Regeneration.Renewal.forceCoord hd) K ∧
            Regeneration.HasFirstRegenerationTail Q.measure (Regeneration.Renewal.regenDelta lam)
              lam (l / lam) c C (Regeneration.Renewal.forceCoord hd) K

/-- Step 1 of Proposition 3.2 (`regen.first-reward`, `paper/main.tex` lines 473–480), the Girsanov
step, with the quantifier prefix of Proposition 3.2: `∃ l₀ ∀ l ≥ l₀`, then for every success
probability `δ ∈ (0, 1)` of the coupling, `∃ p₀ > 1 ∀ p ≥ p₀ ∃ C`, uniform in the environment
law, the force `λ ∈ (0, 1]`, the realization `(P, K)` and `G`. The coupling is required to satisfy
`IsGMPCouplingV2`, and `G` is measurable for the local σ-algebra of `B_{l/λ}` with
`G ∈ L^p(Q)`. This open input is the Girsanov step (Step 1) and is not proved here. -/
def FirstRewardStepFrozen : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1)
        (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
        Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ hl0.le hl1 P K →
        ∀ G : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
          MemLp G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) →
          FirstRewardStep hd Q lam l p C K G

/-- Path-law uniqueness of GMP Section 7 realizations: two fixed-environment realizations of the
same zero-potential or physical pair, with the same force, have the same path law. -/
def RealizationPathLawUniqueInput : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d) (hω : IsRegular Λ₀ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1),
    r.pathLaw = r'.pathLaw

/-! ## Transfer between coupled path laws with the same origin law -/

/-- Two coupled path laws with reduced origin laws have almost everywhere equal origin laws, by
path-law uniqueness of the GMP realizations of the zero-potential pair. -/
theorem originLaw_ae_eq_of_reduced {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (hU : RealizationPathLawUniqueInput) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1) (P P' : QuenchedPathLaws d)
    (hP : IsGMPReducedOriginLaw hd hΛ₀ Q lam h0 h1 (originLaw P))
    (hP' : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P') :
    ∀ᵐ ω ∂Q.measure, originLaw P ω = originLaw P' ω := by
  unfold IsGMPReducedOriginLaw at hP
  unfold IsGMPReducedKernel at hP'
  filter_upwards [hP, hP'] with ω hω hω'
  obtain ⟨hω1, r, hr⟩ := hω
  obtain ⟨_hω2, r', hr'⟩ := hω'
  have heq := hU hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
    (zeroPotentialReducedPair ω) hω1 lam h0 h1 r r'
  calc originLaw P ω = r.pathLaw 0 := hr
    _ = r'.pathLaw 0 := by rw [heq]
    _ = P' (0, ω) := (hr' 0).symm
    _ = originLaw P' ω := (originLaw_apply P' ω).symm

/-- Kernels that agree almost everywhere give equal annealed joint measures. The comparison goes
through the integrals of measurable test functions, because the subtype of probability fibres
depends on the kernel. -/
theorem annealedJoint_congr_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) [IsProbabilityMeasure Q] (K K' : ProbabilityTheory.Kernel α β)
    (hK : ∀ᵐ a ∂Q, IsProbabilityMeasure (K a)) (hK' : ∀ᵐ a ∂Q, IsProbabilityMeasure (K' a))
    (h : ∀ᵐ a ∂Q, K a = K' a) :
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers Q K hK =
      Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers Q K' hK' := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral Q K hK F hF,
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral Q K' hK' F hF]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with a ha
  simp only [ha]

/-- The annealed coordinate joint depends on the quenched path law only through its origin law. -/
theorem annealedCoordinateJoint_congr {d : ℕ} (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (P P' : QuenchedPathLaws d) (hP0 : ∀ᵐ ω ∂μ, IsProbabilityMeasure (originLaw P ω))
    (hP0' : ∀ᵐ ω ∂μ, IsProbabilityMeasure (originLaw P' ω))
    (h : ∀ᵐ ω ∂μ, originLaw P ω = originLaw P' ω) :
    Carriers.annealedCoordinateJoint μ P hP0 = Carriers.annealedCoordinateJoint μ P' hP0' :=
  annealedJoint_congr_of_ae μ (originLaw P) (originLaw P') hP0 hP0' h

/-- The reduced Laplace density predicate transfers along an equality of annealed joints. -/
theorem isReducedLaplaceDensity_congr {d : ℕ} (μ : Measure (FieldPair d))
    (P P' : QuenchedPathLaws d) (hP0 : ∀ᵐ ω ∂μ, IsProbabilityMeasure (originLaw P ω))
    (hP0' : ∀ᵐ ω ∂μ, IsProbabilityMeasure (originLaw P' ω))
    (hJ : Carriers.annealedCoordinateJoint μ P hP0 = Carriers.annealedCoordinateJoint μ P' hP0')
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ)
    (h : Carriers.IsReducedLaplaceDensity μ P hP0 s rho) :
    Carriers.IsReducedLaplaceDensity μ P' hP0' s rho := by
  unfold Carriers.IsReducedLaplaceDensity at h ⊢
  have he : Carriers.reducedLaplaceObservedLaw μ P' hP0' s =
      Carriers.reducedLaplaceObservedLaw μ P hP0 s := by
    unfold Carriers.reducedLaplaceObservedLaw
    rw [hJ]
  exact ⟨h.1, h.2.1, he.trans h.2.2⟩

/-! ## The composite Proposition 3.2 -/

/-- Proposition 3.2 (`regen.occupation`, `paper/main.tex` lines 445–507), the twin of the frozen
statement `EinsteinRelation.regeneration_occupation` in production form. It is derived from:

* `hR`: Lemma 3.1 in quantifier form (`RenewalLemma31Input`);
* `hE`, `hTail`: the GMP coupling existence and the no-backtracking and first-regeneration tails;
* `hS`: the Girsanov step `FirstRewardStepFrozen` (Step 1), an open input;
* `hU`: path-law uniqueness of GMP realizations, which identifies the origin laws of the given
  path law `P` and of the coupled path law `P'` from the existence input.

The constant is `max C (C / c)`, where `C` is the step constant and `c` the no-backtracking mass. -/
theorem occupationTwin_of_steps
    (hR : RenewalLemma31Input) (hE : GMPCouplingExistsV2Input)
    (hTail : GMPCouplingTailsV2Input) (hS : FirstRewardStepFrozen)
    (hU : RealizationPathLawUniqueInput) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (hr₀ : 1 ≤ r₀),
      ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1)
          (P : QuenchedPathLaws d) (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
          IsGMPReducedOriginLaw hd hΛ₀ Q lam hl0.le hl1 (originLaw P) →
          ∀ G : FieldPair d → ℝ,
            Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
            MemLp G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) →
            ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
              (∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T,
                  ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
                ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)) ≤
                  ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
                    eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) ∧
              ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity Q.measure P hP0 s rho →
                (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w|
                    ∂(Carriers.reducedReferenceLaw Q)) ≤
                  ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
                    eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
  intro d hd Λ₀ r₀ hΛ₀ hr₀
  obtain ⟨l₁, hl₁, hR'⟩ := hR d hd Λ₀ r₀
  obtain ⟨l₂, -, hE'⟩ := hE d hd Λ₀ r₀
  obtain ⟨l₃, -, hTail'⟩ := hTail d hd Λ₀ r₀
  obtain ⟨l₄, -, hS'⟩ := hS d hd Λ₀ r₀
  refine ⟨max (max l₁ l₂) (max l₃ l₄), ?_, ?_⟩
  · have hM₁ : l₁ ≤ max (max l₁ l₂) (max l₃ l₄) := (le_max_left l₁ l₂).trans (le_max_left _ _)
    linarith
  intro l hl
  have hM₁ : l₁ ≤ l := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hl
  have hM₂ : l₂ ≤ l := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hl
  have hM₃ : l₃ ≤ l := le_trans (le_trans (le_max_left l₃ l₄) (le_max_right _ _)) hl
  have hM₄ : l₄ ≤ l := le_trans (le_trans (le_max_right l₃ l₄) (le_max_right _ _)) hl
  have hl0' : 0 < l := by linarith
  obtain ⟨δ, hδ0, hδ1, hE''⟩ := hE' l hM₂
  obtain ⟨c, _, hc, hTail''⟩ := hTail' l hM₃ δ hδ0 hδ1
  obtain ⟨p₀, hp₀, hS''⟩ := hS' l hM₄ δ hδ0 hδ1
  refine ⟨p₀, hp₀, fun p hp => ?_⟩
  obtain ⟨C, hC0, hSt⟩ := hS'' p hp
  refine ⟨max C (C / c), hC0.trans (le_max_left _ _),
    fun Q lam hl0 hl1 P hP0 hPorig G hG hMem => ?_⟩
  intro T hTpos s
  obtain ⟨P', K', hK'⟩ := hE'' Q lam hl0 hl1
  obtain ⟨hcoup, -⟩ := hTail'' lam hl0 hl1 Q P' K' hK'
  have hPorig' : IsGMPReducedKernel hd hΛ₀ Q lam hl0.le hl1 P' := hK'.2.2.1
  have hU' : ∀ᵐ ω ∂Q.measure, originLaw P ω = originLaw P' ω :=
    originLaw_ae_eq_of_reduced hd hΛ₀ hU Q lam hl0.le hl1 P P' hPorig hPorig'
  have hP0' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P' ω) := by
    filter_upwards [hP0, hU'] with ω h1 h2
    rw [← h2]
    exact h1
  have hJ := annealedCoordinateJoint_congr Q.measure P P' hP0 hP0' hU'
  have hstep := hSt Q lam hl0 hl1 P' K' hK' G hG hMem
  have hocc := occupation_of_renewal hd hΛ₀ Q lam l δ p C c hl0' hl0 hl1 hC0 hc hδ0 hδ1 P' K' hK'
    hcoup l₁ hM₁ (hR' Q) hP0' G hG hstep
  obtain ⟨hTime, hDen⟩ := hocc T hTpos s
  refine ⟨?_, fun rho hrho => ?_⟩
  · rw [hJ]
    exact hTime
  · exact hDen rho (isReducedLaplaceDensity_congr Q.measure P P' hP0 hP0' hJ s rho hrho)

end EinsteinRelation

end
