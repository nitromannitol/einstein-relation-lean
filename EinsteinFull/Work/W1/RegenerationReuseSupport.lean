import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.CorrectedHalfSpaceIndependence

/-!
# Literal regeneration objects and the deterministic factorization ingredients

The trial time, future record and conditioned law used in the frozen surface
are the blueprint's literal objects. The deterministic-slice decomposition,
fresh-bit mass and uniform-endpoint formula below require no kernel-locality
input. Joint finite range proves the independence step once local versions
are available. No renewal marginal or local version of a kernel is assumed
or asserted in this module.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull

open EinsteinRelation

/-- The actual first time is the infimum over successful trial starts. -/
theorem regenerationTime_one_eq_first {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (z : Regeneration.CoupledSample d) :
    regenerationTime hd lam l 1 z =
      Regeneration.firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) z (Regeneration.Renewal.forceCoord hd) :=
  Regeneration.regenerationTime_one _ _ _ _ _

/-- Equality of the complete records, retaining both reduced fields and coins. -/
theorem regenerationRecord_eq_iteratedRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (k : ℕ) :
    regenerationRecord hd lam l k =
      Regeneration.iteratedRecord (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) (Regeneration.Renewal.forceCoord hd) k := rfl

/-- The literal times are measurable even when they are infinite. -/
theorem measurable_regenerationTime {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ) :
    Measurable (regenerationTime hd lam l k) :=
  Regeneration.measurable_regenerationTime _ _ _ _ _

/-- The complete restricted future is measurable, including the infinite-time fallback. -/
theorem measurable_regenerationRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ) :
    Measurable (regenerationRecord hd lam l k) :=
  Regeneration.measurable_cycleRecord hd lam l k

/-- The source event D is measurable in the environment/path/coin product. -/
theorem measurableSet_regenerationNoReturn {d : ℕ} (hd : 2 ≤ d) (R : ℝ) :
    MeasurableSet (regenerationNoReturn hd R) :=
  (Regeneration.measurableSet_NoBacktracking R (Regeneration.Renewal.forceCoord hd)).preimage
    measurable_snd.fst

/-- The actual conditioned measure is exactly the blueprint conditional measure. -/
theorem regenerationConditionedLaw_eq_cond {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) :
    regenerationConditionedLaw hd Q lam l K hK hD =
      ProbabilityTheory.cond (Regeneration.annealedCoupledLaw Q.measure K)
        {p | Regeneration.NoBacktracking (l / lam) p.2.1
          (Regeneration.Renewal.forceCoord hd)} := rfl

/-- Conditioning preserves all annealed almost-everywhere identities. -/
theorem regenerationConditionedLaw_absolutelyContinuous {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) :
    regenerationConditionedLaw hd Q lam l K hK hD ≪
      Regeneration.annealedCoupledLaw Q.measure K :=
  ProbabilityTheory.cond_absolutelyContinuous

/-- The lattice masses are computed on the same first-trial slices as the blueprint. -/
theorem regenerationLatticeMass_eq_first_slice {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (n : ℕ) :
    regenerationLatticeMass hd Q lam l K hK hD n =
      (regenerationConditionedLaw hd Q lam l K hK hD).real {p |
        Regeneration.firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) p.2 (Regeneration.Renewal.forceCoord hd) =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} := by
  unfold regenerationLatticeMass
  simp only [regenerationTime_one_eq_first]

/-- The explicit prebridge event has the exact deterministic-time history sigma algebra. -/
theorem measurableSet_regeneration_prebridge {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (h₀ : 0 < lam) (hl : 0 < l) (m : ℕ) :
    MeasurableSet[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m]
      (Regeneration.forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) (Regeneration.Renewal.forceCoord hd) m) :=
  Regeneration.measurableSet_forcedBitTrialEvent_finiteHistory _
    (Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀)))
    _ _ (div_pos hl h₀) _ _

/-- The actual slice splits into the prebridge event, the last coin, and shifted D. -/
theorem regenerationTime_slice_iff {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (h₀ : 0 < lam) (m : ℕ) (z : Regeneration.CoupledSample d) :
    regenerationTime hd lam l 1 z =
        ((((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) ↔
      z ∈ Regeneration.forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) (Regeneration.Renewal.forceCoord hd) m ∧
        z.2 m = true ∧ Regeneration.NoBacktracking (l / lam)
          (Regeneration.pathTimeShift z.1
            (((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
          (Regeneration.Renewal.forceCoord hd) := by
  rw [regenerationTime_one_eq_first]
  exact Regeneration.firstRegenerationTime_eq_iff_forcedBitTrialEvent _
    (Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))) _ _ _ _ _

/-- Freshness applies to the literal prebridge event; no independence is added as a premise. -/
theorem regeneration_prebridge_lastBit_mass {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l) (hδ : 0 ≤ δ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K) (m : ℕ) :
    Regeneration.annealedCoupledLaw Q.measure K
      {p | p.2 ∈ Regeneration.forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) (Regeneration.Renewal.forceCoord hd) m ∧ p.2.2 m = true} =
      ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q.measure K
        {p | p.2 ∈ Regeneration.forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) (Regeneration.Renewal.forceCoord hd) m} :=
  Regeneration.measure_annealed_forcedBitTrialEvent_lastBit Q.measure K hK.1 _
    (Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))) δ hδ hK.2.2.2.1
    lam (l / lam) (div_pos hl h₀) _ m

/-- The paper's unscaled separation implies the actual scaled half-space gap. -/
theorem regeneration_scaled_gap (r₀ lam l : ℝ) (h₀ : 0 < lam)
    (h₁ : lam ≤ 1) (hl : 0 < l) (hsep : r₀ < 2 * l) :
    r₀ < 2 * (l / lam) := by
  have hscale : l ≤ l / lam := (le_div_iff₀ h₀).mpr (mul_le_of_le_one_right hl.le h₁)
  exact hsep.trans_le (mul_le_mul_of_nonneg_left hscale (by norm_num))

/-- Joint finite range gives the source past/future independence, at every endpoint. -/
theorem indep_regeneration_halfSpaces {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l) (hsep : r₀ < 2 * l) (y : Vec d) :
    ProbabilityTheory.Indep
      (localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
        y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)})
      (localSigma {x : Vec d | y (Regeneration.Renewal.forceCoord hd) - 2 * (l / lam) ≤
        x (Regeneration.Renewal.forceCoord hd)}) Q.measure :=
  Regeneration.indep_corrected_halfSpaces Q _ _ _
    (regeneration_scaled_gap r₀ lam l h₀ h₁ hl hsep)

/-- The original ball observable belongs to the past sigma algebra at every admissible endpoint. -/
theorem measurable_regeneration_initial_in_past {d : ℕ} (hd : 2 ≤ d)
    (lam l : ℝ) (h₀ : 0 < lam) (hl : 0 < l) (y : Vec d)
    (hy : 10 * (l / lam) ≤ y (Regeneration.Renewal.forceCoord hd))
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F) :
    Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] F := by
  apply hF.mono (Probability.localSigma_mono ?_) le_rfl
  intro x hx
  have hcoord := (le_abs_self (x (Regeneration.Renewal.forceCoord hd))).trans
    (Regeneration.coordinate_abs_le_euclideanNorm x (Regeneration.Renewal.forceCoord hd))
  have hR := div_pos hl h₀
  change x (Regeneration.Renewal.forceCoord hd) ≤ _
  change euclideanNorm x < l / lam at hx
  linarith

/-- Actual joint finite range factors a.e. local versions of the two environment kernels. -/
theorem integral_regeneration_local_versions_mul {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l) (hsep : r₀ < 2 * l) (y : Vec d)
    (A B A' B' : FieldPair d → ℝ)
    (hA : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A')
    (hB : Measurable[localSigma {x : Vec d | y (Regeneration.Renewal.forceCoord hd) -
      2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}] B')
    (hAe : A =ᵐ[Q.measure] A') (hBe : B =ᵐ[Q.measure] B') :
    (∫ ω, A ω * B ω ∂Q.measure) =
      (∫ ω, A ω ∂Q.measure) * ∫ ω, B ω ∂Q.measure :=
  Regeneration.integral_mul_eq_of_corrected_halfSpace_versions Q _ _ _
    (regeneration_scaled_gap r₀ lam l h₀ h₁ hl hsep) A B A' B' hA hB hAe hBe

/-- The actual slice admits the source's uniform-endpoint formula, before locality or normalization.
The single jointly measurable future version works for every deterministic history test. -/
theorem regeneration_exists_endpoint_slice_formula {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hb : Regeneration.BoundedRealTest Φ) :
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ ω ∂Q.measure, B (0, ω) = ∫ z, Regeneration.killedFutureTest (l / lam)
        (Regeneration.Renewal.forceCoord hd) Φ ((0, ω), z) ∂K (0, ω)) ∧
      (∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
        B xω = ∫ z, Regeneration.killedFutureTest (l / lam)
          (Regeneration.Renewal.forceCoord hd) Φ (xω, z) ∂K xω) ∧
      ∀ (m : ℕ) (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H →
        Regeneration.BoundedRealTest H →
        (∫ p in {p : FieldPair d × Regeneration.CoupledSample d |
            regenerationTime hd lam l 1 p.2 =
              ((((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          H p.2 * Φ (regenerationRecord hd lam l 1 p) ∂Regeneration.annealedCoupledLaw Q.measure K) =
          ∫ ω, δ * ∫ z,
            ((Regeneration.forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam)
              lam (l / lam) (Regeneration.Renewal.forceCoord hd) m).indicator H) z *
            Regeneration.endpointAverage (Regeneration.Renewal.forceCoord hd) (l / lam)
              (z.1 ((m : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) (fun y => B (y, ω))
            ∂K (0, ω) ∂Q.measure := by
  simpa only [regenerationTime_one_eq_first, regenerationRecord_eq_iteratedRecord] using
    Regeneration.exists_killed_future_version_slice_integral hd Q lam h₀.le h₁ P K
      hK.1 hK.2.1 hK.2.2.1 (Regeneration.Renewal.regenDelta lam)
      (Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))) δ (l / lam) (div_pos hl h₀)
      (Regeneration.Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.1 Φ hΦ hb

/-- Spatial Fubini for the same literal slice and one common killed-future version.
This is the deterministic endpoint calculation in Appendix A, before proving
half-space locality and dividing the formula for Φ by the formula for one. -/
theorem regeneration_exists_spatial_slice_formula {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hb : Regeneration.BoundedRealTest Φ) :
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ ω ∂Q.measure, B (0, ω) = ∫ z, Regeneration.killedFutureTest (l / lam)
        (Regeneration.Renewal.forceCoord hd) Φ ((0, ω), z) ∂K (0, ω)) ∧
      (∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
        B xω = ∫ z, Regeneration.killedFutureTest (l / lam)
          (Regeneration.Renewal.forceCoord hd) Φ (xω, z) ∂K xω) ∧
      ∀ (m : ℕ) (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H →
        Regeneration.BoundedRealTest H →
        (∫ p in {p : FieldPair d × Regeneration.CoupledSample d |
            regenerationTime hd lam l 1 p.2 =
              ((((m + 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          H p.2 * Φ (regenerationRecord hd lam l 1 p) ∂Regeneration.annealedCoupledLaw Q.measure K) =
          (δ / (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
            (l / lam) (0 : Vec d))).toReal) *
          ∫ y, ∫ ω, Regeneration.firstSlicePastIntegral (Regeneration.Renewal.regenDelta lam)
            lam (l / lam) (Regeneration.Renewal.forceCoord hd) m K H (y, ω) * B (y, ω)
            ∂Q.measure := by
  obtain ⟨B, hB, hbB, hBo, hBp, _⟩ :=
    regeneration_exists_endpoint_slice_formula hd Q lam l δ h₀ h₁ hl P K hK Φ hΦ hb
  refine ⟨B, hB, hbB, hBo, hBp, ?_⟩
  intro m H hH hbH
  simpa only [regenerationTime_one_eq_first, regenerationRecord_eq_iteratedRecord] using
    Regeneration.firstRegeneration_slice_integral_eq hd Q lam h₀.le h₁ P K
      hK.1 hK.2.1 hK.2.2.1 (Regeneration.Renewal.regenDelta lam)
      (Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))) δ (l / lam) (div_pos hl h₀)
      (Regeneration.Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.1
      Φ hΦ hb B hB hbB hBp m H hH hbH

end EinsteinFull
