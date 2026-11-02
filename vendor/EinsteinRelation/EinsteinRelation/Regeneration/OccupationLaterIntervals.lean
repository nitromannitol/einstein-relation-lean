import EinsteinRelation.Carriers.RegenerationCorrectorTwins
import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Regeneration.OccupationFromSteps
import EinsteinRelation.Regeneration.RenewalCarriers

/-!
# Step 2 of Proposition 3.2: the later regeneration intervals

Source `paper/main.tex` lines 477–490 (Step 2 of `regen.occupation`). For `k ≥ 1` the coupled
expected reward `ξ_k` of the regeneration interval `[τ_k, τ_{k+1})` is bounded by `(μ D)⁻¹`
times the expected reward `ξ_0` of the first interval, where `μ` is the coupled annealed law and
`D` is the no-backtracking event. The bound comes from the renewal identity (Lemma 3.1,
`regen.renewal`), applied to truncations of a record functional and passed to the monotone limit,
together with the coupling tail `P̂(D) ≥ c`.

The renewal identity enters as the hypothesis `RenewalLemma31At`. The pathwise record
factorization of the cycle reward (the identity that makes `ξ_k` a function of the future record)
enters as the hypothesis `CycleRewardFactors`.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation

/-! ## The renewal input and the cycle reward -/

/-- Lemma 3.1 (`regen.renewal`, `paper/main.tex` lines 342–348) at the threshold `l₀`, in the
production form of `EinsteinRelation.Frozen.renewalV2`. The coupled path law input is replaced by
the environment law `Q` and the coupled kernel `K`, with `I.Q = Q.measure` built in, and the frozen
names by their production twins. The frozen statement is
`∀ d hd Λ₀ r₀, ∃ l₀, r₀ < 2 l₀ ∧ ∀ Q, RenewalLemma31At hd Q l₀`. -/
def RenewalLemma31At {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (l₀ : ℝ) :
    Prop :=
  ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
      ∀ hGMP : Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ
        hl0.le hl1 P K,
      ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
          (Carriers.cycleConditioningEvent hd (l / lam)) ≠ 0,
      ∀ k : ℕ, 1 ≤ k →
        AEMeasurable (Regeneration.Renewal.cycleRecord hd lam l k)
          (Regeneration.annealedCoupledLaw Q.measure K) ∧
        AEMeasurable (Regeneration.Renewal.cycleRecord hd lam l 0)
          (Regeneration.annealedCoupledLaw Q.measure K) ∧
        ∀ Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ,
          Measurable Φ → Regeneration.BoundedRealTest Φ →
          (∫ ωz, Φ (Regeneration.Renewal.cycleRecord hd lam l k ωz)
              ∂(Regeneration.annealedCoupledLaw Q.measure K)) =
            ∫ ωz, Φ (Regeneration.Renewal.cycleRecord hd lam l 0 ωz)
              ∂((Carriers.cycleConditionedLaw Q.measure K hGMP.1 hd (l / lam) hD).1)

/-- The coupled cycle reward `ξ_k` of Step 2 (`paper/main.tex` lines 477–490): the integral of
`|G|` along the observed environment over the regeneration interval `[τ_k, τ_{k+1})`. It is the
integrand of `LaterIntervalsStep` and `FirstRewardStep`. -/
def cycleReward {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (G : FieldPair d → ℝ) (k : ℕ)
    (ωz : FieldPair d × Regeneration.CoupledSample d) : ℝ≥0∞ :=
  ∫⁻ t in regenInterval
      (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
        (Regeneration.Renewal.forceCoord hd) k)
      (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
        (Regeneration.Renewal.forceCoord hd) (k + 1)),
    ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|

/-- The pathwise record factorization of Step 2 (`paper/main.tex` lines 481–484). There is one
measurable function `F` of the future record such that `ξ_k ≤ F(𝒴_k)` for every `k ≥ 1`, and
`F(𝒴_0) ≤ ξ_0` on the no-backtracking event `D`. On `D` the reward `ξ_0` is a function of `𝒴_0`,
and the same function of `𝒴_k` gives `ξ_k`. -/
def CycleRewardFactors {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l : ℝ) (K : Regeneration.CoupledQuenchedLaws d) (G : FieldPair d → ℝ) : Prop :=
  ∃ F : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ≥0∞,
    Measurable F ∧
    (∀ k : ℕ, 1 ≤ k → ∀ᵐ ωz ∂(Regeneration.annealedCoupledLaw Q.measure K),
      cycleReward hd lam l G k ωz ≤ F (Regeneration.Renewal.cycleRecord hd lam l k ωz)) ∧
    (∀ᵐ ωz ∂(Regeneration.annealedCoupledLaw Q.measure K),
      ωz ∈ Carriers.cycleConditioningEvent hd (l / lam) →
        F (Regeneration.Renewal.cycleRecord hd lam l 0 ωz) ≤ cycleReward hd lam l G 0 ωz)

/-! ## Truncation of extended-real functionals -/

/-- The truncation `min (F y) n` of an extended-real functional, as a real function. -/
def truncR {Y : Type*} (F : Y → ℝ≥0∞) (n : ℕ) (y : Y) : ℝ :=
  (min (F y) (n : ℝ≥0∞)).toReal

theorem measurable_truncR {Y : Type*} [MeasurableSpace Y] {F : Y → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) : Measurable (truncR F n) := by
  have hmin : Measurable fun y => min (F y) (n : ℝ≥0∞) := hF.min measurable_const
  exact hmin.ennreal_toReal

theorem abs_truncR_le {Y : Type*} (F : Y → ℝ≥0∞) (n : ℕ) (y : Y) :
    |truncR F n y| ≤ n := by
  unfold truncR
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg n)
    ((min_le_right _ _).trans (ENNReal.ofReal_natCast n).ge)

theorem ofReal_truncR {Y : Type*} (F : Y → ℝ≥0∞) (n : ℕ) (y : Y) :
    ENNReal.ofReal (truncR F n y) = min (F y) (n : ℝ≥0∞) :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))

theorem integrable_truncR_self {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : Y → ℝ≥0∞} (hF : Measurable F) {X : Ω → Y}
    (hX : AEMeasurable X μ) (n : ℕ) : Integrable (fun ω => truncR F n (X ω)) μ :=
  Integrable.of_bound ((measurable_truncR hF n).comp_aemeasurable hX).aestronglyMeasurable
    (n : ℝ) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_truncR_le F n (X ω))

theorem integrable_truncR_of_ac {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {μ ν : Measure Ω} [IsFiniteMeasure ν] (hν : ν ≪ μ) {F : Y → ℝ≥0∞} (hF : Measurable F)
    {X : Ω → Y} (hX : AEMeasurable X μ) (n : ℕ) :
    Integrable (fun ω => truncR F n (X ω)) ν :=
  have hmeas : AEStronglyMeasurable (fun ω => truncR F n (X ω)) μ :=
    ((measurable_truncR hF n).comp_aemeasurable hX).aestronglyMeasurable
  Integrable.of_bound (AEStronglyMeasurable.mono_ac hν hmeas) (n : ℝ)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact abs_truncR_le F n (X ω))

theorem iSup_min_natCast (x : ℝ≥0∞) : ⨆ n : ℕ, min x (n : ℝ≥0∞) = x := by
  apply le_antisymm
  · exact iSup_le fun n => min_le_left _ _
  · by_cases hx : x = ⊤
    · subst hx
      have h : ∀ n : ℕ, min (⊤ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) :=
        fun n => min_eq_right le_top
      simp only [h]
      exact ENNReal.iSup_natCast.ge
    · obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hx
      exact le_iSup_of_le m (le_of_eq (min_eq_left hm.le).symm)

/-! ## The probabilistic core of Step 2 -/

/-- Step 2 bookkeeping for one later interval. Let `D` have positive mass, let the record
functional `Ya` at a later cycle and `Y0` at the first cycle satisfy the renewal identity for
bounded measurable test functions (Lemma 3.1 with the conditional law `μ[|D]`), and let `F` be a
measurable functional with `ξa ≤ F ∘ Ya` almost surely and `F ∘ Y0 ≤ ξ0` on `D`. Then the
expected later reward is at most `(μ D)⁻¹` times the expected first reward. -/
theorem lintegral_le_of_truncated_renewal {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Set Ω) (hD : MeasurableSet D) (hpos : μ D ≠ 0)
    (Ya Y0 : Ω → Y) (hYa : AEMeasurable Ya μ) (hY0 : AEMeasurable Y0 μ)
    (hId : ∀ Φ : Y → ℝ, Measurable Φ → (∃ C : ℝ, ∀ y, |Φ y| ≤ C) →
      ∫ ω, Φ (Ya ω) ∂μ = ∫ ω, Φ (Y0 ω) ∂(ProbabilityTheory.cond μ D))
    (F : Y → ℝ≥0∞) (hF : Measurable F) (ξ0 ξa : Ω → ℝ≥0∞)
    (hξa : ∀ᵐ ω ∂μ, ξa ω ≤ F (Ya ω))
    (hξ0 : ∀ᵐ ω ∂μ, ω ∈ D → F (Y0 ω) ≤ ξ0 ω) :
    ∫⁻ ω, ξa ω ∂μ ≤ (μ D)⁻¹ * ∫⁻ ω, ξ0 ω ∂μ := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ D) :=
    ProbabilityTheory.cond_isProbabilityMeasure hpos
  have hac : ProbabilityTheory.cond μ D ≪ μ := ProbabilityTheory.cond_absolutelyContinuous
  have hbound : ∀ n : ℕ, ∫⁻ ω, min (F (Ya ω)) (n : ℝ≥0∞) ∂μ ≤
      (μ D)⁻¹ * ∫⁻ ω, ξ0 ω ∂μ := by
    intro n
    calc ∫⁻ ω, min (F (Ya ω)) (n : ℝ≥0∞) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (truncR F n (Ya ω)) ∂μ :=
          lintegral_congr fun ω => (ofReal_truncR F n (Ya ω)).symm
      _ = ENNReal.ofReal (∫ ω, truncR F n (Ya ω) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (integrable_truncR_self hF hYa n)
            (ae_of_all _ fun ω => ENNReal.toReal_nonneg)).symm
      _ = ENNReal.ofReal (∫ ω, truncR F n (Y0 ω) ∂(ProbabilityTheory.cond μ D)) := by
          rw [hId (truncR F n) (measurable_truncR hF n) ⟨(n : ℝ), abs_truncR_le F n⟩]
      _ = ∫⁻ ω, ENNReal.ofReal (truncR F n (Y0 ω)) ∂(ProbabilityTheory.cond μ D) :=
          ofReal_integral_eq_lintegral_ofReal (integrable_truncR_of_ac hac hF hY0 n)
            (ae_of_all _ fun ω => ENNReal.toReal_nonneg)
      _ = ∫⁻ ω, min (F (Y0 ω)) (n : ℝ≥0∞) ∂(ProbabilityTheory.cond μ D) :=
          lintegral_congr fun ω => ofReal_truncR F n (Y0 ω)
      _ = (μ D)⁻¹ * ∫⁻ ω in D, min (F (Y0 ω)) (n : ℝ≥0∞) ∂μ := by
          rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
      _ ≤ (μ D)⁻¹ * ∫⁻ ω in D, ξ0 ω ∂μ :=
          mul_le_mul_right (setLIntegral_mono_ae' hD (hξ0.mono fun ω h hω =>
            (min_le_left _ _).trans (h hω))) _
      _ ≤ (μ D)⁻¹ * ∫⁻ ω, ξ0 ω ∂μ :=
          mul_le_mul_right (setLIntegral_le_lintegral D ξ0) _
  have hmin : ∀ n : ℕ, Measurable fun y => min (F y) (n : ℝ≥0∞) :=
    fun n => hF.min measurable_const
  have hsup : ∫⁻ ω, F (Ya ω) ∂μ ≤ (μ D)⁻¹ * ∫⁻ ω, ξ0 ω ∂μ := by
    calc ∫⁻ ω, F (Ya ω) ∂μ
        = ∫⁻ ω, ⨆ n : ℕ, min (F (Ya ω)) (n : ℝ≥0∞) ∂μ :=
          lintegral_congr fun ω => (iSup_min_natCast _).symm
      _ = ⨆ n : ℕ, ∫⁻ ω, min (F (Ya ω)) (n : ℝ≥0∞) ∂μ :=
          lintegral_iSup' (fun n => (hmin n).comp_aemeasurable hYa)
            (ae_of_all _ fun ω n m hnm => min_le_min_left _ (by exact_mod_cast hnm))
      _ ≤ (μ D)⁻¹ * ∫⁻ ω, ξ0 ω ∂μ := iSup_le hbound
  exact (lintegral_mono_ae hξa).trans hsup

/-! ## The later-interval bound -/

/-- Step 2 of Proposition 3.2 (`paper/main.tex` lines 477–490), from the renewal identity
(`RenewalLemma31At`), the coupling tail `P̂(D) ≥ c` (`HasNoBacktrackingMass`), the first-reward
bound (`FirstRewardStep`), and the record factorization of the cycle reward
(`CycleRewardFactors`). The constant is `C' = C / c`. -/
theorem laterIntervals_of_renewal {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ p C c : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hc : 0 < c)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hGMP : Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q lam l δ
      hl0.le hl1 P K)
    (hcoup : Regeneration.HasNoBacktrackingMass Q.measure (l / lam) c
      (Regeneration.Renewal.forceCoord hd) K)
    (l₀ : ℝ) (hl₀ : l₀ ≤ l) (H31 : RenewalLemma31At hd Q l₀)
    (G : FieldPair d → ℝ)
    (hfirst : FirstRewardStep hd Q lam l p C K G)
    (hF : CycleRewardFactors hd Q lam l K G) :
    LaterIntervalsStep hd Q lam l p (C / c) K G := by
  unfold LaterIntervalsStep
  intro k hk
  haveI : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hGMP.1
  have hmass : ENNReal.ofReal c ≤
      Regeneration.annealedCoupledLaw Q.measure K (Carriers.cycleConditioningEvent hd (l / lam)) :=
    hcoup
  have hpos : Regeneration.annealedCoupledLaw Q.measure K
      (Carriers.cycleConditioningEvent hd (l / lam)) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc) hmass).ne'
  have hmeas : Measurable (fun ωz : FieldPair d × Regeneration.CoupledSample d => ωz.2.1) :=
    measurable_fst.comp measurable_snd
  have hNB := Regeneration.measurableSet_NoBacktracking (l / lam)
    (Regeneration.Renewal.forceCoord hd)
  have hDmeas : MeasurableSet (Carriers.cycleConditioningEvent hd (l / lam)) :=
    hNB.preimage hmeas
  obtain ⟨hAk, hA0, hIdk⟩ := H31 l hl₀ δ hδ0 hδ1 lam hl0 hl1 P K hGMP hpos k hk
  obtain ⟨F, hFm, hFa, hF0⟩ := hF
  have hchain := lintegral_le_of_truncated_renewal (Regeneration.annealedCoupledLaw Q.measure K)
    (Carriers.cycleConditioningEvent hd (l / lam)) hDmeas hpos
    (Regeneration.Renewal.cycleRecord hd lam l k) (Regeneration.Renewal.cycleRecord hd lam l 0)
    hAk hA0 hIdk F hFm (cycleReward hd lam l G 0) (cycleReward hd lam l G k) (hFa k hk) hF0
  have hfirst' : ∫⁻ ωz, cycleReward hd lam l G 0 ωz ∂(Regeneration.annealedCoupledLaw Q.measure K) ≤
      ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
        eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := hfirst
  have hinv : (Regeneration.annealedCoupledLaw Q.measure K
      (Carriers.cycleConditioningEvent hd (l / lam)))⁻¹ ≤ ENNReal.ofReal c⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hc]
    exact ENNReal.inv_le_inv.2 hmass
  calc ∫⁻ ωz, cycleReward hd lam l G k ωz ∂(Regeneration.annealedCoupledLaw Q.measure K)
      ≤ (Regeneration.annealedCoupledLaw Q.measure K
          (Carriers.cycleConditioningEvent hd (l / lam)))⁻¹ *
        ∫⁻ ωz, cycleReward hd lam l G 0 ωz ∂(Regeneration.annealedCoupledLaw Q.measure K) :=
        hchain
    _ ≤ (Regeneration.annealedCoupledLaw Q.measure K
          (Carriers.cycleConditioningEvent hd (l / lam)))⁻¹ *
        (ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)) :=
        mul_le_mul_right hfirst' _
    _ ≤ ENNReal.ofReal c⁻¹ *
        (ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)) :=
        mul_le_mul_left hinv _
    _ = ENNReal.ofReal (c⁻¹ * (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ))) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hc.le), mul_assoc]
    _ = ENNReal.ofReal (C / c * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
        rw [show C / c * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ) =
          c⁻¹ * (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) by ring]

end EinsteinRelation

end
