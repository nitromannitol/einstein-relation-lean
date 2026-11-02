import EinsteinRelation.Regeneration.CycleRewardFactors
import EinsteinRelation.Regeneration.OccupationLaterIntervals
import EinsteinRelation.Regeneration.NoBacktracking
import EinsteinRelation.Regeneration.RegenerationShiftObservables
import EinsteinRelation.Probability.FutureFieldDecoder
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Carriers.DensityAnnealedTwins

/-!
# Pathwise factorization of the cycle reward (Step 2 of Proposition 3.2)

Source `paper/main.tex` lines 477–490. The later-interval reward `ξ_k` is the integral of `|G|`
along the environment seen from the regeneration time `τ_k`, over `[τ_k, τ_{k+1})`. On the
no-backtracking event the path stays above `-R` in the force direction, so every ball of radius
`R = l/λ` around a visited point lies in the future half-space. A function measurable for the local
σ-algebra of that ball therefore sees only the future record `𝒴_k`.

The record stores the environment on the future half-space as a field. The measurable decoder
`Probability.exists_future_halfSpace_decoder` recovers a continuous field from it, and the
extension `extendFromHalfSpace` evaluates that field after projecting each point onto the
half-space. The factor `regenFactor` integrates `|G|` along the recentered record path over the
length of the record's first regeneration interval, which is the same length as `τ_{k+1} - τ_k`.

`CycleRewardFactors` is proved for `G` measurable for the local σ-algebra of `B_{l/λ}` (the
`H_{B_{l/λ}}`-measurability of Proposition 3.2) and for `0 < λ` (the standing assumption
`λ ∈ (0, 1]`).
-/

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation

open Regeneration Regeneration.Renewal

/-! ## Extension of a field on the future half-space -/

/-- Projection of `Vec d` onto the closed future half-space `{x | -2R ≤ x i}`: the coordinate `i`
is replaced by its maximum with `-2R`. -/
def halfSpaceProj {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) : Vec d :=
  Function.update x i (max (x i) (-2 * R))

theorem halfSpaceProj_mem {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) :
    -2 * R ≤ halfSpaceProj i R x i := by
  unfold halfSpaceProj
  rw [Function.update_self]
  exact le_max_right _ _

theorem continuous_halfSpaceProj {d : ℕ} (i : Fin d) (R : ℝ) :
    Continuous (halfSpaceProj i R) :=
  continuous_id.update i ((continuous_apply i).max continuous_const)

/-- The projection fixes every point of the half-space. -/
theorem halfSpaceProj_eq_self {d : ℕ} (i : Fin d) (R : ℝ) (z : Vec d) (hz : -2 * R ≤ z i) :
    halfSpaceProj i R z = z := by
  unfold halfSpaceProj
  rw [max_eq_left hz]
  exact Function.update_eq_self i z

/-- The projection `Vec d → future half-space` as a continuous map. -/
def halfSpaceSection {d : ℕ} (i : Fin d) (R : ℝ) :
    C(Vec d, Regeneration.FutureHalfSpace d i R) where
  toFun x := ⟨halfSpaceProj i R x, halfSpaceProj_mem i R x⟩
  continuous_toFun := (continuous_halfSpaceProj i R).subtype_mk
    (p := fun x : Vec d => -2 * R ≤ x i) (halfSpaceProj_mem i R)

/-- The restriction of a coefficient pair to the future half-space, as a continuous field. -/
def restrictHalfSpace {d : ℕ} (i : Fin d) (R : ℝ) (E : FieldPair d) :
    C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ) where
  toFun x := (E.1 x.1, E.2 x.1)
  continuous_toFun := (E.1.continuous.comp continuous_subtype_val).prodMk
    (E.2.continuous.comp continuous_subtype_val)

/-- The extension of a continuous field on the future half-space to `Vec d`: each point is
projected onto the half-space before the field is evaluated. The extension agrees with the field
on the half-space, and it is a coefficient pair for every continuous input. -/
def extendFromHalfSpace {d : ℕ} (i : Fin d) (R : ℝ)
    (f : C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ)) : FieldPair d :=
  ((ContinuousMap.fst : C(Mat d × ℝ, Mat d)).comp (f.comp (halfSpaceSection i R)),
    (ContinuousMap.snd : C(Mat d × ℝ, ℝ)).comp (f.comp (halfSpaceSection i R)))

theorem continuous_extendFromHalfSpace {d : ℕ} (i : Fin d) (R : ℝ) :
    Continuous (extendFromHalfSpace i R) := by
  show Continuous fun f : C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ) =>
    (((ContinuousMap.fst : C(Mat d × ℝ, Mat d)).comp (f.comp (halfSpaceSection i R))),
      ((ContinuousMap.snd : C(Mat d × ℝ, ℝ)).comp (f.comp (halfSpaceSection i R))))
  refine Continuous.prodMk ?_ ?_
  · exact (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(Mat d × ℝ, Mat d))).comp
      (ContinuousMap.continuous_precomp (halfSpaceSection i R))
  · exact (ContinuousMap.continuous_postcomp (ContinuousMap.snd : C(Mat d × ℝ, ℝ))).comp
      (ContinuousMap.continuous_precomp (halfSpaceSection i R))

/-- The extension is Borel measurable for the Borel σ-algebra of the continuous fields. -/
theorem measurable_extendFromHalfSpace {d : ℕ} (i : Fin d) (R : ℝ) :
    @Measurable (C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ)) (FieldPair d)
      (borel _) inferInstance (extendFromHalfSpace i R) := by
  letI : MeasurableSpace C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ) := borel _
  haveI : BorelSpace C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ) := ⟨rfl⟩
  exact (continuous_extendFromHalfSpace i R).measurable

/-- On the half-space, the extension of the restriction of `E` is `E` itself. The translate by
`v` of the extension agrees with the translate of `E` at every `x` whose shifted point `v + x`
lies in the half-space. -/
theorem translate_extend_eq_of_mem {d : ℕ} (i : Fin d) (R : ℝ) (E : FieldPair d) (v x : Vec d)
    (hx : -2 * R ≤ (v + x) i) :
    (translate v (extendFromHalfSpace i R (restrictHalfSpace i R E))).1 x = (translate v E).1 x ∧
      (translate v (extendFromHalfSpace i R (restrictHalfSpace i R E))).2 x =
        (translate v E).2 x := by
  have hproj : halfSpaceProj i R (v + x) = v + x := halfSpaceProj_eq_self i R (v + x) hx
  constructor
  · show E.1 (halfSpaceProj i R (v + x)) = E.1 (v + x)
    rw [hproj]
  · show E.2 (halfSpaceProj i R (v + x)) = E.2 (v + x)
    rw [hproj]

/-! ## Invariance of the regeneration times under spatial recentering

Every construction of the regeneration times uses the path only through coordinate increments
`γ s i - γ t i`, and the time shift keeps these increments. Recentering therefore leaves the
regeneration times unchanged. -/

theorem increments_pathTimeShift {d : ℕ} {i : Fin d} {γ δ : Path d}
    (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) (t : ℝ≥0) :
    ∀ s u : ℝ≥0, (pathTimeShift δ t) s i - (pathTimeShift δ t) u i =
      (pathTimeShift γ t) s i - (pathTimeShift γ t) u i :=
  fun s u => h (t + s) (t + u)

theorem increments_recenterSample {d : ℕ} (i : Fin d) (x : Vec d) (z : CoupledSample d)
    (s t : ℝ≥0) :
    (recenterSample x z).1 s i - (recenterSample x z).1 t i = z.1 s i - z.1 t i := by
  show (z.1 s - x) i - (z.1 t - x) i = z.1 s i - z.1 t i
  simp only [Pi.sub_apply]
  ring

theorem firstHittingAbove_congr_inc {d : ℕ} {i : Fin d} {γ δ : Path d}
    (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) (a : ℝ) :
    firstHittingAbove δ i a = firstHittingAbove γ i a := by
  unfold firstHittingAbove
  refine iInf_congr fun t => ?_
  rw [h t 0]

theorem firstHittingBelow_congr_inc {d : ℕ} {i : Fin d} {γ δ : Path d}
    (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) (a : ℝ) :
    firstHittingBelow δ i a = firstHittingBelow γ i a := by
  unfold firstHittingBelow
  refine iInf_congr fun t => ?_
  rw [h t 0]

theorem coordinateMaximum_congr_inc {d : ℕ} {i : Fin d} {γ δ : Path d}
    (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) (t : ℝ≥0) :
    coordinateMaximum δ i t = coordinateMaximum γ i t := by
  have hf : (fun u : ℝ≥0 => δ u i - δ 0 i) = fun u : ℝ≥0 => γ u i - γ 0 i :=
    funext fun u => h u 0
  unfold coordinateMaximum
  rw [hf]

theorem passageSequence_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) {i : Fin d} {γ δ : Path d}
    (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) (n : ℕ) :
    passageSequence Δ lam R a δ i n = passageSequence Δ lam R a γ i n := by
  induction n with
  | zero =>
    simp only [passageSequence]
    exact firstHittingAbove_congr_inc h _
  | succ n ih =>
    simp only [passageSequence, ih, firstHittingAbove_congr_inc h, coordinateMaximum_congr_inc h]

theorem isGoodPassage_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) {i : Fin d} {γ δ : Path d}
    (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) (n : ℕ) :
    IsGoodPassage Δ lam R a δ i n = IsGoodPassage Δ lam R a γ i n := by
  simp only [IsGoodPassage, passageSequence_congr_inc Δ lam R a h, h]

theorem firstRoundedCandidate_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) {i : Fin d}
    {γ δ : Path d} (h : ∀ s t : ℝ≥0, δ s i - δ t i = γ s i - γ t i) :
    firstRoundedCandidate Δ lam R a δ i = firstRoundedCandidate Δ lam R a γ i := by
  unfold firstRoundedCandidate
  refine iInf_congr fun n => ?_
  rw [isGoodPassage_congr_inc Δ lam R a h n, passageSequence_congr_inc Δ lam R a h n]

theorem roundedCandidateSequence_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) {i : Fin d}
    {z w : CoupledSample d} (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i) (n : ℕ) :
    roundedCandidateSequence Δ lam R a w i n = roundedCandidateSequence Δ lam R a z i n := by
  induction n with
  | zero =>
    simp only [roundedCandidateSequence]
    exact firstRoundedCandidate_congr_inc Δ lam R a h
  | succ n ih =>
    simp only [roundedCandidateSequence, ih]
    rw [firstRoundedCandidate_congr_inc Δ lam R (3 * lam * R)
      (increments_pathTimeShift h (roundedCandidateSequence Δ lam R a z i n).toNNReal)]

theorem isSuccessfulCandidate_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) {i : Fin d}
    {z w : CoupledSample d} (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i)
    (hb : w.2 = z.2) (n : ℕ) :
    IsSuccessfulCandidate Δ lam R a w i n = IsSuccessfulCandidate Δ lam R a z i n := by
  simp only [IsSuccessfulCandidate, roundedCandidateSequence_congr_inc Δ lam R a h n, hb]

theorem firstSuccessfulCandidate_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ) {i : Fin d}
    {z w : CoupledSample d} (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i)
    (hb : w.2 = z.2) :
    firstSuccessfulCandidate Δ lam R a w i = firstSuccessfulCandidate Δ lam R a z i := by
  unfold firstSuccessfulCandidate
  refine iInf_congr fun n => ?_
  rw [isSuccessfulCandidate_congr_inc Δ lam R a h hb n,
    roundedCandidateSequence_congr_inc Δ lam R a h n]

theorem trialDownwardTime_congr_inc {d : ℕ} (Δ : ℝ≥0) (R : ℝ) {i : Fin d} {z w : CoupledSample d}
    (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i) (S : ℝ≥0∞) :
    trialDownwardTime Δ R w i S = trialDownwardTime Δ R z i S := by
  unfold trialDownwardTime
  by_cases hS : S = ⊤
  · simp only [if_pos hS]
  · simp only [if_neg hS]
    congr 1
    exact firstHittingBelow_congr_inc (increments_pathTimeShift h S.toNNReal) (-R)

theorem trialFailureTime_congr_inc {d : ℕ} (Δ : ℝ≥0) (R : ℝ) {i : Fin d} {z w : CoupledSample d}
    (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i) (S : ℝ≥0∞) :
    trialFailureTime Δ R w i S = trialFailureTime Δ R z i S := by
  unfold trialFailureTime
  rw [trialDownwardTime_congr_inc Δ R h S]

theorem sampleTimeShift_congr_inc {d : ℕ} (Δ : ℝ≥0) {i : Fin d} {z w : CoupledSample d}
    (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i) (hb : w.2 = z.2) (t : ℝ≥0) :
    (∀ s u : ℝ≥0, (sampleTimeShift Δ w t).1 s i - (sampleTimeShift Δ w t).1 u i =
        (sampleTimeShift Δ z t).1 s i - (sampleTimeShift Δ z t).1 u i) ∧
      (sampleTimeShift Δ w t).2 = (sampleTimeShift Δ z t).2 := by
  refine ⟨increments_pathTimeShift h t, ?_⟩
  show (fun n : ℕ => w.2 (gridIndex Δ t + n)) = fun n : ℕ => z.2 (gridIndex Δ t + n)
  rw [hb]

theorem trialStartSequence_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) {i : Fin d}
    {z w : CoupledSample d} (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i)
    (hb : w.2 = z.2) (n : ℕ) :
    trialStartSequence Δ lam R w i n = trialStartSequence Δ lam R z i n := by
  induction n with
  | zero =>
    simp only [trialStartSequence]
    rw [firstSuccessfulCandidate_congr_inc Δ lam R (3 * lam * R) h hb]
  | succ n ih =>
    have hT : trialFailureTime Δ R w i (trialStartSequence Δ lam R w i n) =
        trialFailureTime Δ R z i (trialStartSequence Δ lam R z i n) := by
      rw [ih, trialFailureTime_congr_inc Δ R h]
    have hS : ∀ t : ℝ≥0,
        firstSuccessfulCandidate Δ lam R
          (lam * (coordinateMaximum w.1 i t - (w.1 t i - w.1 0 i) + R)) (sampleTimeShift Δ w t) i =
        firstSuccessfulCandidate Δ lam R
          (lam * (coordinateMaximum z.1 i t - (z.1 t i - z.1 0 i) + R)) (sampleTimeShift Δ z t) i := by
      intro t
      rw [coordinateMaximum_congr_inc h t, h t 0]
      exact firstSuccessfulCandidate_congr_inc (z := sampleTimeShift Δ z t)
        (w := sampleTimeShift Δ w t) Δ lam R _ (sampleTimeShift_congr_inc Δ h hb t).1
        (sampleTimeShift_congr_inc Δ h hb t).2
    simp only [trialStartSequence, hT, hS]

theorem isRegenerationTrial_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) {i : Fin d}
    {z w : CoupledSample d} (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i)
    (hb : w.2 = z.2) (n : ℕ) :
    IsRegenerationTrial Δ lam R w i n = IsRegenerationTrial Δ lam R z i n := by
  simp only [IsRegenerationTrial, trialStartSequence_congr_inc Δ lam R h hb n,
    trialFailureTime_congr_inc Δ R h]

theorem firstRegenerationTime_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) {i : Fin d}
    {z w : CoupledSample d} (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i)
    (hb : w.2 = z.2) :
    firstRegenerationTime Δ lam R w i = firstRegenerationTime Δ lam R z i := by
  unfold firstRegenerationTime
  refine iInf_congr fun n => ?_
  rw [isRegenerationTrial_congr_inc Δ lam R h hb n, trialStartSequence_congr_inc Δ lam R h hb n]

/-- The first regeneration time of a recentered sample is that of the sample. -/
theorem firstRegenerationTime_recenterSample {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (x : Vec d) (z : CoupledSample d) :
    firstRegenerationTime Δ lam R (recenterSample x z) i = firstRegenerationTime Δ lam R z i :=
  firstRegenerationTime_congr_inc Δ lam R (fun s t => increments_recenterSample i x z s t) rfl

/-! ## Regeneration times and the no-backtracking event -/

theorem regenerationTime_succ_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (z : CoupledSample d) (i : Fin d)
    (n : ℕ) (hn : regenerationTime Δ lam R z i n ≠ ⊤) :
    regenerationTime Δ lam R z i (n + 1) = regenerationTime Δ lam R z i n +
      firstRegenerationTime Δ lam R
        (sampleTimeShift Δ z (regenerationTime Δ lam R z i n).toNNReal) i := by
  rw [regenerationTime, if_neg hn]

/-- No-backtracking bounds every later coordinate displacement from the start point below by `-R`,
strictly. -/
theorem coord_gt_of_noBacktracking {d : ℕ} (γ : Path d) (i : Fin d) (R : ℝ) (a s : ℝ≥0)
    (hD : NoBacktracking R (pathTimeShift γ a) i) :
    -R < γ (a + s) i - γ a i := by
  by_contra hc
  push_neg at hc
  have hcross : γ (a + s) i - γ (a + 0) i ≤ -R := by
    rw [add_zero]
    exact hc
  have h1 := firstHittingBelow_le_of_crossing (pathTimeShift γ a) i (-R) s hcross
  unfold NoBacktracking at hD
  rw [hD] at h1
  exact ENNReal.coe_ne_top (top_le_iff.1 h1)

/-- A path with no backtracking from time zero keeps its no-backtracking property after the time
shift by zero. -/
theorem noBacktracking_pathTimeShift_zero {d : ℕ} (R : ℝ) (i : Fin d) (γ : Path d)
    (hD : NoBacktracking R γ i) : NoBacktracking R (pathTimeShift γ 0) i := by
  have hinc : ∀ s t : ℝ≥0, (pathTimeShift γ 0) s i - (pathTimeShift γ 0) t i = γ s i - γ t i := by
    intro s t
    show γ (0 + s) i - γ (0 + t) i = γ s i - γ t i
    rw [zero_add, zero_add]
  unfold NoBacktracking at hD ⊢
  rw [firstHittingBelow_congr_inc hinc (-R)]
  exact hD

theorem regenDelta_pos {lam : ℝ} (hl0 : 0 < lam) : 0 < regenDelta lam :=
  Real.toNNReal_pos.2 (inv_pos.2 (pow_pos hl0 2))

/-! ## Shifting a regeneration interval -/

theorem mem_regenInterval_add_iff (a : ℝ≥0) (L : ℝ≥0∞) (s : ℝ) :
    s + (a : ℝ) ∈ regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L) ↔ s ∈ regenInterval 0 L := by
  have ha_top : (a : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (s + (a : ℝ)) = ENNReal.ofReal s + (a : ℝ≥0∞) := by
    intro s hs
    rw [ENNReal.ofReal_add hs (NNReal.coe_nonneg a), ENNReal.ofReal_coe_nnreal]
  rw [mem_regenInterval, mem_regenInterval]
  constructor
  · rintro ⟨h0, ha, hL⟩
    have hs : 0 ≤ s := by
      have h1 : ENNReal.ofReal (a : ℝ) ≤ ENNReal.ofReal (s + (a : ℝ)) := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact ha
      have h2 := (ENNReal.ofReal_le_ofReal_iff h0).1 h1
      linarith
    rw [hsplit s hs, add_comm (ENNReal.ofReal s)] at hL
    exact ⟨hs, zero_le, (ENNReal.add_lt_add_iff_left ha_top).1 hL⟩
  · rintro ⟨hs, -, hlt⟩
    refine ⟨add_nonneg hs (NNReal.coe_nonneg a), ?_, ?_⟩
    · rw [hsplit s hs]
      exact le_add_self
    · rw [hsplit s hs, add_comm (ENNReal.ofReal s)]
      exact (ENNReal.add_lt_add_iff_left ha_top).2 hlt

/-- Translation of the regeneration interval `[a, a + L)` by the finite start `a`. -/
theorem lintegral_regenInterval_shift (a : ℝ≥0) (L : ℝ≥0∞) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L), g t =
      ∫⁻ s in regenInterval 0 L, g (s + (a : ℝ)) := by
  have hS := measurableSet_regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L)
  have hT := measurableSet_regenInterval (0 : ℝ≥0∞) L
  have hind : ∀ s : ℝ, (regenInterval (0 : ℝ≥0∞) L).indicator (fun s => g (s + (a : ℝ))) s =
      (regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L)).indicator g (s + (a : ℝ)) := by
    intro s
    by_cases h : s ∈ regenInterval (0 : ℝ≥0∞) L
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem ((mem_regenInterval_add_iff a L s).2 h)]
    · have h' : s + (a : ℝ) ∉ regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L) :=
        fun h'' => h ((mem_regenInterval_add_iff a L s).1 h'')
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [← lintegral_indicator hS, ← lintegral_indicator hT]
  calc ∫⁻ t, (regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L)).indicator g t
      = ∫⁻ s, (regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L)).indicator g (s + (a : ℝ)) :=
        (lintegral_add_right_eq_self
          ((regenInterval (a : ℝ≥0∞) ((a : ℝ≥0∞) + L)).indicator g) (a : ℝ)).symm
    _ = ∫⁻ s, (regenInterval (0 : ℝ≥0∞) L).indicator (fun s => g (s + (a : ℝ))) s :=
        lintegral_congr fun s => (hind s).symm

/-- The shift identity for a finite start `τ`, with the endpoint `τ + L`. -/
theorem lintegral_regenInterval_shift_of_ne_top (τ : ℝ≥0∞) (hτ : τ ≠ ⊤) (L : ℝ≥0∞)
    (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in regenInterval τ (τ + L), g t =
      ∫⁻ s in regenInterval 0 L, g (s + (τ.toNNReal : ℝ)) := by
  have h := lintegral_regenInterval_shift τ.toNNReal L g
  rwa [ENNReal.coe_toNNReal hτ] at h

/-- A regeneration interval starting at `⊤` is empty. -/
theorem lintegral_regenInterval_top_eq_zero (b : ℝ≥0∞) (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in regenInterval ⊤ b, g t = 0 := by
  have hempty : regenInterval (⊤ : ℝ≥0∞) b = ∅ := by
    ext t
    constructor
    · intro h
      obtain ⟨-, h1, -⟩ := mem_regenInterval.1 h
      exact absurd (top_le_iff.1 h1) ENNReal.ofReal_ne_top
    · intro h
      simp at h
  rw [hempty]
  exact setLIntegral_empty g

/-! ## The environment on the record -/

theorem reduce_translate_sub {d : ℕ} (ω : FieldPair d) (x y : Vec d) :
    reduce (translate x ω) = translate (x - y) (translate y (reduce ω)) := by
  rw [reduce_translate, translate_add, sub_add_cancel]

/-- The reduced observation of the environment at a shifted time, as the translate of the
reduced environment at the start. -/
theorem reducedObservationAt_shift {d : ℕ} (ω : FieldPair d) (γ : Path d) (a : ℝ≥0) (s : ℝ)
    (hs : 0 ≤ s) :
    Carriers.reducedObservationAt (s + (a : ℝ)).toNNReal (ω, γ) =
      reduce (translate (γ (a + s.toNNReal)) ω) := by
  have h : (s + (a : ℝ)).toNNReal = a + s.toNNReal := by
    rw [Real.toNNReal_add hs (NNReal.coe_nonneg a), Real.toNNReal_coe, add_comm]
  rw [h]
  rfl

/-! ## The pathwise factor -/

/-- The pathwise factor of Step 2 on the future record `y`: the integral of `|G|` along the
environment translated by the recentered record path, over the record's first regeneration
interval `[0, L(y))`. The field of the record is recovered by the decoder `D` and extended by
`extendFromHalfSpace`. -/
def regenFactor {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (G : FieldPair d → ℝ) (y : FutureState d i R) : ℝ≥0∞ :=
  ∫⁻ s in regenInterval 0 (firstRegenerationTime Δ lam R (y.1, y.2.1) i),
    ENNReal.ofReal |G (translate (y.1 s.toNNReal) (extendFromHalfSpace i R (D y.2.2)))|

/-- The integrand of `regenFactor` is jointly measurable in the record and the time. -/
theorem measurable_regenFactor {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (hD : @Measurable (Regeneration.FutureHalfSpace d i R → Mat d × ℝ)
      (C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ)) inferInstance (borel _) D)
    (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | euclideanNorm x < R})
      inferInstance G) :
    Measurable (regenFactor Δ lam R i D G) := by
  have hpath : Measurable (fun p : FutureState d i R × ℝ => p.1.1 p.2.toNNReal) :=
    (Regeneration.measurable_path_eval (d := d)).comp
      ((measurable_snd.real_toNNReal).prodMk (measurable_fst.comp measurable_fst))
  have hY : Measurable (fun p : FutureState d i R × ℝ => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hE : Measurable (fun p : FutureState d i R × ℝ =>
      extendFromHalfSpace i R (D p.1.2.2)) :=
    (measurable_extendFromHalfSpace i R).comp (hD.comp hY)
  have hΦ : Measurable (fun p : FutureState d i R × ℝ =>
      translate (p.1.1 p.2.toNNReal) (extendFromHalfSpace i R (D p.1.2.2))) :=
    (Probability.continuous_translate (d := d)).measurable.comp (hpath.prodMk hE)
  have hΦloc : @Measurable (FutureState d i R × ℝ) (FieldPair d) inferInstance
      (localSigma {x : Vec d | euclideanNorm x < R})
      (fun p : FutureState d i R × ℝ =>
        translate (p.1.1 p.2.toNNReal) (extendFromHalfSpace i R (D p.1.2.2))) := by
    refine measurable_iff_comap_le.2 ?_
    unfold localSigma
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun x => ?_
    rw [MeasurableSpace.comap_comp]
    have hev : Measurable (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) :=
      (((continuous_eval_const (x : Vec d)).comp continuous_fst).prodMk
        ((continuous_eval_const (x : Vec d)).comp continuous_snd)).measurable
    exact measurable_iff_comap_le.1 (hev.comp hΦ)
  have hGΦ : Measurable (fun p : FutureState d i R × ℝ =>
      G (translate (p.1.1 p.2.toNNReal) (extendFromHalfSpace i R (D p.1.2.2)))) :=
    hG.comp hΦloc
  have hint : Measurable (fun p : FutureState d i R × ℝ =>
      ENNReal.ofReal |G (translate (p.1.1 p.2.toNNReal) (extendFromHalfSpace i R (D p.1.2.2)))|) :=
    (continuous_abs.measurable.comp hGΦ).ennreal_ofReal
  have hL : Measurable (fun y : FutureState d i R =>
      firstRegenerationTime Δ lam R (y.1, y.2.1) i) :=
    (Regeneration.measurable_firstRegenerationTime Δ lam R i).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact measurable_lintegral_regenInterval
    (fun (y : FutureState d i R) (s : ℝ) =>
      ENNReal.ofReal |G (translate (y.1 s.toNNReal) (extendFromHalfSpace i R (D y.2.2)))|)
    hint (fun _ => 0) (fun y => firstRegenerationTime Δ lam R (y.1, y.2.1) i)
    measurable_const hL

/-- On the no-backtracking event of the record's start, the integrand of `regenFactor` at the
record equals the reduced observation of the environment at the shifted time. -/
theorem integrand_futureRecord_eq {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (D : (Regeneration.FutureHalfSpace d i R → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ))
    (hDr : ∀ f : C(Regeneration.FutureHalfSpace d i R, Mat d × ℝ), D (fun x => f x) = f)
    (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | euclideanNorm x < R})
      inferInstance G)
    (ω : FieldPair d) (z : CoupledSample d) (a s : ℝ≥0)
    (hNB : NoBacktracking R (pathTimeShift z.1 a) i) :
    ENNReal.ofReal |G (translate ((futureRecord Δ R ω z i a).1 s)
        (extendFromHalfSpace i R (D (futureRecord Δ R ω z i a).2.2)))| =
      ENNReal.ofReal |G (reduce (translate (z.1 (a + s)) ω))| := by
  have hD : D (futureRecord Δ R ω z i a).2.2 =
      restrictHalfSpace i R (translate (z.1 a) (reduce ω)) :=
    hDr (restrictHalfSpace i R (translate (z.1 a) (reduce ω)))
  rw [hD]
  show ENNReal.ofReal |G (translate (z.1 (a + s) - z.1 a)
      (extendFromHalfSpace i R (restrictHalfSpace i R (translate (z.1 a) (reduce ω)))))| =
    ENNReal.ofReal |G (reduce (translate (z.1 (a + s)) ω))|
  have hvi : -R < (z.1 (a + s) - z.1 a) i := by
    rw [Pi.sub_apply]
    exact coord_gt_of_noBacktracking z.1 i R a s hNB
  have hloc : G (translate (z.1 (a + s) - z.1 a)
      (extendFromHalfSpace i R (restrictHalfSpace i R (translate (z.1 a) (reduce ω))))) =
      G (translate (z.1 (a + s) - z.1 a) (translate (z.1 a) (reduce ω))) :=
    eq_of_measurable_localSigma hG fun x hx =>
      translate_extend_eq_of_mem i R (translate (z.1 a) (reduce ω)) _ x
        (neg_two_mul_le_add_coord_of_norm_lt i x _ hx hvi)
  rw [hloc, reduce_translate_sub ω (z.1 (a + s)) (z.1 a)]

/-- The later-interval reward equals the pathwise factor of its record, whenever the cycle start is
finite and the shifted path does not backtrack. -/
theorem cycleReward_eq_regenFactor {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (D : (Regeneration.FutureHalfSpace d (forceCoord hd) (l / lam) → Mat d × ℝ) →
      C(Regeneration.FutureHalfSpace d (forceCoord hd) (l / lam), Mat d × ℝ))
    (hDr : ∀ f : C(Regeneration.FutureHalfSpace d (forceCoord hd) (l / lam), Mat d × ℝ),
      D (fun x => f x) = f)
    (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | euclideanNorm x < l / lam})
      inferInstance G)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d)
    (hfin : regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k ≠ ⊤)
    (hNB : NoBacktracking (l / lam)
      (pathTimeShift ωz.2.1
        (regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k).toNNReal)
      (forceCoord hd)) :
    cycleReward hd lam l G k ωz =
      regenFactor (regenDelta lam) lam (l / lam) (forceCoord hd) D G
        (cycleRecord hd lam l k ωz) := by
  have hlen : firstRegenerationTime (regenDelta lam) lam (l / lam)
      ((cycleRecord hd lam l k ωz).1, (cycleRecord hd lam l k ωz).2.1) (forceCoord hd) =
      firstRegenerationTime (regenDelta lam) lam (l / lam)
        (sampleTimeShift (regenDelta lam) ωz.2
          (regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k).toNNReal)
        (forceCoord hd) :=
    firstRegenerationTime_recenterSample (regenDelta lam) lam (l / lam) (forceCoord hd)
      (ωz.2.1 (regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k).toNNReal)
      (sampleTimeShift (regenDelta lam) ωz.2
        (regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k).toNNReal)
  unfold cycleReward regenFactor
  rw [regenerationTime_succ_eq (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k hfin,
    lintegral_regenInterval_shift_of_ne_top _ hfin, hlen]
  refine setLIntegral_congr_fun (measurableSet_regenInterval _ _) fun s hs => ?_
  have hs0 : 0 ≤ s := (mem_regenInterval.1 hs).1
  rw [reducedObservationAt_shift ωz.1 ωz.2.1 _ s hs0]
  exact (integrand_futureRecord_eq (regenDelta lam) (l / lam) (forceCoord hd) D hDr G hG
    ωz.1 ωz.2 _ s.toNNReal hNB).symm

/-- A later-interval reward is zero when its cycle start is infinite. -/
theorem cycleReward_eq_zero_of_top {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (G : FieldPair d → ℝ)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d)
    (htop : regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) k = ⊤) :
    cycleReward hd lam l G k ωz = 0 := by
  unfold cycleReward
  rw [htop, lintegral_regenInterval_top_eq_zero]

/-! ## The factorization theorem -/

/-- Step 2 of Proposition 3.2 (`paper/main.tex` lines 477–490): the record factorization of the
cycle reward. It is proved for `G` measurable for the local σ-algebra of `B_{l/λ}` and for
`0 < λ`. The factor is `regenFactor` at the decoder of the future half-space. -/
theorem cycleRewardFactors_of_localMeasurable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (hl0 : 0 < lam)
    (K : CoupledQuenchedLaws d) (G : FieldPair d → ℝ)
    (hG : @Measurable (FieldPair d) ℝ (localSigma {x : Vec d | euclideanNorm x < l / lam})
      inferInstance G) :
    CycleRewardFactors hd Q lam l K G := by
  obtain ⟨D, hD, hDr⟩ := Probability.exists_future_halfSpace_decoder (forceCoord hd) (l / lam)
  unfold CycleRewardFactors
  refine ⟨regenFactor (regenDelta lam) lam (l / lam) (forceCoord hd) D G,
    measurable_regenFactor (regenDelta lam) lam (l / lam) (forceCoord hd) D hD G hG, ?_, ?_⟩
  · intro k hk
    refine ae_of_all _ fun ωz => ?_
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    by_cases hτ : regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) (n + 1) = ⊤
    · rw [cycleReward_eq_zero_of_top hd lam l G (n + 1) ωz hτ]
      exact zero_le
    · have hNB := regenerationTime_succ_noBacktracking (regenDelta lam) (regenDelta_pos hl0) lam
        (l / lam) ωz.2 (forceCoord hd) n hτ
      exact le_of_eq (cycleReward_eq_regenFactor hd lam l D hDr G hG (n + 1) ωz hτ hNB)
  · refine ae_of_all _ fun ωz hωz => ?_
    have hD0 : NoBacktracking (l / lam) ωz.2.1 (forceCoord hd) := hωz
    have h0 : regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) 0 = 0 := rfl
    have hfin0 : regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) 0 ≠ ⊤ := by
      rw [h0]
      exact ENNReal.zero_ne_top
    have hNB0 : NoBacktracking (l / lam)
        (pathTimeShift ωz.2.1
          (regenerationTime (regenDelta lam) lam (l / lam) ωz.2 (forceCoord hd) 0).toNNReal)
        (forceCoord hd) := by
      rw [h0, ENNReal.toNNReal_zero]
      exact noBacktracking_pathTimeShift_zero (l / lam) (forceCoord hd) ωz.2.1 hD0
    exact le_of_eq (cycleReward_eq_regenFactor hd lam l D hDr G hG 0 ωz hfin0 hNB0).symm

end EinsteinRelation

end
