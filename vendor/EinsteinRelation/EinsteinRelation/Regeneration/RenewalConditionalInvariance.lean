import EinsteinRelation.Regeneration.NoBacktrackingPrefix
import EinsteinRelation.Regeneration.FirstRegenerationFiniteness
import EinsteinRelation.Regeneration.CycleRecordMeasurability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ConditionalProbability

/-!
# Summing the first-regeneration factorization

Source `paper/main.tex:405–425`. The factorization on each deterministic
slice implies both the first-record identity and conditional invariance.
The factorization itself remains a separate internal proof obligation.
-/

open MeasureTheory Function
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Summation over a countable measurable partition of full measure, as used
for the regeneration slices in `paper/main.tex:409–425`. -/
theorem integral_eq_of_slice_integrals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (Disjoint on s)) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ n, s n)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (a : ℝ)
    (h : ∀ n, (∫ x in s n, f x ∂μ) = a * ∫ x in s n, g x ∂μ) :
    (∫ x, f x ∂μ) = a * ∫ x, g x ∂μ := by
  have hfull : (⋃ n, s n) =ᵐ[μ] Set.univ := by
    filter_upwards [hcover] with x hx
    exact propext ⟨fun _ => Set.mem_univ x, fun _ => hx⟩
  have hfSum := hasSum_integral_iUnion hs hdisj hf.integrableOn
  have hgSum := hasSum_integral_iUnion hs hdisj hg.integrableOn
  have heq : (∫ x in ⋃ n, s n, f x ∂μ) = a * ∫ x in ⋃ n, s n, g x ∂μ := by
    apply HasSum.unique hfSum
    simpa only [← h] using hgSum.mul_left a
  simpa only [setIntegral_congr_set hfull, Measure.restrict_univ] using heq

/-- The positive grid slices of the first regeneration time are pairwise
disjoint (`paper/main.tex:353–364,409–411`). -/
theorem pairwise_disjoint_firstRegenerationSlices {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d) :
    Pairwise (Disjoint on fun m : ℕ =>
      {ωz : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R ωz.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro ωz hm hn
  have heq : ((m + 1 : ℕ) : ℝ≥0) * Δ = ((n + 1 : ℕ) : ℝ≥0) * Δ :=
    ENNReal.coe_inj.mp (hm.symm.trans hn)
  have hcast := mul_right_cancel₀ hΔ.ne' heq
  have hnat : m + 1 = n + 1 := by exact_mod_cast hcast
  exact hmn (Nat.add_right_cancel hnat)

/-- Source `paper/main.tex:405–425`: if the bounded functional `f` satisfies
the first-factor identity against every exact-past test on each regeneration
slice, then its annealed expectation and its expectation conditioned on
no-backtracking both equal the same constant `a`.

The slice factorization is an internal premise, not a cited external input.
The conditional part uses the proved barrier identity and successful-bridge
support of the actual coupling.
-/
theorem integral_and_condIntegral_of_first_factor {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam R ωz.2 i ≠ ⊤)
    (f : FieldPair d × CoupledSample d → ℝ) (hf : Measurable f)
    (hb : BoundedRealTest f) (a : ℝ)
    (hslice : ∀ (m : ℕ) (H : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H →
      BoundedRealTest H →
      (∫ ωz in {ωz : FieldPair d × CoupledSample d |
          firstRegenerationTime Δ lam R ωz.2 i =
            ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        H ωz.2 * f ωz ∂annealedCoupledLaw Q K) =
      a * ∫ ωz in {ωz : FieldPair d × CoupledSample d |
          firstRegenerationTime Δ lam R ωz.2 i =
            ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        H ωz.2 ∂annealedCoupledLaw Q K)
    (hD : annealedCoupledLaw Q K {ωz | NoBacktracking R ωz.2.1 i} ≠ 0) :
    (∫ ωz, f ωz ∂annealedCoupledLaw Q K) = a ∧
      (∫ ωz, f ωz ∂ProbabilityTheory.cond (annealedCoupledLaw Q K)
        {ωz | NoBacktracking R ωz.2.1 i}) = a := by
  classical
  let μ := annealedCoupledLaw Q K
  let D : Set (FieldPair d × CoupledSample d) := {ωz | NoBacktracking R ωz.2.1 i}
  let s : ℕ → Set (FieldPair d × CoupledSample d) := fun m =>
    {ωz | firstRegenerationTime Δ lam R ωz.2 i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hDm : MeasurableSet D :=
    (measurableSet_NoBacktracking R i).preimage measurable_snd.fst
  have hsm : ∀ m, MeasurableSet (s m) := fun m =>
    measurableSet_eq_fun ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd)
      measurable_const
  have hdisj : Pairwise (Disjoint on s) :=
    pairwise_disjoint_firstRegenerationSlices Δ hΔ lam R i
  have hcover : ∀ᵐ ωz ∂μ, ωz ∈ ⋃ m, s m := by
    filter_upwards [hfinite] with ωz hωz
    obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R ωz.2 i hωz
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  obtain ⟨C, hC⟩ := hb
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ωz => by rw [Real.norm_eq_abs]; exact hC ωz)
  have hfirst : (∫ ωz, f ωz ∂μ) = a := by
    have h := integral_eq_of_slice_integrals μ s hsm hdisj hcover f (fun _ => 1) hfi
      (integrable_const 1) a (fun m => by
        simpa only [one_mul] using hslice m (fun _ => 1) measurable_const
          ⟨1, fun _ => by norm_num⟩)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul,
      mul_one] using h
  have hrestrict : (∫ ωz in D, f ωz ∂μ) = a * (μ D).toReal := by
    have hsum := integral_eq_of_slice_integrals μ s hsm hdisj hcover
      (D.indicator f) (D.indicator (fun _ => 1))
      (hfi.indicator hDm) ((integrable_const (1 : ℝ)).indicator hDm) a ?_
    · simpa only [integral_indicator hDm, setIntegral_one_eq_measureReal, measureReal_def]
        using hsum
    intro m
    let E : Set (CoupledSample d) :=
      {z | ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i}
    have hEm : @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ m) E :=
      measurableSet_noBacktracking_prefix Δ m R i
    have hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance
        (E.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hEm
    have hHb : BoundedRealTest (E.indicator (fun _ => (1 : ℝ))) :=
      ⟨1, fun z => by by_cases hz : z ∈ E <;> simp [hz]⟩
    have hDeq : ∀ᵐ ωz ∂μ.restrict (s m), ωz ∈ D ↔ ωz.2 ∈ E := by
      have hid := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q K hK Δ hΔ
        lam R hlam hR i m hsupport
      filter_upwards [ae_restrict_of_ae hid, ae_restrict_mem (hsm m)] with ωz hid hωz
      exact hid hωz
    have hF : (∫ ωz in s m, D.indicator f ωz ∂μ) =
        ∫ ωz in s m, E.indicator (fun _ => (1 : ℝ)) ωz.2 * f ωz ∂μ := by
      apply integral_congr_ae
      filter_upwards [hDeq] with ωz hωz
      by_cases hmem : ωz ∈ D
      · simp [hmem, hωz.mp hmem]
      · simp [hmem, mt hωz.mpr hmem]
    have hOne : (∫ ωz in s m, D.indicator (fun _ => (1 : ℝ)) ωz ∂μ) =
        ∫ ωz in s m, E.indicator (fun _ => (1 : ℝ)) ωz.2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hDeq] with ωz hωz
      by_cases hmem : ωz ∈ D
      · simp [hmem, hωz.mp hmem]
      · simp [hmem, mt hωz.mpr hmem]
    rw [hF, hOne]
    exact hslice m (E.indicator (fun _ => 1)) hH hHb
  refine ⟨hfirst, ?_⟩
  change (∫ ωz, f ωz ∂((μ D)⁻¹ • μ.restrict D)) = a
  rw [integral_smul_measure, hrestrict, ENNReal.toReal_inv, smul_eq_mul]
  have hmass : (μ D).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hD, measure_ne_top μ D⟩
  field_simp


end EinsteinRelation.Regeneration
