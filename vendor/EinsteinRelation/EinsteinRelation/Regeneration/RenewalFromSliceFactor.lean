import EinsteinRelation.Regeneration.RenewalConditionalInvariance
import EinsteinRelation.Regeneration.RenewalRecordIteration

/-!
# From deterministic slice factorization to all renewal marginals

Source `paper/main.tex:405–426`. The only paper-specific premise left in this
reduction is the exact slice factorization. It is an internal obligation,
not a literature input or a proof of Lemma 3.1 from frozen inputs.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Finite measures on any measurable space are determined by bounded real
measurable tests; no topology on the restricted-record carrier is needed. -/
theorem measure_eq_of_bounded_real_tests {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : α → ℝ, Measurable f → BoundedRealTest f → ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  classical
  apply Measure.ext
  intro s hs
  have ht := h (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
    ⟨1, fun x => by by_cases hx : x ∈ s <;> simp [hx]⟩
  simp only [integral_indicator hs, setIntegral_one_eq_measureReal, measureReal_def] at ht
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp ht

/-- The exact deterministic-slice identity of `paper/main.tex:405–409`.
This is a named internal proof obligation, not a permitted external input. -/
def FirstRegenerationSliceFactor {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) : Prop :=
  ∀ (Φ : FutureState d i R → ℝ), Measurable Φ → BoundedRealTest Φ →
    ∀ (m : ℕ) (H : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H →
      BoundedRealTest H →
      (∫ p in {p : FieldPair d × CoupledSample d |
          firstRegenerationTime Δ lam R p.2 i =
            ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        H p.2 * Φ (iteratedRecord Δ lam R i 1 p) ∂annealedCoupledLaw Q K) =
      (∫ p, Φ (iteratedRecord Δ lam R i 0 p)
        ∂ProbabilityTheory.cond (annealedCoupledLaw Q K) {p | NoBacktracking R p.2.1 i}) *
      ∫ p in {p : FieldPair d × CoupledSample d |
          firstRegenerationTime Δ lam R p.2 i =
            ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        H p.2 ∂annealedCoupledLaw Q K

/-- Source `paper/main.tex:409–426`: the slice factorization, first-time
finiteness and successful-bridge support imply every renewal marginal.
Finiteness of later times and conditional invariance are proved here.
The slice factorization remains an explicit internal premise. -/
theorem renewal_marginals_of_slice_factor {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfinite : ∀ᵐ p ∂annealedCoupledLaw Q K, firstRegenerationTime Δ lam R p.2 i ≠ ⊤)
    (hD : annealedCoupledLaw Q K {p | NoBacktracking R p.2.1 i} ≠ 0)
    (hslice : FirstRegenerationSliceFactor Q K Δ lam R i) :
    ∀ j : ℕ, (∀ᵐ p ∂annealedCoupledLaw Q K,
      regenerationTime Δ lam R p.2 i (j + 1) ≠ ⊤) ∧
      ∀ Φ : FutureState d i R → ℝ, Measurable Φ →
        (∫ p, Φ (iteratedRecord Δ lam R i (j + 1) p) ∂annealedCoupledLaw Q K) =
        ∫ p, Φ (iteratedRecord Δ lam R i 0 p)
          ∂ProbabilityTheory.cond (annealedCoupledLaw Q K) {p | NoBacktracking R p.2.1 i} := by
  let μ := annealedCoupledLaw Q K
  let κ := ProbabilityTheory.cond μ {p | NoBacktracking R p.2.1 i}
  let X := iteratedRecord Δ lam R i
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  haveI : IsProbabilityMeasure κ := ProbabilityTheory.cond_isProbabilityMeasure hD
  have hX : ∀ k, Measurable (X k) := measurable_iteratedRecord Δ lam R i
  have hfactors : ∀ Φ : FutureState d i R → ℝ, Measurable Φ → BoundedRealTest Φ →
      (∫ p, Φ (X 1 p) ∂μ) = ∫ p, Φ (X 0 p) ∂κ ∧
      (∫ p, Φ (X 1 p) ∂κ) = ∫ p, Φ (X 0 p) ∂κ := by
    intro Φ hΦ hb
    apply integral_and_condIntegral_of_first_factor Q K hK Δ hΔ lam R hlam hR i hsupport
      hfinite (fun p => Φ (X 1 p)) (hΦ.comp (hX 1)) ?_ _ (hslice Φ hΦ hb) hD
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun p => hC (X 1 p)⟩
  have hfirst : μ.map (X 1) = κ.map (X 0) := by
    apply measure_eq_of_bounded_real_tests
    intro Φ hΦ hb
    rw [integral_map (hX 1).aemeasurable hΦ.aestronglyMeasurable,
      integral_map (hX 0).aemeasurable hΦ.aestronglyMeasurable]
    exact (hfactors Φ hΦ hb).1
  have hcond : κ.map (X 1) = κ.map (X 0) := by
    apply measure_eq_of_bounded_real_tests
    intro Φ hΦ hb
    rw [integral_map (hX 1).aemeasurable hΦ.aestronglyMeasurable,
      integral_map (hX 0).aemeasurable hΦ.aestronglyMeasurable]
    exact (hfactors Φ hΦ hb).2
  have hgood : ∀ᵐ p ∂μ, RecordCanShift Δ lam R i (X 0 p) := by
    have hfwd := ae_firstRegenerationTime_forward Q K hK Δ hΔ lam R hlam hR i hsupport
    filter_upwards [hfinite, hfwd] with p hp hfw
    apply (recordCanShift_futureRecord_iff Δ lam R i p.1 p.2 0).mpr
    simpa only [sampleTimeShift_zero, zero_add] using And.intro hp (hfw hp)
  have hall := iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i μ κ
    ProbabilityTheory.cond_absolutelyContinuous hgood hfirst hcond
  intro j
  refine ⟨(hall j).1, ?_⟩
  intro Φ hΦ
  rw [← integral_map (hX (j + 1)).aemeasurable hΦ.aestronglyMeasurable,
    ← integral_map (hX 0).aemeasurable hΦ.aestronglyMeasurable, (hall j).2]


end EinsteinRelation.Regeneration
