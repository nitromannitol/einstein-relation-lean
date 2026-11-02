import EinsteinRelation.Correctors.StationaryMaximalTransference
import EinsteinRelation.Correctors.CubeMaximalWeakBound
import Mathlib.MeasureTheory.Group.Integral

/-!
# Stationary weak maximal bounds for spatial gradient errors

Source: `paper/main.tex:693-698`. A deterministic localization estimate,
stationarity, and increasing unions control all integer cube radii on the
same event. No ergodicity or independence is used in this transfer.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- Transfer a finite-radius deterministic localization estimate to all
integer radii under the stationary environment law. -/
theorem stationary_integerCube_maximal_of_localization (d : ℕ) (C : ℝ) (hC : 0 < C)
    (hlocal : ∀ (f : Vec d → ℝ), (∀ x, 0 ≤ f x) → ∀ (N : ℕ) (R t : ℝ),
      0 < R → 0 < t → IntegrableOn f (Metric.closedBall 0 (R + (N : ℝ) + 1)) volume →
      volume {x | x ∈ Metric.closedBall (0 : Vec d) R ∧
        ∃ n : ℕ, n < N ∧
          t * volume.real (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) <
            ∫ y in Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), f (y + x) ∂volume} ≤
        ENNReal.ofReal (C / t * ∫ y in Metric.closedBall 0 (R + (N : ℝ) + 1), f y ∂volume))
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : FieldPair d → ℝ) (hf : Measurable f) (hi : Integrable f Q)
    (hnonneg : ∀ ω, 0 ≤ f ω) (t : ℝ) (ht : 0 < t) :
    Q {ω | ∃ n : ℕ, t * volume.real (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) <
      ∫ x in Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), f (translate x ω) ∂volume} ≤
      ENNReal.ofReal (C / t * ∫ ω, f ω ∂Q) := by
  let B := fun n : ℕ => Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  let s := fun N : ℕ => {ω : FieldPair d | ∃ n : ℕ, n < N ∧
    t * volume.real (B n) < ∫ x in B n, f (translate x ω) ∂volume}
  have hm (n : ℕ) : Measurable (fun ω : FieldPair d =>
      ∫ x in B n, f (translate x ω) ∂volume) := by
    have h : StronglyMeasurable (fun p : FieldPair d × Vec d => f (translate p.2 p.1)) :=
      (hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_fst))).stronglyMeasurable
    exact h.integral_prod_right'.measurable
  have hs (N : ℕ) : MeasurableSet (s N) := by
    simp only [s, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : n < N
    · simpa only [hn, true_and] using measurableSet_lt
        (measurable_const : Measurable fun _ : FieldPair d => t * volume.real (B n)) (hm n)
    · simp only [hn, false_and, Set.setOf_false, MeasurableSet.empty]
  have hbound (N : ℕ) : Q.real (s N) ≤ C / t * ∫ ω, f ω ∂Q := by
    apply probability_le_of_spatial_localization Q hQ f hf hi (s N) (hs N)
      (C / t) ((N : ℝ) + 1)
    intro R hR
    let K := Metric.closedBall (0 : Vec d) (R + (N : ℝ) + 1)
    letI : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_ne_top
    have hiK := (stationary_spatial_integral Q hQ (volume.restrict K) f hf hi).1
    filter_upwards [hiK.prod_left_ae] with ω hω
    have hb := hlocal (fun x => f (translate x ω)) (fun x => hnonneg _) N R t hR ht hω
    have heq : {x : Vec d | x ∈ Metric.closedBall 0 R ∧
        ∃ n : ℕ, n < N ∧ t * volume.real (B n) <
          ∫ y in B n, f (translate (y + x) ω) ∂volume} =
        Metric.closedBall 0 R ∩ (fun x => translate x ω) ⁻¹' s N := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, s, B, translate_add]
    change volume {x : Vec d | x ∈ Metric.closedBall 0 R ∧
      ∃ n : ℕ, n < N ∧ t * volume.real (B n) <
        ∫ y in B n, f (translate (y + x) ω) ∂volume} ≤ _ at hb
    rw [heq] at hb
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (mul_nonneg (div_nonneg hC.le ht.le)
      (integral_nonneg fun _ => hnonneg _))] at hreal
    have hp : MeasurableSet ((fun x => translate x ω) ⁻¹' s N) :=
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const)) (hs N)
    have hind : (∫ x in Metric.closedBall (0 : Vec d) R,
        (s N).indicator (fun _ => (1 : ℝ)) (translate x ω) ∂volume) =
        volume.real (Metric.closedBall (0 : Vec d) R ∩
          (fun x => translate x ω) ⁻¹' s N) := by
      have hfun : (fun x => (s N).indicator (fun _ => (1 : ℝ)) (translate x ω)) =
          ((fun x => translate x ω) ⁻¹' s N).indicator (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hx : translate x ω ∈ s N <;> simp [hx]
      rw [hfun, setIntegral_indicator hp]
      simp [Measure.real]
    rw [hind]
    simpa only [K, add_assoc, Measure.real] using hreal
  have hmeasure (N : ℕ) : Q (s N) ≤ ENNReal.ofReal (C / t * ∫ ω, f ω ∂Q) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q (s N))]
    exact ENNReal.ofReal_le_ofReal (hbound N)
  have hmono : Monotone s := by
    intro N M hNM ω hω
    obtain ⟨n, hn, hb⟩ := hω
    exact ⟨n, hn.trans_le hNM, hb⟩
  have hevent : {ω | ∃ n : ℕ, t * volume.real (B n) <
      ∫ x in B n, f (translate x ω) ∂volume} = ⋃ N, s N := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, s]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n + 1, n, Nat.lt_succ_self n, hn⟩
    · rintro ⟨N, n, _, hn⟩
      exact ⟨n, hn⟩
  change Q {ω | ∃ n : ℕ, t * volume.real (B n) <
    ∫ x in B n, f (translate x ω) ∂volume} ≤ _
  rw [hevent, hmono.measure_iUnion]
  exact iSup_le hmeasure

end EinsteinRelation.Correctors
