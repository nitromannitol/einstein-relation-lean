import EinsteinFull.Calculus.S4CountableBasicSupport

/-!
# The martingale problem as countably many conditions

For bounded measurable coefficients `A`, `b`, a probability measure `P` on path space solves the
martingale problem of `svGenerator A b` from `x` if and only if `CountableCond` holds: the start
is `x` and the compensated tests of the countable family `tfam d` satisfy
`∫_B (M_T - M_S) dP = 0` for rational `S ≤ T` and `B` in the countable π-system `cylSys d S`.
-/

open MeasureTheory Topology Filter
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- A chosen countable family dense in the compactly supported smooth test functions. -/
noncomputable def tfam (d : ℕ) : Set (Vec d → ℝ) := (exists_countable_testFamily d).choose

theorem tfam_countable (d : ℕ) : (tfam d).Countable :=
  (exists_countable_testFamily d).choose_spec.1

theorem tfam_test (d : ℕ) : ∀ f ∈ tfam d, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f :=
  (exists_countable_testFamily d).choose_spec.2.1

theorem tfam_dense (d : ℕ) :
    ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∃ (m : ℝ) (u : ℕ → Vec d → ℝ), (∀ k, u k ∈ tfam d) ∧ (∀ k, InH m (u k)) ∧
        (∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))) ∧
        (∀ j y, Tendsto (fun k => D1 (u k) j y) atTop (𝓝 (D1 f j y))) ∧
        ∀ i j y, Tendsto (fun k => D2 (u k) i j y) atTop (𝓝 (D2 f i j y)) :=
  (exists_countable_testFamily d).choose_spec.2.2

/-- A chosen countable cylinder pi-system at each dense deterministic time. -/
noncomputable def cylSys (d : ℕ) : MarkovProcess.DenseTime → Set (Set (Path d)) :=
  (exists_cylinder_piSystem d).choose

theorem cylSys_countable (d : ℕ) (S : MarkovProcess.DenseTime) : (cylSys d S).Countable :=
  (exists_cylinder_piSystem d).choose_spec.1 S

theorem cylSys_piSystem (d : ℕ) (S : MarkovProcess.DenseTime) : IsPiSystem (cylSys d S) :=
  (exists_cylinder_piSystem d).choose_spec.2.1 S

theorem cylSys_univ (d : ℕ) (S : MarkovProcess.DenseTime) : Set.univ ∈ cylSys d S :=
  (exists_cylinder_piSystem d).choose_spec.2.2.1 S

theorem cylSys_gen (d : ℕ) (S : MarkovProcess.DenseTime) :
    MeasurableSpace.generateFrom (cylSys d S) =
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)
        (MarkovProcess.DenseTime.castOrderEmbedding S) :=
  (exists_cylinder_piSystem d).choose_spec.2.2.2 S

/-- The countable conditions. -/
def CountableCond {d : ℕ} (L : (Vec d → ℝ) → Vec d → ℝ) (x : Vec d)
    (P : Measure (Path d)) : Prop :=
  IsProbabilityMeasure P ∧ (∀ᵐ γ ∂P, γ 0 = x) ∧
    ∀ u ∈ tfam d, ∀ S T : MarkovProcess.DenseTime, S ≤ T → ∀ B ∈ cylSys d S,
      ∫ γ in B, (compensatedTest L u (MarkovProcess.DenseTime.castOrderEmbedding T) γ -
        compensatedTest L u (MarkovProcess.DenseTime.castOrderEmbedding S) γ) ∂P = 0

theorem countableCond_of_solves {d : ℕ} {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d}
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem L x P) : CountableCond L x P := by
  obtain ⟨hprob, hstart, hf⟩ := hP
  refine ⟨hprob, hstart, ?_⟩
  intro u hu S T hST B hB
  obtain ⟨_, hint, hmart⟩ := hf u (tfam_test d u hu).1 (tfam_test d u hu).2
  rw [pathFiltration_eq_canonical] at hmart
  haveI := hprob
  have hBm : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)
      (MarkovProcess.DenseTime.castOrderEmbedding S)] B := by
    rw [← cylSys_gen d S]
    exact MeasurableSpace.measurableSet_generateFrom hB
  have hle : MarkovProcess.DenseTime.castOrderEmbedding S ≤
      MarkovProcess.DenseTime.castOrderEmbedding T :=
    MarkovProcess.DenseTime.castOrderEmbedding.monotone hST
  have e := hmart.setIntegral_eq hle hBm
  rw [integral_sub (hint _).integrableOn (hint _).integrableOn, e, sub_self]

theorem intervalIntegrable_path_of_bounded {d : ℕ} {g : Vec d → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ y, |g y| ≤ C) (γ : Path d) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => g (γ u.toNNReal)) volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun ?_ ?_
  · exact (hg.comp (γ.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    simp only [Real.norm_eq_abs]
    exact (hC _).trans (le_abs_self C)

theorem tendsto_compensatedTest_approx {d : ℕ} {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (h : BddCoef A b M) {f : Vec d → ℝ} {u : ℕ → Vec d → ℝ} {m : ℝ} (hu : ∀ k, InH m (u k))
    (hf0 : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y)))
    (h1 : ∀ j y, Tendsto (fun k => D1 (u k) j y) atTop (𝓝 (D1 f j y)))
    (h2 : ∀ i j y, Tendsto (fun k => D2 (u k) i j y) atTop (𝓝 (D2 f i j y)))
    (γ : Path d) (t : ℝ≥0) :
    Tendsto (fun k => compensatedTest (External.Draft.svGenerator A b) (u k) t γ) atTop
      (𝓝 (compensatedTest (External.Draft.svGenerator A b) f t γ)) := by
  unfold compensatedTest
  refine Tendsto.sub (Tendsto.sub (hf0 (γ t)) (hf0 (γ 0))) ?_
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 / 2 : ℝ) * (d * (d * (M * m))) + d * (M * m)) ?_ ?_ intervalIntegrable_const ?_
  · exact Filter.Eventually.of_forall fun k =>
      ((h.measurable_gen (u k)).comp
        (γ.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs]
      exact h.gen_bound (hu k) _
  · exact Filter.Eventually.of_forall fun s _ => h.gen_tendsto h1 h2 _

theorem tendsto_setIntegral_compensated {d : ℕ} {A : Vec d → Mat d} {b : Vec d → Vec d}
    {M : ℝ} (h : BddCoef A b M) {f : Vec d → ℝ} {u : ℕ → Vec d → ℝ} {m : ℝ}
    (hu : ∀ k, InH m (u k)) (hf0 : ∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y)))
    (h1 : ∀ j y, Tendsto (fun k => D1 (u k) j y) atTop (𝓝 (D1 f j y)))
    (h2 : ∀ i j y, Tendsto (fun k => D2 (u k) i j y) atTop (𝓝 (D2 f i j y)))
    (P : Measure (Path d)) [IsProbabilityMeasure P] {B : Set (Path d)} (S T : ℝ≥0) :
    Tendsto (fun k => ∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) (u k) T γ -
        compensatedTest (External.Draft.svGenerator A b) (u k) S γ) ∂P) atTop
      (𝓝 (∫ γ in B, (compensatedTest (External.Draft.svGenerator A b) f T γ -
        compensatedTest (External.Draft.svGenerator A b) f S γ) ∂P)) := by
  have hmeas : ∀ (k : ℕ) (t : ℝ≥0), StronglyMeasurable
      (compensatedTest (External.Draft.svGenerator A b) (u k) t) := fun k t =>
    ((stronglyAdapted_compensatedTest_of_measurable (External.Draft.svGenerator A b) (u k)
      (hu k).1.1.continuous (h.measurable_gen (u k))) t).mono ((pathFiltration d).le t)
  refine tendsto_integral_of_dominated_convergence
    (fun _ => (2 * m + ((1 / 2 : ℝ) * (d * (d * (M * m))) + d * (M * m)) * T) +
      (2 * m + ((1 / 2 : ℝ) * (d * (d * (M * m))) + d * (M * m)) * S)) ?_
    (integrable_const _) ?_ ?_
  · exact fun k => ((hmeas k T).sub (hmeas k S)).aestronglyMeasurable
  · intro k
    refine Filter.Eventually.of_forall fun γ => ?_
    have hT := norm_compensatedTest_le (External.Draft.svGenerator A b) (u k)
      (fun y => (hu k).2.1.1 y) (fun y => h.gen_bound (hu k) y) T γ
    have hS := norm_compensatedTest_le (External.Draft.svGenerator A b) (u k)
      (fun y => (hu k).2.1.1 y) (fun y => h.gen_bound (hu k) y) S γ
    have h3 := norm_sub_le (compensatedTest (External.Draft.svGenerator A b) (u k) T γ)
      (compensatedTest (External.Draft.svGenerator A b) (u k) S γ)
    linarith
  · exact Filter.Eventually.of_forall fun γ =>
      (tendsto_compensatedTest_approx h hu hf0 h1 h2 γ T).sub
        (tendsto_compensatedTest_approx h hu hf0 h1 h2 γ S)

end EinsteinFull
