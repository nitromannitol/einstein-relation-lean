import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness
import EinsteinFull.Calculus.U5RegularPhysicalOccupation
import EinsteinFull.Calculus.S4CountableSolvesSupport
import EinsteinRelation.Diffusion.StoppedPathLocality
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport

/-! Countable affine comparisons along the same supplied physical law. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

/-- A smooth test has the textbook generator at every point on the common
countable defect event where its gradient matches a locally affine coordinate
sum. All tests and affine coefficients are fixed before the event. -/
theorem u5_physical_countable_affine_gradient_comparison
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : ℕ → Vec d → ℝ) (A : ℕ → Fin d → Vec d → ℝ)
    (c : ℕ → Fin d → ℝ) (s : ℕ → Finset (Fin d))
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hA : ∀ n j, ContDiff ℝ (⊤ : ℕ∞) (A n j))
    (hcA : ∀ n j, HasCompactSupport (A n j)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ n : ℕ,
      (∀ j ∈ s n, A n j =ᶠ[𝓝 (γ u.toNNReal)] fun z => c n j * z j) →
      gradient (F n) (γ u.toNNReal) =
        gradient (fun y => ∑ j ∈ s n, A n j y) (γ u.toNNReal) →
      physicalGenerator i ω lam (F n) (γ u.toNNReal) =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (F n) (γ u.toNNReal) := by
  let G : ℕ → Vec d → ℝ := fun n y => ∑ j ∈ s n, A n j y
  have hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n) := by
    intro n
    exact ContDiff.sum fun j _ => hA n j
  have hscompact (n : ℕ) (t : Finset (Fin d)) :
      HasCompactSupport (fun y => ∑ j ∈ t, A n j y) := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, Pi.zero_def] using
        (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
    | @insert j t hj ih =>
      simpa only [Finset.sum_insert hj, Pi.add_def] using (hcA n j).add ih
  have hcG : ∀ n, HasCompactSupport (G n) := fun n => hscompact n (s n)
  have hcmp := c4_physical_countable_same_gradient_discrepancy_ae
    hΛ hω i lam hP F G hF hcF hG hcG
  have haff := c4_physical_countable_coordinate_sum_ae
    hΛ hω i lam hP A c hA hcA s
  filter_upwards [hcmp, haff] with γ hcmpγ haffγ
  filter_upwards [hcmpγ, haffγ] with u hcmpu haffu
  intro n hlocal hgradient
  have h := hcmpu n hgradient
  have hGval := haffu n hlocal
  change physicalGenerator i ω lam (G n) (γ u.toNNReal) =
    External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
      (G n) (γ u.toNNReal) at hGval
  rw [hGval, sub_self] at h
  exact sub_eq_zero.mp h


/-- Controlled approximations for a countable family share one event under
 the supplied physical law. The event is independent of the sequence index. -/
theorem u5_physical_countable_controlled_approximations_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (f : ℕ → Vec d → ℝ) (hf : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k))
    (hfc : ∀ k, HasCompactSupport (f k))
    (F : ℕ → ℕ → Vec d → ℝ)
    (hF : ∀ k n, ContDiff ℝ (⊤ : ℕ∞) (F k n))
    (hcF : ∀ k n, HasCompactSupport (F k n))
    (G : ℕ → ℕ → ℝ) (H : ℕ → ℕ → ℝ≥0)
    (hG0 : ∀ k n, 0 ≤ G k n)
    (hG : ∀ k n y j, |coordinateDerivative j (fun z => f k z - F k n z) y| ≤ G k n)
    (hH : ∀ k n j, LipschitzWith (H k n)
      (fun y => coordinateDerivative j (fun z => f k z - F k n z) y))
    (hGlim : ∀ k, Tendsto (G k) atTop (𝓝 0))
    (hHlim : ∀ k, Tendsto (fun n => (H k n : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ k,
      Tendsto (fun n => physicalGenerator i ω lam (F k n) (γ u.toNNReal))
        atTop (𝓝 (physicalGenerator i ω lam (f k) (γ u.toNNReal))) := by
  have h : ∀ᵐ γ ∂P, ∀ k, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Tendsto (fun n => physicalGenerator i ω lam (F k n) (γ u.toNNReal))
        atTop (𝓝 (physicalGenerator i ω lam (f k) (γ u.toNNReal))) := by
    apply ae_all_iff.mpr
    intro k
    exact c4_physical_generator_approximation_ae hΛ hω i lam hP (f k) (hf k)
      (hfc k) (F k) (hF k) (hcF k) (G k) (H k) (hG0 k) (hG k) (hH k)
      (hGlim k) (hHlim k)
  filter_upwards [h] with γ hγ
  exact ae_all_iff.mpr hγ


/-- On one event, the literal physical generator is additive over every finite
subset of a prescribed countable family of compactly supported smooth tests. -/
theorem u5_physical_countable_finite_sum_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : ℕ → Vec d → ℝ) (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ s : Finset ℕ,
      physicalGenerator i ω lam (fun y => ∑ n ∈ s, F n y) (γ u.toNNReal) =
        ∑ n ∈ s, physicalGenerator i ω lam (F n) (γ u.toNNReal) := by
  have hcompact (s : Finset ℕ) : HasCompactSupport (fun y => ∑ n ∈ s, F n y) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, Pi.zero_def] using
        (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
    | @insert n s hn ih =>
      simpa only [Finset.sum_insert hn, Pi.add_def] using (hcF n).add ih
  have heach (s : Finset ℕ) : ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      physicalGenerator i ω lam (fun y => ∑ n ∈ s, F n y) (γ u.toNNReal) =
        ∑ n ∈ s, physicalGenerator i ω lam (F n) (γ u.toNNReal) := by
    induction s using Finset.induction_on with
    | empty =>
      filter_upwards with γ
      filter_upwards with u
      simpa only [Finset.sum_empty, zero_mul] using
        c4_physical_generator_const_mul ω i lam 0 (F 0) (γ u.toNNReal)
    | @insert n s hn ih =>
      have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ j ∈ s, F j y) :=
        ContDiff.sum fun j _ => hF j
      filter_upwards [ih, c4_physical_additivity_defect_ae_zero hΛ hω i lam hP
        (hF n) (hcF n) hs (hcompact s)] with γ hγ hsum
      filter_upwards [hγ, hsum] with u hu hsumu
      simpa only [Finset.sum_insert hn, hu] using hsumu
  have h : ∀ᵐ γ ∂P, ∀ s : Finset ℕ, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      physicalGenerator i ω lam (fun y => ∑ n ∈ s, F n y) (γ u.toNNReal) =
        ∑ n ∈ s, physicalGenerator i ω lam (F n) (γ u.toNNReal) :=
    ae_all_iff.mpr heach
  filter_upwards [h] with γ hγ
  exact ae_all_iff.mpr hγ

/-- On a single supplied-law event, the literal generator is linear on all
finite rational combinations of a prescribed countable smooth test family. -/
theorem u5_physical_countable_rational_span_ae
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : ℕ → Vec d → ℝ) (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ c : ℕ →₀ ℚ,
      physicalGenerator i ω lam (fun y => ∑ n ∈ c.support, (c n : ℝ) * F n y)
          (γ u.toNNReal) =
        ∑ n ∈ c.support, (c n : ℝ) * physicalGenerator i ω lam (F n) (γ u.toNNReal) := by
  have heach (c : ℕ →₀ ℚ) : ∀ᵐ γ ∂P,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      physicalGenerator i ω lam (fun y => ∑ n ∈ c.support, (c n : ℝ) * F n y)
          (γ u.toNNReal) =
        ∑ n ∈ c.support, (c n : ℝ) * physicalGenerator i ω lam (F n) (γ u.toNNReal) := by
    have h := u5_physical_countable_finite_sum_ae hΛ hω i lam hP
      (fun n y => (c n : ℝ) * F n y)
      (fun n => contDiff_const.mul (hF n)) (fun n => (hcF n).mul_left)
    filter_upwards [h] with γ hγ
    filter_upwards [hγ] with u hu
    simpa only [c4_physical_generator_const_mul] using hu c.support
  have hall : ∀ᵐ γ ∂P, ∀ c : ℕ →₀ ℚ,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      physicalGenerator i ω lam (fun y => ∑ n ∈ c.support, (c n : ℝ) * F n y)
          (γ u.toNNReal) =
        ∑ n ∈ c.support, (c n : ℝ) * physicalGenerator i ω lam (F n) (γ u.toNNReal) :=
    ae_all_iff.mpr heach
  filter_upwards [hall] with γ hγ
  exact ae_all_iff.mpr hγ

/-- The rational-core generator identity integrates simultaneously over every
finite horizon along almost every path of the supplied law. -/
theorem u5_physical_countable_rational_span_integral_all_times
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : ℕ → Vec d → ℝ) (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n)) :
    ∀ᵐ γ ∂P, ∀ (c : ℕ →₀ ℚ) (t : ℝ≥0),
      (∫ u in (0 : ℝ)..(t : ℝ),
        physicalGenerator i ω lam (fun y => ∑ n ∈ c.support, (c n : ℝ) * F n y)
          (γ u.toNNReal)) =
        ∑ n ∈ c.support, (c n : ℝ) *
          (∫ u in (0 : ℝ)..(t : ℝ), physicalGenerator i ω lam (F n) (γ u.toNNReal)) := by
  filter_upwards [u5_physical_countable_rational_span_ae hΛ hω i lam hP F hF hcF] with γ hγ
  have hi (n : ℕ) (t : ℝ≥0) : IntervalIntegrable
      (fun u : ℝ => physicalGenerator i ω lam (F n) (γ u.toNNReal)) volume 0 t := by
    obtain ⟨C, hC⟩ := c4_bounded_physical_generator hΛ hω i lam (hF n) (hcF n)
    have hm : Measurable (fun u : ℝ => physicalGenerator i ω lam (F n) (γ u.toNNReal)) :=
      (c4_measurable_physical_generator ω i lam (F n)).comp
        (γ.continuous.comp continuous_real_toNNReal).measurable
    have hl : LocallyIntegrable
        (fun u : ℝ => physicalGenerator i ω lam (F n) (γ u.toNNReal)) volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      apply Measure.integrableOn_of_bounded hK.measure_lt_top.ne hm.aestronglyMeasurable
      exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using hC (γ u.toNNReal))
    exact (hl.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  intro c t
  have ht : Set.uIoc (0 : ℝ) (t : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    exact fun _ hu => hu.1
  have hzero := ae_restrict_of_ae_restrict_of_subset ht hγ
  calc
    (∫ u in (0 : ℝ)..(t : ℝ),
      physicalGenerator i ω lam (fun y => ∑ n ∈ c.support, (c n : ℝ) * F n y)
        (γ u.toNNReal)) =
      ∫ u in (0 : ℝ)..(t : ℝ),
        ∑ n ∈ c.support, (c n : ℝ) * physicalGenerator i ω lam (F n) (γ u.toNNReal) := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [hzero] with u hu
      exact hu c
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun n _ => (hi n t).const_mul (c n : ℝ))]
      simp only [intervalIntegral.integral_const_mul]

/-- The compensated tests are linear on the same rational core, for all
finite horizons simultaneously under the supplied law. -/
theorem u5_physical_countable_rational_span_compensated_all_times
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F : ℕ → Vec d → ℝ) (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n)) :
    ∀ᵐ γ ∂P, ∀ (c : ℕ →₀ ℚ) (t : ℝ≥0),
      compensatedTest (physicalGenerator i ω lam)
          (fun y => ∑ n ∈ c.support, (c n : ℝ) * F n y) t γ =
        ∑ n ∈ c.support, (c n : ℝ) *
          compensatedTest (physicalGenerator i ω lam) (F n) t γ := by
  filter_upwards [u5_physical_countable_rational_span_integral_all_times
    hΛ hω i lam hP F hF hcF] with γ hγ
  intro c t
  simp only [compensatedTest, hγ c t, ← Finset.sum_sub_distrib, ← mul_sub]

/-- An inverse clock preserves absolute continuity of averaged occupation for
any measure on paths. No martingale-problem identification is used. -/
theorem u5_inverse_clock_averaged_occupation_ac {d : ℕ} {Λ₀ : ℝ}
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (P : Measure (Path d))
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      ((P.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)).prod
        (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  let Φ : Path d → Path d := fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω
  have hΦ : Measurable Φ := measurable_timeChangeMap hω
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  intro N hnull
  let M := toMeasurable (volume : Measure (Vec d)) N
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hMnull : (volume : Measure (Vec d)) M = 0 := by simp [M, hnull]
  have hpaths := c16_ae_path_of_averaged_occupation P hocc
    (measure_eq_zero_iff_ae_notMem.mp hMnull)
  have htransport : ∀ᵐ γ ∂P, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Φ γ t.toNNReal ∉ M := by
    filter_upwards [hpaths] with γ hγ
    exact c4_inverse_clock_path_null_occupation hω γ hM hγ
  let B : Set (Path d × ℝ) := {z | z.1 z.2.toNNReal ∈ M}
  have hB : MeasurableSet B := hM.preimage heval
  have hsection : Measurable (fun γ : Path d =>
      (volume.restrict (Set.Ioi (0 : ℝ))) {t | γ t.toNNReal ∈ M}) :=
    measurable_measure_prodMk_left hB
  have hprop : MeasurableSet {γ : Path d |
      (volume.restrict (Set.Ioi (0 : ℝ))) {t | γ t.toNNReal ∈ M} = 0} :=
    measurableSet_eq_fun hsection measurable_const
  have hmap : ∀ᵐ γ ∂P.map Φ, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      γ t.toNNReal ∉ M := by
    have h := (ae_map_iff hΦ.aemeasurable hprop).2
      (htransport.mono fun γ hγ => measure_eq_zero_iff_ae_notMem.mpr hγ)
    exact h.mono fun γ hγ => measure_eq_zero_iff_ae_notMem.mp hγ
  apply measure_mono_null (subset_toMeasurable (volume : Measure (Vec d)) N)
  rw [Measure.map_apply heval hM]
  change (P.map Φ).prod (volume.restrict (Set.Ioi (0 : ℝ))) B = 0
  rw [Measure.prod_apply hB]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hmap] with γ hγ
  exact measure_eq_zero_iff_ae_notMem.mpr hγ

/-- A regular inverse clock and its inverse preserve exactly the same
averaged-occupation absolute-continuity property. -/
theorem u5_inverse_clock_averaged_occupation_ac_iff {d : ℕ} {Λ₀ : ℝ}
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (P : Measure (Path d)) :
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      ((P.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)).prod
        (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) ↔
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) := by
  refine ⟨?_, u5_inverse_clock_averaged_occupation_ac hω P⟩
  intro hocc
  let Φ : Path d → Path d := fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω
  let Q := P.map Φ
  have h := u5_inverse_clock_averaged_occupation_ac (isRegular_flipPotential hω) Q hocc
  have he : Q.map (fun γ => Clock.InverseMeaningV3.inverseClockPath
      (flipPotential ω) γ Λ₀ (isRegular_flipPotential hω)) = P := by
    change (P.map Φ).map (forwardClockPath hω) = P
    dsimp only [Φ]
    rw [Measure.map_map (measurable_forwardClockPath hω)
      (measurable_inverseClockPath_fixed ω Λ₀ hω)]
    have hid : (fun γ : Path d => forwardClockPath hω
        (Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)) = id := by
      funext γ
      exact forwardClockPath_inverseClockPath hω γ
    change P.map (fun γ => forwardClockPath hω
      (Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)) = P
    rw [hid, Measure.map_id]
  simpa only [he] using h


/-- The averaged occupation of a supplied law is absolutely continuous exactly
when that of its actual forward-clock image is. -/
theorem u5_forward_clock_averaged_occupation_ac_iff {d : ℕ} {Λ₀ : ℝ}
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (P : Measure (Path d)) :
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      ((P.map (forwardClockPath hω)).prod (volume.restrict (Set.Ioi 0))) ≪
        (volume : Measure (Vec d))) ↔
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) := by
  exact u5_inverse_clock_averaged_occupation_ac_iff (isRegular_flipPotential hω) P

/-- Every solution of the physical textbook problem has absolutely continuous
averaged occupation. The comparison law is obtained by clocking a reduced
textbook solution and identified by physical textbook well-posedness. -/
theorem u5_physical_textbook_averaged_occupation_ac {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x P) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  obtain ⟨R, hR, _⟩ := foundation_reduced_textbook_well_posed
    (by omega) hΛ hω i lam x
  letI : IsProbabilityMeasure R := hR.1
  have hRocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛ hω i lam hR
  have hactual := c16_reduced_solves_of_textbook_and_averaged_occupation
    hΛ hω i lam hR hRocc
  have hclock := c16_time_change_solves_of_regular hΛ hω i lam x hactual
  have hclockocc := u5_inverse_clock_averaged_occupation_ac hω R hRocc
  have hclocktext := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛ hω i lam hclock hclockocc
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hω i lam
  obtain ⟨S, _, huniq⟩ := foundation_textbook_well_posed d (by omega)
    (⇑ω.1) (physicalDrift ω i lam) hc hs hb he hm hbd x
  have heq := (huniq _ hP).trans (huniq _ hclocktext).symm
  rw [heq]
  exact hclockocc

/-- For the same supplied physical solution, the textbook martingale problem
is equivalent to absolute continuity of its averaged occupation. -/
theorem u5_physical_textbook_iff_occupation_ac {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x P ↔
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) :=
  ⟨u5_physical_textbook_averaged_occupation_ac hd hΛ hω i lam,
    c4_textbook_solves_of_physical_and_averaged_occupation hΛ hω i lam hP⟩

/-- A single measurable spatial null set, independent of the force, start and
supplied law, captures precisely the remaining occupation issue. Avoiding this
set in path-time is equivalent to full occupation absolute continuity for each
literal physical martingale-problem solution. -/
theorem u5_physical_occupation_iff_avoids_common_null_set {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) :
    ∃ N : Set (Vec d), MeasurableSet N ∧ (volume : Measure (Vec d)) N = 0 ∧
      ∀ (i : Fin d) (lam : ℝ) (x : Vec d) (P : Measure (Path d)),
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) ↔
          ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
            γ u.toNNReal ∉ N) := by
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (c4_physical_generator_ae_textbook hΛ hω))
  refine ⟨N, hNm, hNzero, ?_⟩
  intro i lam x P hP
  constructor
  · intro hocc
    have hp : ∀ᵐ y ∂(volume : Measure (Vec d)), y ∉ N := by
      apply ae_iff.mpr
      simpa only [not_not, Set.setOf_mem_eq] using hNzero
    exact c16_ae_path_of_averaged_occupation P hocc hp
  · intro havoid
    apply u5_physical_textbook_averaged_occupation_ac hd hΛ hω i lam
    refine c16_solves_of_ae_path_generator hP
      (fun f _ _ => c4_measurable_physical_textbook_generator hΛ hω i lam f) ?_
    intro f hf _ t
    filter_upwards [havoid] with γ hγ
    have hs : Set.uIoc (0 : ℝ) (t : ℝ) ⊆ Set.Ioi 0 := by
      rw [Set.uIoc_of_le t.coe_nonneg]
      exact fun _ hu => hu.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hγ] with u hu
    have hg : ∀ (i : Fin d) (lam : ℝ) (f : Vec d → ℝ),
        ContDiff ℝ 2 f → physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f (γ u.toNNReal) := by
      by_contra hn
      exact hu (hsub hn)
    exact hg i lam f (contDiff_two_of_top hf)

/-- It suffices to identify the generator along the supplied law for the fixed
countable textbook test family. The remaining tests are recovered from the
bounded-coefficient textbook martingale problem. -/
theorem u5_physical_occupation_ac_of_countable_generator_comparison {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hcompare : ∀ f ∈ tfam d, ∀ᵐ γ ∂P,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            f (γ u.toNNReal)) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  obtain ⟨hc, _, ⟨Ma, hMa⟩, _, hm, ⟨Mb, hMb⟩⟩ := physical_svHypotheses hΛ hω i lam
  have hb : BddCoef (⇑ω.1) (physicalDrift ω i lam) (max Ma Mb) :=
    ⟨fun j k => ((hc.matrix_elem j k).measurable),
      fun j => (measurable_pi_apply j).comp hm,
      fun y j k => (hMa y j k).trans (le_max_left _ _),
      fun y j => (hMb y j).trans (le_max_right _ _)⟩
  apply u5_physical_textbook_averaged_occupation_ac hd hΛ hω i lam
  apply solves_of_countableCond hb
  obtain ⟨hprob, hstart, hcond⟩ := countableCond_of_solves hP
  refine ⟨hprob, hstart, ?_⟩
  intro f hf S T hST B hB
  have he (t : ℝ≥0) : compensatedTest (physicalGenerator i ω lam) f t =ᵐ[P]
      compensatedTest (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) f t := by
    filter_upwards [hcompare f hf] with γ hγ
    have hs : Set.uIoc (0 : ℝ) (t : ℝ) ⊆ Set.Ioi 0 := by
      rw [Set.uIoc_of_le t.coe_nonneg]
      exact fun _ hu => hu.1
    unfold compensatedTest
    rw [intervalIntegral.integral_congr_ae_restrict
      (ae_restrict_of_ae_restrict_of_subset hs hγ)]
  have h := hcond f hf S T hST B hB
  have heT := he (MarkovProcess.DenseTime.castOrderEmbedding T)
  have heS := he (MarkovProcess.DenseTime.castOrderEmbedding S)
  apply (integral_congr_ae ?_).trans h
  filter_upwards [ae_restrict_of_ae heT, ae_restrict_of_ae heS] with γ hT hS
  rw [hT, hS]

/-- For a supplied solution, occupation absolute continuity is equivalent to
comparing its generator on the fixed countable textbook test family. -/
theorem u5_physical_occupation_ac_iff_countable_generator_comparison {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) ↔
    (∀ f ∈ tfam d, ∀ᵐ γ ∂P,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            f (γ u.toNNReal)) := by
  constructor
  · intro hocc f hf
    filter_upwards [c16_ae_path_of_averaged_occupation P hocc
      (c4_physical_generator_ae_textbook hΛ hω)] with γ hγ
    filter_upwards [hγ] with u hu
    exact hu i lam f (contDiff_two_of_top (tfam_test d f hf).1)
  · exact u5_physical_occupation_ac_of_countable_generator_comparison hd hΛ hω i lam hP

/-- A supplied solution spends no time in any prescribed countable set of
points at which compact smooth tests witness failure of generator additivity.
The witnesses may depend on the spatial point. -/
theorem u5_physical_supplied_law_avoids_countable_nonadditive_points
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {S : Set (Vec d)} (hS : S.Countable)
    (hbad : ∀ y ∈ S, ∃ f g : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      HasCompactSupport f ∧ HasCompactSupport g ∧
      physicalGenerator i ω lam (fun z => f z + g z) y ≠
        physicalGenerator i ω lam f y + physicalGenerator i ω lam g y) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      γ u.toNNReal ∉ S := by
  letI : Countable S := hS.to_subtype
  have h : ∀ᵐ γ ∂P, ∀ y : S,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), γ u.toNNReal ≠ (y : Vec d) := by
    apply ae_all_iff.mpr
    intro y
    obtain ⟨f, g, hf, hg, hfc, hgc, hne⟩ := hbad y y.property
    have he := c4_physical_additivity_defect_ae_zero hΛ hω i lam hP hf hfc hg hgc
    filter_upwards [he] with γ hγ
    filter_upwards [hγ] with u hu heq
    apply hne
    simpa only [heq] using hu
  filter_upwards [h] with γ hγ
  filter_upwards [ae_all_iff.mpr hγ] with u hu hmem
  exact hu ⟨γ u.toNNReal, hmem⟩ rfl

/-- At one regular environment and starting point, well-posedness of the
literal physical problem is equivalent to occupation absolute continuity for
every one of its solutions. -/
theorem u5_physical_well_posed_iff_occupation_ac {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) (x : Vec d) :
    (∃! P : Measure (Path d),
      SolvesMartingaleProblem (physicalGenerator i ω lam) x P) ↔
    (∀ P : Measure (Path d),
      SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
      Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) := by
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hω i lam
  obtain ⟨S, hS, huniq⟩ := foundation_textbook_well_posed d (by omega)
    (⇑ω.1) (physicalDrift ω i lam) hc hs hb he hm hbd x
  have hSocc := u5_physical_textbook_averaged_occupation_ac hd hΛ hω i lam hS
  have hSphys := c4_physical_solves_of_textbook_and_averaged_occupation
    hΛ hω i lam hS hSocc
  constructor
  · rintro ⟨R, hR, hRunique⟩ P hP
    have heq : P = S := (hRunique P hP).trans (hRunique S hSphys).symm
    simpa only [heq] using hSocc
  · intro hocc
    refine ⟨S, hSphys, ?_⟩
    intro P hP
    exact huniq P (c4_textbook_solves_of_physical_and_averaged_occupation
      hΛ hω i lam hP (hocc P hP))

/-- A countable collection of smooth tests cannot distinguish an atomless
distribution supported on the trap coefficient's nondifferentiability set
from zero generator values. The event depends on the chosen collection. -/
theorem u5_cantorTrap_countable_generator_ae_zero
    (μ : Measure ℝ) [NullSingletonClass μ]
    (F : ℕ → Vec 1 → ℝ) (hF : ∀ n, ContDiff ℝ 2 (F n))
    (ha : ∀ᵐ r ∂μ, ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∀ᵐ r ∂μ, ∀ n, physicalGenerator 0 c4CantorTrapField 0 (F n) (fun _ => r) = 0 := by
  apply ae_all_iff.mpr
  intro n
  exact c4_cantorTrapField_generator_ae_eq_zero μ (hF n) ha

/-- A law concentrated on nondifferentiability points of the Lipschitz trap
coefficient is singular with respect to Lebesgue measure. -/
theorem u5_cantorTrap_nondifferentiability_law_singular
    (μ : Measure ℝ)
    (ha : ∀ᵐ r ∂μ, ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    μ ⟂ₘ (volume : Measure ℝ) := by
  apply Measure.mutuallySingular_iff_disjoint_ae.mpr
  apply Filter.disjoint_of_disjoint_of_mem _ ha
    c4_cantorTrapCoefficient_lipschitz.ae_differentiableAt_real
  exact Set.disjoint_left.mpr (fun _ hnot hdiff => hnot hdiff)

private theorem u5_hasFDerivAt_mul_zero {d : ℕ} {c g : Vec d → ℝ}
    {g' : Vec d →L[ℝ] ℝ} {x : Vec d} (hc : ContinuousAt c x)
    (hg : HasFDerivAt g g' x) (hzero : g x = 0) :
    HasFDerivAt (fun y => c y * g y) (c x • g') x := by
  have hsmall : (fun y => c y - c x) =o[𝓝 x] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (by
      simpa only [sub_self] using hc.tendsto.sub_const (c x))
  have hbig : g =O[𝓝 x] (fun y => y - x) := by
    simpa only [hzero, sub_zero] using hg.isBigO_sub
  have hprod : (fun y => (c y - c x) * g y) =o[𝓝 x] (fun y => y - x) := by
    simpa only [smul_eq_mul, one_smul] using hsmall.smul_isBigO hbig
  apply HasFDerivAt.of_isLittleO
  convert hprod.add (hg.isLittleO.const_mul_left (c x)) using 1
  funext y
  simp only [smul_apply, smul_eq_mul, hzero]
  ring

/-- For each fixed smooth test, the trap generator can be nonzero at only
countably many nondifferentiability points of the coefficient. -/
theorem u5_cantorTrap_generator_nonzero_countable
    {f : Vec 1 → ℝ} (hf : ContDiff ℝ 2 f) :
    {r : ℝ | ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r ∧
      physicalGenerator 0 c4CantorTrapField 0 f (fun _ => r) ≠ 0}.Countable := by
  let g : Vec 1 → ℝ := fun y => coordinateDerivative 0 f y
  have hgc : ContDiff ℝ 1 g := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (le_of_eq one_add_one_eq_two)
    exact h1.clm_apply contDiff_const
  have hline (r : ℝ) :
      HasDerivAt (fun t : ℝ => fun _ : Fin 1 => t) (unitVector 0) r := by
    have heq : (fun t : ℝ => t • unitVector (d := 1) 0) =
        (fun t : ℝ => fun _ : Fin 1 => t) := by
      funext t j
      fin_cases j
      simp [unitVector]
    simpa only [id_eq, one_smul, heq] using
      (hasDerivAt_id r).smul_const (unitVector (d := 1) 0)
  have hscalar (r : ℝ) : HasDerivAt (fun t => g (fun _ => t))
      (fderiv ℝ g (fun _ => r) (unitVector 0)) r := by
    simpa only [Function.comp_def] using
      (hgc.differentiable one_ne_zero (fun _ => r)).hasFDerivAt.comp_hasDerivAt r (hline r)
  apply (c4_countable_nonflat_zeros (fun t => g (fun _ => t))).mono
  intro r hr
  have hz : g (fun _ => r) = 0 := by
    by_contra hz
    exact hr.2 (c4_cantorTrapField_generator_eq_zero hf
      (c4_cantorTrapCoefficient_not_differentiableAt_vec hr.1) hz)
  refine ⟨hz, (hscalar r).differentiableAt, ?_⟩
  intro hflat
  have hderiv : fderiv ℝ g (fun _ => r) (unitVector 0) = 0 := by
    rw [← (hscalar r).deriv]
    exact hflat
  have hp := u5_hasFDerivAt_mul_zero
    (c4_cantorTrapCoefficient_lipschitz.continuous.comp (continuous_apply 0)).continuousAt
    (hgc.differentiable one_ne_zero (fun _ => r)).hasFDerivAt hz
  have hflux :
      (fun y : Vec 1 => (reducedCoefficient c4CantorTrapField y).mulVec (gradient f y) 0) =
        fun y => c4CantorTrapCoefficient (y 0) * g y := by
    funext y
    simp [reducedCoefficient, clockDensity, c4CantorTrapField, ContinuousMap.coe_mk,
      Matrix.mulVec, dotProduct, gradient, g]
    exact Or.inl rfl
  apply hr.2
  simp only [physicalGenerator, zero_mul, add_zero, divergence, Fin.sum_univ_one]
  rw [hflux]
  change _ * (fderiv ℝ (fun y => c4CantorTrapCoefficient (y 0) * g y)
    (fun _ => r)) (unitVector 0) = 0
  have hp' : fderiv ℝ (fun y : Vec 1 => c4CantorTrapCoefficient (y 0) * g y)
      (fun _ => r) = c4CantorTrapCoefficient r • fderiv ℝ g (fun _ => r) := by
    simpa only [Function.comp_def] using hp.fderiv
  rw [hp']
  change _ * (c4CantorTrapCoefficient r * fderiv ℝ g (fun _ => r) (unitVector 0)) = 0
  rw [hderiv]
  simp

/-- A countable test family has one countable exceptional set, independent of
any chosen law on the coefficient's nondifferentiability points. -/
theorem u5_cantorTrap_countable_family_exceptions
    (F : ℕ → Vec 1 → ℝ) (hF : ∀ n, ContDiff ℝ 2 (F n)) :
    {r : ℝ | ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r ∧
      ∃ n, physicalGenerator 0 c4CantorTrapField 0 (F n) (fun _ => r) ≠ 0}.Countable := by
  have h : (⋃ n : ℕ, {r : ℝ | ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r ∧
      physicalGenerator 0 c4CantorTrapField 0 (F n) (fun _ => r) ≠ 0}).Countable :=
    Set.countable_iUnion fun n => u5_cantorTrap_generator_nonzero_countable (hF n)
  apply h.mono
  intro r hr
  obtain ⟨hn, n, hg⟩ := hr
  exact Set.mem_iUnion.mpr ⟨n, hn, hg⟩

/-- At every coefficient nondifferentiability point, the literal physical
operator fails additivity on two explicit smooth tests. -/
theorem u5_cantorTrap_generator_not_additive {r : ℝ}
    (hr : ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∃ f g : Vec 1 → ℝ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧
      physicalGenerator 0 c4CantorTrapField 0 (fun y => f y + g y) (fun _ => r) ≠
        physicalGenerator 0 c4CantorTrapField 0 f (fun _ => r) +
        physicalGenerator 0 c4CantorTrapField 0 g (fun _ => r) := by
  let l : Vec 1 → ℝ := fun y => y 0 - r
  let q : Vec 1 → ℝ := fun y => l y ^ 2
  have hl : ContDiff ℝ 2 l := (contDiff_apply ℝ ℝ 0).sub contDiff_const
  have hq : ContDiff ℝ 2 q := hl.pow 2
  have hdl (y : Vec 1) : fderiv ℝ l y = ContinuousLinearMap.proj 0 :=
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 y).sub_const r).fderiv
  have hqfirst (y : Vec 1) : coordinateDerivative 0 q y = 2 * l y := by
    unfold coordinateDerivative q
    rw [fderiv_fun_pow 2 (hl.differentiable (by norm_num) y), hdl]
    simp [unitVector, Pi.single_apply, mul_comm]
  have hlfirst (y : Vec 1) : coordinateDerivative 0 l y = 1 := by
    simp [coordinateDerivative, hdl, unitVector, Pi.single_apply]
  have hfirst : coordinateDerivative 0 (fun y => q y - l y) (fun _ => r) = -1 := by
    unfold coordinateDerivative
    change (fderiv ℝ (q - l) (fun _ => r)) (unitVector 0) = -1
    rw [fderiv_sub (hq.differentiable (by norm_num) _) (hl.differentiable (by norm_num) _)]
    change coordinateDerivative 0 q (fun _ => r) - coordinateDerivative 0 l (fun _ => r) = -1
    rw [hqfirst, hlfirst]
    simp [l]
  have ha := c4_cantorTrapCoefficient_not_differentiableAt_vec hr
  have hzero1 : physicalGenerator 0 c4CantorTrapField 0 l (fun _ => r) = 0 :=
    c4_cantorTrapField_generator_eq_zero hl ha (by rw [hlfirst]; norm_num)
  have hzero2 : physicalGenerator 0 c4CantorTrapField 0 (fun y => q y - l y) (fun _ => r) = 0 :=
    c4_cantorTrapField_generator_eq_zero (hq.sub hl) ha (by rw [hfirst]; norm_num)
  have hflux :
      (fun y : Vec 1 => (reducedCoefficient c4CantorTrapField y).mulVec (gradient q y) 0) =
        fun y => c4CantorTrapCoefficient (y 0) * (2 * l y) := by
    funext y
    simp [reducedCoefficient, clockDensity, c4CantorTrapField, ContinuousMap.coe_mk,
      Matrix.mulVec, dotProduct, gradient, hqfirst]
    exact Or.inl rfl
  have hp := u5_hasFDerivAt_mul_zero
    (c4_cantorTrapCoefficient_lipschitz.continuous.comp (continuous_apply 0)).continuousAt
    ((contDiff_const.mul hl).differentiable (by norm_num) (fun _ => r)).hasFDerivAt
    (by simp [l] : (fun y => 2 * l y) (fun _ => r) = 0)
  have hderiv : fderiv ℝ (fun y : Vec 1 => 2 * l y) (fun _ => r) (unitVector 0) = 2 := by
    rw [fderiv_const_mul (hl.differentiable (by norm_num) _) 2, hdl]
    simp [unitVector, Pi.single_apply]
  have hqgen : physicalGenerator 0 c4CantorTrapField 0 q (fun _ => r) =
      c4CantorTrapCoefficient r := by
    simp only [physicalGenerator, zero_mul, add_zero, divergence, Fin.sum_univ_one]
    rw [hflux]
    unfold coordinateDerivative
    simp only [Function.comp_def] at hp
    rw [hp.fderiv]
    simp [hderiv, clockDensity, c4CantorTrapField]
    ring
  refine ⟨l, fun y => q y - l y, hl, hq.sub hl, ?_⟩
  have he : (fun y => l y + (q y - l y)) = q := by funext y; ring
  rw [he, hqgen, hzero1, hzero2]
  have hb := (c4_cantorTrapCoefficient_bounds r).1
  linarith

/-- The regular trap field supplies an actual point of nonadditivity. -/
theorem u5_cantorTrap_generator_nonadditive_at_left :
    ∃ f g : Vec 1 → ℝ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧
      physicalGenerator 0 c4CantorTrapField 0 (fun y => f y + g y)
          (fun _ => (5 / 4 : ℝ)) ≠
        physicalGenerator 0 c4CantorTrapField 0 f (fun _ => (5 / 4 : ℝ)) +
        physicalGenerator 0 c4CantorTrapField 0 g (fun _ => (5 / 4 : ℝ)) :=
  u5_cantorTrap_generator_not_additive c4_cantorTrapCoefficient_not_differentiableAt_left


/-- The literal physical generator depends only on the germ of its test. -/
theorem u5_physicalGenerator_congr_nhds {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (lam : ℝ) {f g : Vec d → ℝ} {x : Vec d} (h : f =ᶠ[𝓝 x] g) :
    physicalGenerator i ω lam f x = physicalGenerator i ω lam g x := by
  have hg : gradient f =ᶠ[𝓝 x] gradient g := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    change (fun j => fderiv ℝ f y (unitVector j)) =
      (fun j => fderiv ℝ g y (unitVector j))
    rw [hy.fderiv_eq]
  have hgx : gradient f x = gradient g x := hg.self_of_nhds
  have hd : divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x =
      divergence (fun y => (reducedCoefficient ω y).mulVec (gradient g y)) x := by
    unfold divergence coordinateDerivative
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun y => (reducedCoefficient ω y).mulVec (gradient f y) j) =ᶠ[𝓝 x]
        (fun y => (reducedCoefficient ω y).mulVec (gradient g y) j) := by
      filter_upwards [hg] with y hy
      rw [hy]
    rw [he.fderiv_eq]
  simp only [physicalGenerator, hd, hgx]

/-- The polynomial witnesses are infinitely differentiable. -/
theorem u5_cantorTrap_generator_not_additive_smooth {r : ℝ}
    (hr : ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∃ f g : Vec 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      physicalGenerator 0 c4CantorTrapField 0 (fun y => f y + g y) (fun _ => r) ≠
        physicalGenerator 0 c4CantorTrapField 0 f (fun _ => r) +
        physicalGenerator 0 c4CantorTrapField 0 g (fun _ => r) := by
  let l : Vec 1 → ℝ := fun y => y 0 - r
  let q : Vec 1 → ℝ := fun y => l y ^ 2
  have hl : ContDiff ℝ (⊤ : ℕ∞) l := (contDiff_apply ℝ ℝ 0).sub contDiff_const
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := hl.pow 2
  have hdl (y : Vec 1) : fderiv ℝ l y = ContinuousLinearMap.proj 0 :=
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 y).sub_const r).fderiv
  have hqfirst (y : Vec 1) : coordinateDerivative 0 q y = 2 * l y := by
    unfold coordinateDerivative q
    rw [fderiv_fun_pow 2 (hl.differentiable (by norm_num) y), hdl]
    simp [unitVector, Pi.single_apply, mul_comm]
  have hlfirst (y : Vec 1) : coordinateDerivative 0 l y = 1 := by
    simp [coordinateDerivative, hdl, unitVector, Pi.single_apply]
  have hfirst : coordinateDerivative 0 (fun y => q y - l y) (fun _ => r) = -1 := by
    unfold coordinateDerivative
    change (fderiv ℝ (q - l) (fun _ => r)) (unitVector 0) = -1
    rw [fderiv_sub (hq.differentiable (by norm_num) _) (hl.differentiable (by norm_num) _)]
    change coordinateDerivative 0 q (fun _ => r) - coordinateDerivative 0 l (fun _ => r) = -1
    rw [hqfirst, hlfirst]
    simp [l]
  have ha := c4_cantorTrapCoefficient_not_differentiableAt_vec hr
  have hzero1 : physicalGenerator 0 c4CantorTrapField 0 l (fun _ => r) = 0 :=
    c4_cantorTrapField_generator_eq_zero (contDiff_two_of_top hl) ha (by rw [hlfirst]; norm_num)
  have hzero2 : physicalGenerator 0 c4CantorTrapField 0 (fun y => q y - l y) (fun _ => r) = 0 :=
    c4_cantorTrapField_generator_eq_zero (contDiff_two_of_top (hq.sub hl)) ha (by rw [hfirst]; norm_num)
  have hflux :
      (fun y : Vec 1 => (reducedCoefficient c4CantorTrapField y).mulVec (gradient q y) 0) =
        fun y => c4CantorTrapCoefficient (y 0) * (2 * l y) := by
    funext y
    simp [reducedCoefficient, clockDensity, c4CantorTrapField, ContinuousMap.coe_mk,
      Matrix.mulVec, dotProduct, gradient, hqfirst]
    exact Or.inl rfl
  have hp := u5_hasFDerivAt_mul_zero
    (c4_cantorTrapCoefficient_lipschitz.continuous.comp (continuous_apply 0)).continuousAt
    ((contDiff_const.mul hl).differentiable (by norm_num) (fun _ => r)).hasFDerivAt
    (by simp [l] : (fun y => 2 * l y) (fun _ => r) = 0)
  have hderiv : fderiv ℝ (fun y : Vec 1 => 2 * l y) (fun _ => r) (unitVector 0) = 2 := by
    rw [fderiv_const_mul (hl.differentiable (by norm_num) _) 2, hdl]
    simp [unitVector, Pi.single_apply]
  have hqgen : physicalGenerator 0 c4CantorTrapField 0 q (fun _ => r) =
      c4CantorTrapCoefficient r := by
    simp only [physicalGenerator, zero_mul, add_zero, divergence, Fin.sum_univ_one]
    rw [hflux]
    unfold coordinateDerivative
    simp only [Function.comp_def] at hp
    rw [hp.fderiv]
    simp [hderiv, clockDensity, c4CantorTrapField]
    ring
  refine ⟨l, fun y => q y - l y, hl, hq.sub hl, ?_⟩
  have he : (fun y => l y + (q y - l y)) = q := by funext y; ring
  rw [he, hqgen, hzero1, hzero2]
  have hb := (c4_cantorTrapCoefficient_bounds r).1
  linarith


/-- Nonadditivity persists after localizing both tests to compact support. -/
theorem u5_cantorTrap_generator_not_additive_compact {r : ℝ}
    (hr : ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∃ f g : Vec 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      HasCompactSupport f ∧ HasCompactSupport g ∧
      physicalGenerator 0 c4CantorTrapField 0 (fun y => f y + g y) (fun _ => r) ≠
        physicalGenerator 0 c4CantorTrapField 0 f (fun _ => r) +
        physicalGenerator 0 c4CantorTrapField 0 g (fun _ => r) := by
  obtain ⟨f, g, hf, hg, hne⟩ := u5_cantorTrap_generator_not_additive_smooth hr
  let x : Vec 1 := fun _ => r
  let b : ContDiffBump x := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : (fun y => b y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    apply b.one_of_mem_closedBall
    exact Metric.ball_subset_closedBall hy
  have hbf : (fun y => b y * f y) =ᶠ[𝓝 x] f := by
    filter_upwards [hb] with y hy
    simp [hy]
  have hbg : (fun y => b y * g y) =ᶠ[𝓝 x] g := by
    filter_upwards [hb] with y hy
    simp [hy]
  refine ⟨fun y => b y * f y, fun y => b y * g y,
    b.contDiff.mul hf, b.contDiff.mul hg, b.hasCompactSupport.mul_right,
    b.hasCompactSupport.mul_right, ?_⟩
  have hsum : (fun y => b y * f y + b y * g y) =ᶠ[𝓝 x] (fun y => f y + g y) :=
    hbf.add hbg
  rw [u5_physicalGenerator_congr_nhds 0 c4CantorTrapField 0 hsum,
    u5_physicalGenerator_congr_nhds 0 c4CantorTrapField 0 hbf,
    u5_physicalGenerator_congr_nhds 0 c4CantorTrapField 0 hbg]
  exact hne

/-- A supplied solution cannot spend positive time at any fixed cusp of the
trap coefficient. The exceptional time set may depend on the cusp. -/
theorem u5_cantorTrap_supplied_law_avoids_fixed_cusp
    {x : Vec 1} {P : Measure (Path 1)}
    (hP : SolvesMartingaleProblem (physicalGenerator 0 c4CantorTrapField 0) x P)
    {r : ℝ} (hr : ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      γ u.toNNReal ≠ (fun _ => r) := by
  obtain ⟨f, g, hf, hg, hfc, hgc, hne⟩ :=
    u5_cantorTrap_generator_not_additive_compact hr
  have h := c4_physical_additivity_defect_ae_zero (by norm_num : (0 : ℝ) < 2)
    c4_cantorTrapField_isRegular 0 0 hP hf hfc hg hgc
  filter_upwards [h] with γ hγ
  filter_upwards [hγ] with u hu heq
  apply hne
  simpa only [heq] using hu

/-- A supplied trap solution avoids any prescribed countable family of
coefficient cusps on one common path-time event. -/
theorem u5_cantorTrap_supplied_law_avoids_countable_cusps
    {x : Vec 1} {P : Measure (Path 1)}
    (hP : SolvesMartingaleProblem (physicalGenerator 0 c4CantorTrapField 0) x P)
    {S : Set ℝ} (hS : S.Countable)
    (hcusps : ∀ r ∈ S, ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ r ∈ S, γ u.toNNReal ≠ (fun _ => r) := by
  letI : Countable S := hS.to_subtype
  have h : ∀ᵐ γ ∂P, ∀ r : S,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        γ u.toNNReal ≠ (fun _ => (r : ℝ)) := by
    apply ae_all_iff.mpr
    intro r
    exact u5_cantorTrap_supplied_law_avoids_fixed_cusp hP (hcusps r r.property)
  filter_upwards [h] with γ hγ
  have htime := ae_all_iff.mpr hγ
  filter_upwards [htime] with u hu r hr
  exact hu ⟨r, hr⟩

/-- For any countable family of smooth tests, a supplied trap law sees zero
generator values at almost every time at which the coefficient has a cusp. -/
theorem u5_cantorTrap_supplied_law_countable_generator_ae_zero_on_cusps
    {x : Vec 1} {P : Measure (Path 1)}
    (hP : SolvesMartingaleProblem (physicalGenerator 0 c4CantorTrapField 0) x P)
    (F : ℕ → Vec 1 → ℝ) (hF : ∀ n, ContDiff ℝ 2 (F n)) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ¬ DifferentiableAt ℝ c4CantorTrapCoefficient (γ u.toNNReal 0) →
      ∀ n, physicalGenerator 0 c4CantorTrapField 0 (F n) (γ u.toNNReal) = 0 := by
  let S : Set ℝ := {r | ¬ DifferentiableAt ℝ c4CantorTrapCoefficient r ∧
    ∃ n, physicalGenerator 0 c4CantorTrapField 0 (F n) (fun _ => r) ≠ 0}
  have hS : S.Countable := u5_cantorTrap_countable_family_exceptions F hF
  have h := u5_cantorTrap_supplied_law_avoids_countable_cusps hP hS
    (fun _ hr => hr.1)
  filter_upwards [h] with γ hγ
  filter_upwards [hγ] with u hu hdiff n
  by_contra hn
  have heq : γ u.toNNReal = (fun _ => γ u.toNNReal 0) := by
    funext j
    fin_cases j
    rfl
  have hmem : γ u.toNNReal 0 ∈ S := ⟨hdiff, n, by simpa only [← heq] using hn⟩
  exact hu _ hmem heq


private theorem u5_lt_localityExitTime_iff {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) (T : ℝ≥0) :
    (T : ℝ≥0∞) < Diffusion.localityExitTime U γ ↔
      ∀ t : ℝ≥0, t ≤ T → γ t ∈ U := by
  constructor
  · intro h t ht
    by_contra hout
    have he : Diffusion.localityExitTime U γ ≤ (t : ℝ≥0∞) :=
      iInf_le_of_le t (iInf_le _ hout)
    exact (not_le_of_gt h) (he.trans (ENNReal.coe_le_coe.mpr ht))
  · exact Diffusion.lt_localityExitTime_of_stays U hU γ T

/-- Pointwise agreement of generators transfers along a path before its exit. -/
theorem u5_physical_compensator_before_exit_of_pointwise_agreement
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (γ : Path d) (t : ℝ≥0)
    (L L' : (Vec d → ℝ) → Vec d → ℝ)
    (hag : ∀ f x, x ∈ U → L f x = L' f x)
    (ht : (t : ℝ≥0∞) < Diffusion.localityExitTime U γ) (f : Vec d → ℝ) :
    L f (γ t) = L' f (γ t) := by
  exact hag f (γ t) ((u5_lt_localityExitTime_iff U hU γ t).mp ht t le_rfl)

/-- The compensator integrals agree up to any time strictly before exit. -/
theorem u5_physical_compensator_integral_before_exit_of_pointwise_agreement
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (γ : Path d) (t : ℝ≥0)
    (L L' : (Vec d → ℝ) → Vec d → ℝ)
    (hag : ∀ f x, x ∈ U → L f x = L' f x)
    (ht : (t : ℝ≥0∞) < Diffusion.localityExitTime U γ) (f : Vec d → ℝ) :
    (∫ s in (0 : ℝ)..(t : ℝ), L f (γ s.toNNReal)) =
      ∫ s in (0 : ℝ)..(t : ℝ), L' f (γ s.toNNReal) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hs
  apply hag
  apply (u5_lt_localityExitTime_iff U hU γ t).mp ht
  exact (Real.toNNReal_le_iff_le_coe).2 hs.2


/-- Under any supplied path law, the literal physical compensator agrees with
that of a pointwise-matching generator on paths surviving until the horizon. -/
theorem u5_physical_compensator_integral_supplied_law_before_exit
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (i : Fin d) (ω : FieldPair d) (lam : ℝ) (P : Measure (Path d))
    (L' : (Vec d → ℝ) → Vec d → ℝ)
    (hag : ∀ f x, x ∈ U → physicalGenerator i ω lam f x = L' f x)
    (f : Vec d → ℝ) :
    ∀ᵐ γ ∂P, (t : ℝ≥0∞) < Diffusion.localityExitTime U γ →
      (∫ s in (0 : ℝ)..(t : ℝ), physicalGenerator i ω lam f (γ s.toNNReal)) =
        ∫ s in (0 : ℝ)..(t : ℝ), L' f (γ s.toNNReal) := by
  exact ae_of_all P fun γ ht =>
    u5_physical_compensator_integral_before_exit_of_pointwise_agreement
      U hU γ t (physicalGenerator i ω lam) L' hag ht f

/-- Pointwise agreement also transfers through the bounded exit time. -/
theorem u5_compensator_integral_at_bounded_exit
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (γ : Path d) (T : ℝ≥0)
    (L L' : (Vec d → ℝ) → Vec d → ℝ)
    (hag : ∀ f x, x ∈ U → L f x = L' f x) (f : Vec d → ℝ) :
    let τ : ℝ := (min (T : ℝ≥0∞) (Diffusion.localityExitTime U γ)).toReal
    (∫ s in (0 : ℝ)..τ, L f (γ s.toNNReal)) =
      ∫ s in (0 : ℝ)..τ, L' f (γ s.toNNReal) := by
  let e : ℝ≥0∞ := min (T : ℝ≥0∞) (Diffusion.localityExitTime U γ)
  have he : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hτ : 0 ≤ e.toReal := ENNReal.toReal_nonneg
  change (∫ s in (0 : ℝ)..e.toReal, L f (γ s.toNNReal)) =
    ∫ s in (0 : ℝ)..e.toReal, L' f (γ s.toNNReal)
  apply intervalIntegral.integral_congr_Ioo_of_le hτ
  intro s hs
  apply hag
  have hlt : (s.toNNReal : ℝ≥0∞) < e := by
    rw [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_toReal he]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.1.le).2 hs.2
  have hexit : (s.toNNReal : ℝ≥0∞) < Diffusion.localityExitTime U γ :=
    hlt.trans_le (min_le_right _ _)
  exact (u5_lt_localityExitTime_iff U hU γ s.toNNReal).mp hexit _ le_rfl

/-- A path-dependent time, capped by a horizon and the exit time, transfers
the physical compensator under the same supplied law. No measurability of the
time is needed for this pathwise integral identity. -/
theorem u5_physical_compensator_integral_supplied_law_at_stopped_time
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0)
    (τ : Path d → ℝ≥0) (i : Fin d) (ω : FieldPair d) (lam : ℝ)
    (P : Measure (Path d)) (L' : (Vec d → ℝ) → Vec d → ℝ)
    (hag : ∀ f x, x ∈ U → physicalGenerator i ω lam f x = L' f x)
    (f : Vec d → ℝ) :
    ∀ᵐ γ ∂P,
      let σ : ℝ := (min ((min T (τ γ) : ℝ≥0) : ℝ≥0∞)
        (Diffusion.localityExitTime U γ)).toReal
      (∫ s in (0 : ℝ)..σ, physicalGenerator i ω lam f (γ s.toNNReal)) =
        ∫ s in (0 : ℝ)..σ, L' f (γ s.toNNReal) := by
  exact ae_of_all P fun γ =>
    u5_compensator_integral_at_bounded_exit U hU γ (min T (τ γ))
      (physicalGenerator i ω lam) L' hag f

/-- Locally matching physical fields have the same compensator through exit. -/
theorem u5_physical_compensator_integral_at_bounded_exit_of_field_agreement
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (γ : Path d) (T : ℝ≥0)
    (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    let τ : ℝ := (min (T : ℝ≥0∞) (Diffusion.localityExitTime U γ)).toReal
    (∫ s in (0 : ℝ)..τ, physicalGenerator i ω lam f (γ s.toNNReal)) =
      ∫ s in (0 : ℝ)..τ, physicalGenerator i ω' lam f (γ s.toNNReal) := by
  exact u5_compensator_integral_at_bounded_exit U hU γ T
    (physicalGenerator i ω lam) (physicalGenerator i ω' lam)
    (fun g x hx => physicalGenerator_eqOn_of_physical_eqOn U hU ω ω' heq i lam g hx) f

/-- Locally matching fields have equal stopped compensators under the same law. -/
theorem u5_physical_compensator_integral_supplied_law_at_stopped_time_of_field_agreement
    {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0)
    (τ : Path d → ℝ≥0) (ω ω' : FieldPair d)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (i : Fin d) (lam : ℝ) (P : Measure (Path d)) (f : Vec d → ℝ) :
    ∀ᵐ γ ∂P,
      let σ : ℝ := (min ((min T (τ γ) : ℝ≥0) : ℝ≥0∞)
        (Diffusion.localityExitTime U γ)).toReal
      (∫ s in (0 : ℝ)..σ, physicalGenerator i ω lam f (γ s.toNNReal)) =
        ∫ s in (0 : ℝ)..σ, physicalGenerator i ω' lam f (γ s.toNNReal) := by
  exact u5_physical_compensator_integral_supplied_law_at_stopped_time
    U hU T τ i ω lam P (physicalGenerator i ω' lam)
    (fun g x hx => physicalGenerator_eqOn_of_physical_eqOn U hU ω ω' heq i lam g hx) f

end EinsteinFull
