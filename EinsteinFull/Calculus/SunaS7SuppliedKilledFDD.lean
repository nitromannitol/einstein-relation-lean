import EinsteinFull.Calculus.SunaS7KilledKernelLocality
import EinsteinFull.Calculus.U1RegularKernelContinuity
import EinsteinFull.Calculus.SunaS2Pathwise
import EinsteinFull.Work.W1.GMPKilledEndpointSupport
import Mathlib.Tactic.Linter

open MeasureTheory ProbabilityTheory
open EinsteinRelation EinsteinRelation.Diffusion
open scoped NNReal ENNReal

namespace EinsteinFull

/-- Killed transition kernel constructed from the supplied continuous path law. -/
noncomputable def s7SuppliedKilledKernel {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) : Kernel (Vec d) (Vec d) :=
  Kernel.map (Q.restrict (MarkovProcess.ContinuousPath.measurableSet_lt_exitTime U hU t))
    (fun γ : Path d => γ t)

/-- The supplied killed kernel is the actual strict-survival marginal. -/
theorem s7SuppliedKilledKernel_apply {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d)
    {A : Set (Vec d)} (hA : MeasurableSet A) :
    s7SuppliedKilledKernel Q U hU t x A =
      Q x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} := by
  have hm : Measurable (fun γ : Path d => γ t) :=
    MarkovProcess.ContinuousPath.measurable_coordinateProcess t
  rw [s7SuppliedKilledKernel, Kernel.map_apply _ hm, Kernel.restrict_apply,
    Measure.map_apply hm hA, Measure.restrict_apply (hm hA)]
  congr 1
  ext γ
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
    s7_localityExitTime_eq]
  tauto

/-- Equality of actual killed marginals gives equality of supplied killed kernels
at every start in the domain. -/
theorem s7SuppliedKilledKernel_eq_of_marginals {d : ℕ}
    (Q R : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (hpart : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U → ∀ A : Set (Vec d), MeasurableSet A →
      Q x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} =
      R x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A}) :
    ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      s7SuppliedKilledKernel Q U hU t x = s7SuppliedKilledKernel R U hU t x := by
  intro t x hx
  apply Measure.ext
  intro A hA
  rw [s7SuppliedKilledKernel_apply Q U hU t x hA,
    s7SuppliedKilledKernel_apply R U hU t x hA]
  exact hpart t x hx A hA


/-- The stopped history generates the canonical filtration at its terminal time. -/
theorem s7_comap_stoppedHistory_eq_canonicalFiltration {d : ℕ} (s : ℝ≥0) :
    MeasurableSpace.comap (fun γ : Path d => fun t : ℝ≥0 => γ (min t s))
      inferInstance = MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s := by
  change MeasurableSpace.comap (fun γ : Path d => fun t : ℝ≥0 => γ (min t s))
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun f : ℝ≥0 → Vec d => f t) inferInstance) = _
  rw [MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp]
  apply le_antisymm
  · apply iSup_le
    intro t
    change MeasurableSpace.comap (MarkovProcess.ContinuousPath.coordinateProcess (min t s))
      inferInstance ≤ _
    exact le_iSup_of_le (⟨min t s, min_le_right t s⟩ : Set.Iic s) le_rfl
  · change (⨆ t : Set.Iic s, MeasurableSpace.comap
        (MarkovProcess.ContinuousPath.coordinateProcess (t : ℝ≥0)) inferInstance) ≤ _
    apply iSup_le
    intro t
    have h := le_iSup (fun u : ℝ≥0 => MeasurableSpace.comap
      (fun γ : Path d => γ (min u s)) inferInstance) (t : ℝ≥0)
    have ht : (t : ℝ≥0) ≤ s := t.property
    change MeasurableSpace.comap (fun γ : Path d => γ (t : ℝ≥0)) inferInstance ≤ _
    simpa only [min_eq_left ht, Function.comp_def] using h

/-- Every canonical past event is the pullback of a measurable stopped-history event. -/
theorem s7_past_event_stoppedHistory_factor {d : ℕ} (s : ℝ≥0) (A : Set (Path d))
    (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] A) :
    ∃ B : Set (ℝ≥0 → Vec d), MeasurableSet B ∧
      (fun γ : Path d => fun t : ℝ≥0 => γ (min t s)) ⁻¹' B = A := by
  apply MeasurableSpace.measurableSet_comap.mp
  rwa [s7_comap_stoppedHistory_eq_canonicalFiltration]

/-- Survival to a deterministic time is a measurable predicate of the stopped history. -/
theorem s7_survival_stoppedHistory_factor {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ≥0) : ∃ B : Set (ℝ≥0 → Vec d), MeasurableSet B ∧
      (fun γ : Path d => fun t : ℝ≥0 => γ (min t s)) ⁻¹' B =
        {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} := by
  apply MeasurableSpace.measurableSet_comap.mp
  rw [s7_comap_stoppedHistory_eq_canonicalFiltration]
  simpa only [s7_localityExitTime_eq] using
    (MarkovProcess.ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU s)

/-- Restart holds after restriction to any event in the canonical past filtration. -/
theorem s7_restart_on_past_event {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (hmarkov : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (s : ℝ≥0) (x : Vec d) (A : Set (Path d))
    (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] A)
    (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ γ, A.indicator (fun _ => (1 : ℝ≥0∞)) γ *
      F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
    ∫⁻ γ, A.indicator (fun _ => (1 : ℝ≥0∞)) γ *
      (∫⁻ η, F η ∂Q (γ s)) ∂Q x := by
  classical
  obtain ⟨B, hB, hpre⟩ := s7_past_event_stoppedHistory_factor s A hA
  have hind (γ : Path d) :
      B.indicator (fun _ => (1 : ℝ≥0∞)) (fun t => γ (min t s)) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) γ := by
    have hm : (fun t => γ (min t s)) ∈ B ↔ γ ∈ A := by
      change γ ∈ (fun γ : Path d => fun t => γ (min t s)) ⁻¹' B ↔ _
      rw [hpre]
    simp only [Set.indicator_apply, hm]
  have h := hmarkov s x (B.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hB) F hF
  simpa only [hind] using h

/-- A stopped-history Markov property restarts on the strict-survival event. -/
theorem s7_restart_on_survival {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (hmarkov : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ≥0) (x : Vec d)
    (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ γ, (if (s : ℝ≥0∞) < localityExitTime U γ then 1 else 0) *
      F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
    ∫⁻ γ, (if (s : ℝ≥0∞) < localityExitTime U γ then 1 else 0) *
      (∫⁻ η, F η ∂Q (γ s)) ∂Q x := by
  classical
  obtain ⟨B, hB, hpre⟩ := s7_survival_stoppedHistory_factor U hU s
  have hind (γ : Path d) :
      B.indicator (fun _ => (1 : ℝ≥0∞)) (fun t => γ (min t s)) =
        if (s : ℝ≥0∞) < localityExitTime U γ then 1 else 0 := by
    have hm : (fun t => γ (min t s)) ∈ B ↔
        (s : ℝ≥0∞) < localityExitTime U γ := by
      change γ ∈ (fun γ : Path d => fun t => γ (min t s)) ⁻¹' B ↔ _
      rw [hpre]
      rfl
    simp only [Set.indicator_apply, hm]
  have h := hmarkov s x (B.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hB) F hF
  simpa only [hind] using h


/-- A finite cemetery-coordinate law determines the corresponding finite
strict-survival trace for a law with the specified initial point. -/
theorem s7_supplied_trace_map_eq_decoded {d : ℕ} (μ : Measure (Path d))
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d)
    (hzero : ∀ᵐ γ ∂μ, γ 0 = x) (I : Finset ℕ) :
    μ.map (fun γ => I.restrict (localityKilledTrace U γ)) =
      (μ.map (fun γ => fun t : I.image (TopologicalSpace.denseSeq ℝ≥0) =>
        MarkovProcess.LifetimePath.coordinate (t : ℝ≥0)
          (MarkovProcess.ContinuousPath.killAtExit U γ))).map
            (s7FiniteTraceDecoder U I x) := by
  let J := I.image (TopologicalSpace.denseSeq ℝ≥0)
  have hf : Measurable (fun γ : MarkovProcess.LifetimePath U =>
      fun t : J => MarkovProcess.LifetimePath.coordinate (t : ℝ≥0) γ) :=
    MarkovProcess.LifetimePath.measurable_coordinateFamily (fun t : J => (t : ℝ≥0))
  change _ = Measure.map (s7FiniteTraceDecoder U I x)
    (Measure.map ((fun γ : MarkovProcess.LifetimePath U =>
      fun t : J => MarkovProcess.LifetimePath.coordinate (t : ℝ≥0) γ) ∘
      MarkovProcess.ContinuousPath.killAtExit U) μ)
  rw [Measure.map_map (s7_measurable_finiteTraceDecoder U I x)
    (hf.comp (MarkovProcess.ContinuousPath.measurable_killAtExit U hU))]
  apply Measure.map_congr
  filter_upwards [hzero] with γ hγ
  funext n
  simp only [Function.comp_apply, Finset.restrict, s7FiniteTraceDecoder]
  rw [s7_cemeteryObservation_killAtExit]
  simp [localityKilledTrace, localityKilledRecord, hγ]


/-- Equal finite cemetery-coordinate laws give equal finite strict-survival
traces when both laws start at the same point. -/
theorem s7_supplied_trace_fdd_eq_of_cemetery_fdd_eq {d : ℕ}
    (μ ν : Measure (Path d)) (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d)
    (hμ : ∀ᵐ γ ∂μ, γ 0 = x) (hν : ∀ᵐ γ ∂ν, γ 0 = x)
    (I : Finset ℕ)
    (h : μ.map (fun γ => fun t : I.image (TopologicalSpace.denseSeq ℝ≥0) =>
          MarkovProcess.LifetimePath.coordinate (t : ℝ≥0)
            (MarkovProcess.ContinuousPath.killAtExit U γ)) =
        ν.map (fun γ => fun t : I.image (TopologicalSpace.denseSeq ℝ≥0) =>
          MarkovProcess.LifetimePath.coordinate (t : ℝ≥0)
            (MarkovProcess.ContinuousPath.killAtExit U γ))) :
    μ.map (fun γ => I.restrict (localityKilledTrace U γ)) =
      ν.map (fun γ => I.restrict (localityKilledTrace U γ)) := by
  rw [s7_supplied_trace_map_eq_decoded μ U hU x hμ I,
    s7_supplied_trace_map_eq_decoded ν U hU x hν I, h]






/-- On survival to the first ordered time, the remaining cemetery
observations are those of the shifted supplied path. -/
theorem s7_killed_coordinates_ordered_survival {d n : ℕ}
    (U : Set (Vec d)) (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (γ : Path d) (hsurv : ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ)
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U)) :
    (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ↔
    MarkovProcess.LifetimePath.coordinate (times 0)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B 0 ∧
    ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
      (MarkovProcess.ContinuousPath.killAtExit U
        (MarkovProcess.ContinuousPath.shift (times 0) γ)) ∈ B i.succ := by
  have hs : ((times 0 : ℝ≥0) : ℝ≥0∞) <
      MarkovProcess.ContinuousPath.exitTime U γ := by
    simpa only [s7_localityExitTime_eq] using hsurv
  constructor
  · intro h
    refine ⟨h 0, fun i => ?_⟩
    rw [MarkovProcess.ContinuousPath.coordinate_killAtExit_shift U γ
      (times 0) (times.relativeTail i) hs,
      MarkovProcess.FiniteOrderedTimes.add_relativeTail times i]
    exact h i.succ
  · rintro ⟨h0, ht⟩ i
    refine Fin.cases h0 (fun j => ?_) i
    have hj := ht j
    rw [MarkovProcess.ContinuousPath.coordinate_killAtExit_shift U γ
      (times 0) (times.relativeTail j) hs,
      MarkovProcess.FiniteOrderedTimes.add_relativeTail times j] at hj
    exact hj



/-- If the first ordered observation is after exit, every observation is
already at the cemetery. -/
theorem s7_killed_coordinates_ordered_after_exit {d n : ℕ}
    (U : Set (Vec d)) (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (γ : Path d) (hexit : localityExitTime U γ ≤ ((times 0 : ℝ≥0) : ℝ≥0∞)) :
    ∀ i : Fin (n + 1), MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) = MarkovProcess.Cemetery.delta := by
  intro i
  apply MarkovProcess.ContinuousPath.coordinate_killAtExit_of_exitTime_le U γ
  · simpa only [s7_localityExitTime_eq] using hexit
  · exact times.monotone (Fin.zero_le i)



/-- Equality of ordered cemetery-coordinate laws implies equality at an
arbitrary finite set of times. -/
theorem s7_cemetery_finite_set_eq_of_ordered_eq {d : ℕ}
    (μ ν : Measure (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (hordered : ∀ {n : ℕ} (times : MarkovProcess.FiniteOrderedTimes n),
      μ.map (fun γ => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)) =
      ν.map (fun γ => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)))
    (I : Finset ℝ≥0) :
    μ.map (fun γ => fun t : I => MarkovProcess.LifetimePath.coordinate (t : ℝ≥0)
      (MarkovProcess.ContinuousPath.killAtExit U γ)) =
    ν.map (fun γ => fun t : I => MarkovProcess.LifetimePath.coordinate (t : ℝ≥0)
      (MarkovProcess.ContinuousPath.killAtExit U γ)) := by
  let f := fun γ : Path d => fun j : Fin I.card =>
    MarkovProcess.LifetimePath.coordinate (MarkovProcess.SubMarkovKernelSemigroup.finiteSetTimes I j)
      (MarkovProcess.ContinuousPath.killAtExit U γ)
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro j
    exact (MarkovProcess.ContinuousPath.measurable_coordinate_killAtExit U hU
      (MarkovProcess.SubMarkovKernelSemigroup.finiteSetTimes I j))
  have hfun : MarkovProcess.SubMarkovKernelSemigroup.orderedPathToFiniteSet (α := MarkovProcess.Cemetery U) I ∘ f =
      fun γ : Path d => fun t : I => MarkovProcess.LifetimePath.coordinate (t : ℝ≥0)
        (MarkovProcess.ContinuousPath.killAtExit U γ) := by
    funext γ t
    show MarkovProcess.LifetimePath.coordinate
      (MarkovProcess.SubMarkovKernelSemigroup.finiteSetTimes I ((I.orderIsoOfFin rfl).symm t))
      (MarkovProcess.ContinuousPath.killAtExit U γ) = _
    rw [MarkovProcess.SubMarkovKernelSemigroup.finiteSetTimes_orderIsoOfFin_symm_apply]
  calc
    _ = (μ.map f).map (MarkovProcess.SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
      rw [Measure.map_map (MarkovProcess.SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I) hf, hfun]
    _ = (ν.map f).map (MarkovProcess.SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
      rw [hordered (MarkovProcess.SubMarkovKernelSemigroup.finiteSetTimes I)]
    _ = _ := by
      rw [Measure.map_map (MarkovProcess.SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I) hf, hfun]



/-- Ordered cemetery-coordinate equality determines the finite killed traces. -/
theorem s7_trace_fdd_eq_of_ordered_cemetery_eq {d : ℕ}
    (μ ν : Measure (Path d)) (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d)
    (hμ : ∀ᵐ γ ∂μ, γ 0 = x) (hν : ∀ᵐ γ ∂ν, γ 0 = x)
    (hordered : ∀ {n : ℕ} (times : MarkovProcess.FiniteOrderedTimes n),
      μ.map (fun γ => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)) =
      ν.map (fun γ => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ))) :
    ∀ I : Finset ℕ,
      μ.map (fun γ => I.restrict (localityKilledTrace U γ)) =
      ν.map (fun γ => I.restrict (localityKilledTrace U γ)) := by
  intro I
  apply s7_supplied_trace_fdd_eq_of_cemetery_fdd_eq μ ν U hU x hμ hν I
  exact s7_cemetery_finite_set_eq_of_ordered_eq μ ν U hU hordered
    (I.image (TopologicalSpace.denseSeq ℝ≥0))



/-- The deterministic restart identity in restricted-integral form. -/
theorem s7_restart_setLIntegral {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (hmarkov : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (s : ℝ≥0) (x : Vec d) (A : Set (Path d))
    (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] A)
    (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ γ in A, F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ in A, (∫⁻ η, F η ∂Q (γ s)) ∂Q x := by
  have hA' : MeasurableSet A :=
    (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s A hA
  have h := s7_restart_on_past_event Q hmarkov s x A hA F hF
  have hleft : (∫⁻ γ, A.indicator (fun _ => (1 : ℝ≥0∞)) γ *
      F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ in A, F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x := by
    rw [← lintegral_indicator hA']
    apply lintegral_congr
    intro γ
    by_cases hγ : γ ∈ A <;> simp [hγ]
  have hright : (∫⁻ γ, A.indicator (fun _ => (1 : ℝ≥0∞)) γ *
      (∫⁻ η, F η ∂Q (γ s)) ∂Q x) =
      ∫⁻ γ in A, (∫⁻ η, F η ∂Q (γ s)) ∂Q x := by
    rw [← lintegral_indicator hA']
    apply lintegral_congr
    intro γ
    by_cases hγ : γ ∈ A <;> simp [hγ]
  exact hleft.symm.trans (h.trans hright)



/-- Equal strict-survival marginals have equal mass in the dead branch. -/
theorem s7_exit_before_eq_of_killed_marginals {d : ℕ}
    (Q R : Kernel (Vec d) (Path d)) [IsMarkovKernel Q] [IsMarkovKernel R]
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d)
    (hpart : ∀ A : Set (Vec d), MeasurableSet A →
      Q x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} =
      R x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A}) :
    Q x {γ | ¬ (t : ℝ≥0∞) < localityExitTime U γ} =
      R x {γ | ¬ (t : ℝ≥0∞) < localityExitTime U γ} := by
  have hA : MeasurableSet {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ} := by
    simpa only [s7_localityExitTime_eq] using
      (MarkovProcess.ContinuousPath.measurableSet_lt_exitTime U hU t)
  have hs : Q x {γ | (t : ℝ≥0∞) < localityExitTime U γ} =
      R x {γ | (t : ℝ≥0∞) < localityExitTime U γ} := by
    simpa only [Set.mem_univ, and_true] using hpart Set.univ MeasurableSet.univ
  change Q x {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ}ᶜ =
    R x {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ}ᶜ
  rw [prob_compl_eq_one_sub hA, prob_compl_eq_one_sub hA, hs]



/-- A live endpoint event is measurable with respect to its complete past. -/
theorem s7_killed_endpoint_event_past {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ≥0) (A : Set (Vec d)) (hA : MeasurableSet A) :
    MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] {γ : Path d |
        (s : ℝ≥0∞) < localityExitTime U γ ∧ γ s ∈ A} := by
  have hs : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} := by
    simpa only [s7_localityExitTime_eq] using
      (MarkovProcess.ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU s)
  exact hs.inter
    ((MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := Vec d) s) hA)



/-- The supplied Markov restart identity restricted to a live endpoint event. -/
theorem s7_restart_on_killed_endpoint {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (hmarkov : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ≥0) (x : Vec d)
    (A : Set (Vec d)) (hA : MeasurableSet A)
    (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ γ in {γ | (s : ℝ≥0∞) < localityExitTime U γ ∧ γ s ∈ A},
      F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
    ∫⁻ γ in {γ | (s : ℝ≥0∞) < localityExitTime U γ ∧ γ s ∈ A},
      (∫⁻ η, F η ∂Q (γ s)) ∂Q x :=
  s7_restart_setLIntegral Q hmarkov s x _
    (s7_killed_endpoint_event_past U hU s A hA) F hF


/-- On the live branch, an ordered cemetery box factors into its first
killed endpoint and a box for the restarted path. -/
theorem s7_ordered_box_live_factor {d n : ℕ} (U : Set (Vec d))
    (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U)) (γ : Path d)
    (hs : ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ) :
    (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ↔
    γ (times 0) ∈ Subtype.val '' (MarkovProcess.Cemetery.alive ⁻¹' B 0) ∧
    ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
      (MarkovProcess.ContinuousPath.killAtExit U
        (MarkovProcess.ContinuousPath.shift (times 0) γ)) ∈ B i.succ := by
  rw [s7_killed_coordinates_ordered_survival U times γ hs B]
  have hs' : ((times 0 : ℝ≥0) : ℝ≥0∞) <
      MarkovProcess.ContinuousPath.exitTime U γ := by
    simpa only [s7_localityExitTime_eq] using hs
  rw [MarkovProcess.ContinuousPath.coordinate_killAtExit_of_lt U γ (times 0) hs']
  rw [MarkovProcess.mem_image_val_iff U
    (MarkovProcess.ContinuousPath.mem_of_lt_exitTime U γ (times 0) hs')]
  rfl


attribute [local instance] Classical.propDecidable

/-- In the dead branch, an ordered box either contains every cemetery
coordinate or has empty intersection with that branch. -/
theorem s7_ordered_box_dead_factor {d n : ℕ} (U : Set (Vec d))
    (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U)) :
    {γ : Path d | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ¬ ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
    if ∀ i, (MarkovProcess.Cemetery.delta : MarkovProcess.Cemetery U) ∈ B i then
      {γ : Path d | ¬ ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ}
    else ∅ := by
  classical
  split_ifs with hb
  · ext γ
    simp only [Set.mem_ofPred_eq]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_, h⟩
      intro i
      rw [s7_killed_coordinates_ordered_after_exit U times γ (not_lt.mp h) i]
      exact hb i
  · ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hbox hexit
    obtain ⟨i, hi⟩ := not_forall.mp hb
    apply hi
    have h := hbox i
    rw [s7_killed_coordinates_ordered_after_exit U times γ (not_lt.mp hexit) i] at h
    exact h


/-- Equal killed marginals give equal dead-branch contributions to each box. -/
theorem s7_ordered_box_dead_eq {d n : ℕ}
    (Q R : Kernel (Vec d) (Path d)) [IsMarkovKernel Q] [IsMarkovKernel R]
    (U : Set (Vec d)) (hU : IsOpen U)
    (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U)) (x : Vec d)
    (hpart : ∀ A : Set (Vec d), MeasurableSet A →
      Q x {γ | ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ ∧ γ (times 0) ∈ A} =
      R x {γ | ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ ∧ γ (times 0) ∈ A}) :
    Q x {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ¬ ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
    R x {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ¬ ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} := by
  rw [s7_ordered_box_dead_factor U times B]
  split_ifs
  · exact s7_exit_before_eq_of_killed_marginals Q R U hU (times 0) x hpart
  · simp


/-- The supplied killed endpoint measure is concentrated on the open domain. -/
theorem s7SuppliedKilledKernel_compl_eq_zero {d : ℕ}
    (Q : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) : s7SuppliedKilledKernel Q U hU t x Uᶜ = 0 := by
  rw [s7SuppliedKilledKernel_apply Q U hU t x hU.measurableSet.compl]
  have h : {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ Uᶜ} = ∅ := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro hs hn
    apply hn
    apply MarkovProcess.ContinuousPath.mem_of_lt_exitTime U γ t
    simpa only [s7_localityExitTime_eq] using hs
  rw [h, measure_empty]


/-- Integration against the supplied killed endpoint is integration over
strict survival of the original supplied path law. -/
theorem s7SuppliedKilledKernel_lintegral {d : ℕ}
    (Q : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (f : Vec d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂(s7SuppliedKilledKernel Q U hU t x)) =
      ∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ}, f (γ t) ∂Q x := by
  change (∫⁻ y, f y ∂((Q.restrict (MarkovProcess.ContinuousPath.measurableSet_lt_exitTime U hU t)).map (MarkovProcess.ContinuousPath.coordinateProcess t) x)) = _
  rw [Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_coordinateProcess t),
    Kernel.restrict_apply,
    lintegral_map hf (MarkovProcess.ContinuousPath.measurable_coordinateProcess t)]
  simp only [s7_localityExitTime_eq, MarkovProcess.ContinuousPath.coordinateProcess]


/-- Equal killed endpoints transport any two measurable integrands that agree
at live positions. -/
theorem s7_killed_endpoint_lintegral_eq {d : ℕ}
    (Q R : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d)
    (hkernel : s7SuppliedKilledKernel Q U hU t x = s7SuppliedKilledKernel R U hU t x)
    (f g : Vec d → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ y ∈ U, f y = g y) :
    (∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ}, f (γ t) ∂Q x) =
      ∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ}, g (γ t) ∂R x := by
  rw [← s7SuppliedKilledKernel_lintegral Q U hU t x f hf,
    ← s7SuppliedKilledKernel_lintegral R U hU t x g hg, ← hkernel]
  apply lintegral_congr_ae
  have h : ∀ᵐ y ∂(s7SuppliedKilledKernel Q U hU t x), y ∈ U :=
    mem_ae_iff.mpr (s7SuppliedKilledKernel_compl_eq_zero Q U hU t x)
  filter_upwards [h] with y hy
  exact hfg y hy


/-- The live part of an ordered box is the intersection of a killed
endpoint event and a shifted tail event. -/
theorem s7_ordered_box_live_event_factor {d n : ℕ} (U : Set (Vec d))
    (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U)) :
    {γ : Path d | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
    {γ : Path d | ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ ∧
      γ (times 0) ∈ Subtype.val '' (MarkovProcess.Cemetery.alive ⁻¹' B 0) ∧
      ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
        (MarkovProcess.ContinuousPath.killAtExit U
          (MarkovProcess.ContinuousPath.shift (times 0) γ)) ∈ B i.succ} := by
  ext γ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hbox, hs⟩
    exact ⟨hs, (s7_ordered_box_live_factor U times B γ hs).mp hbox⟩
  · rintro ⟨hs, htail⟩
    exact ⟨(s7_ordered_box_live_factor U times B γ hs).mpr htail, hs⟩


/-- The set of live positions selected by a measurable cemetery event is
measurable in the ambient state space. -/
theorem s7_measurable_live_cemetery_preimage {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (B : Set (MarkovProcess.Cemetery U)) (hB : MeasurableSet B) :
    MeasurableSet (Subtype.val '' (MarkovProcess.Cemetery.alive ⁻¹' B)) := by
  exact (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr
    (measurable_inl hB)


/-- Equal live endpoints and equal restarted event probabilities give equal
live-branch integrals for any measurable endpoint selection. -/
theorem s7_killed_endpoint_event_lintegral_eq {d : ℕ}
    (Q R : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d)
    (hkernel : s7SuppliedKilledKernel Q U hU t x = s7SuppliedKilledKernel R U hU t x)
    (A : Set (Vec d)) (hA : MeasurableSet A)
    (D : Set (Path d)) (hD : MeasurableSet D)
    (htail : ∀ y ∈ U, Q y D = R y D) :
    (∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ},
      A.indicator (fun y => Q y D) (γ t) ∂Q x) =
    ∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ},
      A.indicator (fun y => R y D) (γ t) ∂R x := by
  apply s7_killed_endpoint_lintegral_eq Q R U hU t x hkernel
  · exact (Q.measurable_coe hD).indicator hA
  · exact (R.measurable_coe hD).indicator hA
  · intro y hy
    by_cases h : y ∈ A
    · simp only [Set.indicator_of_mem h, htail y hy]
    · simp only [Set.indicator_of_notMem h]


/-- Restart a measurable tail event after a live endpoint selection. -/
theorem s7_restart_live_event_measure {d : ℕ} (Q : Kernel (Vec d) (Path d))
    (hmarkov : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d)
    (A : Set (Vec d)) (hA : MeasurableSet A)
    (D : Set (Path d)) (hD : MeasurableSet D) :
    Q x ({γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} ∩
      MarkovProcess.ContinuousPath.shift t ⁻¹' D) =
    ∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ},
      A.indicator (fun y => Q y D) (γ t) ∂Q x := by
  let E : Set (Path d) := {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A}
  let F : Path d → ℝ≥0∞ := D.indicator (fun _ => 1)
  have hF : Measurable F :=
    (measurable_const : Measurable (fun _ : Path d => (1 : ℝ≥0∞))).indicator hD
  have hshift : Measurable (MarkovProcess.ContinuousPath.shift t) :=
    MarkovProcess.ContinuousPath.measurable_shift_fixed (alpha := Vec d) t
  have hsD : MeasurableSet (MarkovProcess.ContinuousPath.shift t ⁻¹' D) := hshift hD
  have hrestart := s7_restart_on_killed_endpoint Q hmarkov U hU t x A hA F hF
  have hleft : Q x (E ∩ MarkovProcess.ContinuousPath.shift t ⁻¹' D) =
      ∫⁻ γ in E, F (MarkovProcess.ContinuousPath.shift t γ) ∂Q x := by
    rw [Set.inter_comm E, ← Measure.restrict_apply hsD, ← setLIntegral_one, ← lintegral_indicator hsD]
    congr 1
  have hright : (∫⁻ γ in E, (∫⁻ η, F η ∂Q (γ t)) ∂Q x) =
      ∫⁻ γ in {γ | (t : ℝ≥0∞) < localityExitTime U γ},
        A.indicator (fun y => Q y D) (γ t) ∂Q x := by
    have hcoord := MarkovProcess.ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t
    have hpre : MeasurableSet ((fun γ : Path d => γ t) ⁻¹' A) := hcoord hA
    have hE : E = {γ | (t : ℝ≥0∞) < localityExitTime U γ} ∩
        (fun γ : Path d => γ t) ⁻¹' A := by
      ext γ
      rfl
    rw [hE, Set.inter_comm, ← Measure.restrict_restrict hpre, ← lintegral_indicator hpre]
    apply lintegral_congr
    intro γ
    have hval : (∫⁻ η, F η ∂Q (γ t)) = Q (γ t) D := by
      dsimp only [F]
      rw [lintegral_indicator hD, setLIntegral_one]
    simp only [Set.indicator_apply, Set.mem_preimage, hval]
  exact hleft.trans (hrestart.trans hright)



/-- The live contribution to an ordered cemetery box is determined by the
killed endpoint law and the restarted tail-event probabilities. -/
theorem s7_ordered_box_live_eq {d n : ℕ}
    (Q R : Kernel (Vec d) (Path d))
    (hmarkovQ : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (hmarkovR : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂R x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂R (γ s)) ∂R x)
    (U : Set (Vec d)) (hU : IsOpen U)
    (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U))
    (hB : ∀ i, MeasurableSet (B i)) (x : Vec d)
    (hkernel : s7SuppliedKilledKernel Q U hU (times 0) x =
      s7SuppliedKilledKernel R U hU (times 0) x)
    (htail : ∀ y ∈ U,
      Q y {γ | ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
        (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ} =
      R y {γ | ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
        (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ}) :
    Q x {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
    R x {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} := by
  let A := Subtype.val '' (MarkovProcess.Cemetery.alive ⁻¹' B 0)
  let D : Set (Path d) := {γ | ∀ i : Fin n,
    MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ}
  have hA : MeasurableSet A := s7_measurable_live_cemetery_preimage U hU (B 0) (hB 0)
  have hD : MeasurableSet D := by
    have hm : MeasurableSet (⋂ i : Fin n, {γ : Path d | MarkovProcess.LifetimePath.coordinate (times.relativeTail i) (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ}) := by
      apply MeasurableSet.iInter
      intro i
      exact (MarkovProcess.ContinuousPath.measurable_coordinate_killAtExit U hU
        (times.relativeTail i)) (hB i.succ)
    convert hm using 1
    ext γ
    simp [D]
  have hset : {γ : Path d | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
      {γ | ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ ∧ γ (times 0) ∈ A} ∩
        MarkovProcess.ContinuousPath.shift (times 0) ⁻¹' D := by
    rw [s7_ordered_box_live_event_factor U times B]
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, A, D]
    tauto
  rw [hset, s7_restart_live_event_measure Q hmarkovQ U hU (times 0) x A hA D hD,
    s7_restart_live_event_measure R hmarkovR U hU (times 0) x A hA D hD]
  exact s7_killed_endpoint_event_lintegral_eq Q R U hU (times 0) x hkernel A hA D hD htail



/-- Equality of the live and dead contributions gives equality of an ordered box. -/
theorem s7_ordered_box_eq_of_branch_eq {d n : ℕ}
    (μ ν : Measure (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (times : MarkovProcess.FiniteOrderedTimes (n + 1))
    (B : Fin (n + 1) → Set (MarkovProcess.Cemetery U))
    (hlive : μ {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
      ν {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ})
    (hdead : μ {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ¬ ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
      ν {γ | (∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i) ∧
      ¬ ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ}) :
    μ {γ | ∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i} =
    ν {γ | ∀ i, MarkovProcess.LifetimePath.coordinate (times i)
      (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i} := by
  let E : Set (Path d) := {γ | ∀ i, MarkovProcess.LifetimePath.coordinate (times i)
    (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i}
  let S : Set (Path d) := {γ | ((times 0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ}
  have hS : MeasurableSet S := by
    simpa only [S, s7_localityExitTime_eq] using
      (MarkovProcess.ContinuousPath.measurableSet_lt_exitTime U hU (times 0))
  change μ E = ν E
  calc
    μ E = μ (E ∩ S) + μ (E \ S) := (measure_inter_add_sdiff E hS).symm
    _ = ν (E ∩ S) + ν (E \ S) := by
      change μ {γ | γ ∈ E ∧ γ ∈ S} + μ {γ | γ ∈ E ∧ γ ∉ S} = _
      change μ {γ | _} + μ {γ | _} = ν {γ | γ ∈ E ∧ γ ∈ S} + ν {γ | γ ∈ E ∧ γ ∉ S}
      exact congrArg₂ (· + ·) hlive hdead
    _ = ν E := measure_inter_add_sdiff E hS



/-- Strict-survival marginals and deterministic restart determine all ordered
cemetery-coordinate distributions for starts in the open domain. -/
theorem s7_ordered_cemetery_fdd_eq_of_killed_marginals {d : ℕ}
    (Q R : Kernel (Vec d) (Path d)) [IsMarkovKernel Q] [IsMarkovKernel R]
    (hmarkovQ : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂Q x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂Q (γ s)) ∂Q x)
    (hmarkovR : ∀ (s : ℝ≥0) (x : Vec d)
      (H : (ℝ≥0 → Vec d) → ℝ≥0∞), Measurable H →
      ∀ (F : Path d → ℝ≥0∞), Measurable F →
      (∫⁻ γ, H (fun t => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂R x) =
      ∫⁻ γ, H (fun t => γ (min t s)) *
        (∫⁻ η, F η ∂R (γ s)) ∂R x)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hpart : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      ∀ A : Set (Vec d), MeasurableSet A →
      Q x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} =
      R x {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A}) :
    ∀ {n : ℕ} (times : MarkovProcess.FiniteOrderedTimes n) (x : Vec d), x ∈ U →
      (Q x).map (fun γ => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)) =
      (R x).map (fun γ => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)) := by
  intro n
  induction n with
  | zero =>
      intro times x hx
      have hf : (fun γ : Path d => fun i : Fin 0 =>
          MarkovProcess.LifetimePath.coordinate (times i)
            (MarkovProcess.ContinuousPath.killAtExit U γ)) =
          fun _ => MarkovProcess.FiniteOrderedTimes.emptyPath (MarkovProcess.Cemetery U) := by
        funext γ
        exact Subsingleton.elim _ _
      rw [hf, Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  | succ n ih =>
      intro times x hx
      let f := fun γ : Path d => fun i : Fin (n + 1) =>
        MarkovProcess.LifetimePath.coordinate (times i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)
      have hf : Measurable f := Measurable.of_eval fun i =>
        MarkovProcess.ContinuousPath.measurable_coordinate_killAtExit U hU (times i)
      let g := fun γ : Path d => fun i : Fin n =>
        MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
          (MarkovProcess.ContinuousPath.killAtExit U γ)
      have hg : Measurable g := Measurable.of_eval fun i =>
        MarkovProcess.ContinuousPath.measurable_coordinate_killAtExit U hU (times.relativeTail i)
      change (Q x).map f = (R x).map f
      refine MeasureTheory.ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
      · rintro _ ⟨B, hB, rfl⟩
        have hBm : ∀ i : Fin (n + 1), MeasurableSet (B i) :=
          fun i => hB i (Set.mem_univ i)
        have hbox : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hBm
        have htailbox : MeasurableSet (Set.univ.pi fun i : Fin n => B i.succ) :=
          MeasurableSet.univ_pi fun i => hBm i.succ
        have htail : ∀ y ∈ U,
            Q y {γ | ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
              (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ} =
            R y {γ | ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
              (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ} := by
          intro y hy
          have h := congrArg (fun μ : Measure (Fin n → MarkovProcess.Cemetery U) =>
            μ (Set.univ.pi fun i : Fin n => B i.succ)) (ih times.relativeTail y hy)
          rw [Measure.map_apply hg htailbox, Measure.map_apply hg htailbox] at h
          have hpre : g ⁻¹' (Set.univ.pi fun i : Fin n => B i.succ) =
              {γ | ∀ i : Fin n, MarkovProcess.LifetimePath.coordinate (times.relativeTail i)
                (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i.succ} := by
            ext γ
            simp [g, Set.mem_pi]
          simpa only [hpre] using h
        rw [Measure.map_apply hf hbox, Measure.map_apply hf hbox]
        have hpre : f ⁻¹' (Set.univ.pi B) =
            {γ | ∀ i, MarkovProcess.LifetimePath.coordinate (times i)
              (MarkovProcess.ContinuousPath.killAtExit U γ) ∈ B i} := by
          ext γ
          simp [f, Set.mem_pi]
        rw [hpre]
        apply s7_ordered_box_eq_of_branch_eq (Q x) (R x) U hU times B
        · exact s7_ordered_box_live_eq Q R hmarkovQ hmarkovR U hU times B hBm x
            (s7SuppliedKilledKernel_eq_of_marginals Q R U hU hpart (times 0) x hx) htail
        · exact s7_ordered_box_dead_eq Q R U hU times B x (hpart (times 0) x hx)
      · rw [measure_univ, measure_univ]


open EinsteinRelation.External.GantertSection7Support

/-- Actual supplied killed endpoint equality determines finite killed-trace laws. -/
theorem s7_supplied_killed_trace_fdd_of_killed_marginals
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hpart : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      ∀ A : Set (Vec d), MeasurableSet A →
      (r.pathLaw x) {γ | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ ∧ γ t ∈ A} =
      (r'.pathLaw x) {γ | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ ∧ γ t ∈ A}) :
    ∀ x ∈ U, ∀ I : Finset ℕ,
      (r.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) =
      (r'.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) := by
  let : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  let : IsMarkovKernel r'.pathLaw := r'.pathLaw_isMarkovKernel
  intro x hx I
  apply s7_trace_fdd_eq_of_ordered_cemetery_eq (r.pathLaw x) (r'.pathLaw x) U hU x
  · simpa only [pathPosition] using r.pathLaw_starts_at x
  · simpa only [pathPosition] using r'.pathLaw_starts_at x
  · intro n times
    exact s7_ordered_cemetery_fdd_eq_of_killed_marginals r.pathLaw r'.pathLaw
      (u1_supplied_deterministic_past_future_factorization hd Λ hΛ ω hω lam h0 h1 r)
      (u1_supplied_deterministic_past_future_factorization hd Λ hΛ ω' hω' lam h0 h1 r') U hU hpart times x hx


/-- Equality of the actual killed endpoint kernels determines killed-trace laws. -/
theorem s7_supplied_killed_trace_fdd_of_endpoint_kernel_equality
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hk : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      gmpKilledEndpointKernel r U hU t x =
        gmpKilledEndpointKernel r' U hU t x) :
    ∀ x ∈ U, ∀ I : Finset ℕ,
      (r.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) =
      (r'.pathLaw x).map (fun γ => I.restrict (localityKilledTrace U γ)) := by
  apply s7_supplied_killed_trace_fdd_of_killed_marginals hd Λ hΛ ω ω' hω hω'
    lam h0 h1 r r' U hU
  intro t x hx A hA
  have heq := congrArg (fun μ : Measure (Vec d) => μ A) (hk t x hx)
  rw [gmpKilledEndpointKernel_apply, gmpKilledEndpointKernel_apply,
    Measure.map_apply (measurable_pathPosition t) hA,
    Measure.map_apply (measurable_pathPosition t) hA,
    Measure.restrict_apply ((measurable_pathPosition t) hA),
    Measure.restrict_apply ((measurable_pathPosition t) hA)] at heq
  simpa only [Set.inter_def, Set.preimage, Set.mem_ofPred_eq, pathPosition, and_comm] using heq

/-- Endpoint equality gives killed-trace laws for a finite family of observation sets
and starts in the domain. -/
theorem s7_supplied_killed_trace_fdd_finite_family_of_endpoint_kernel_equality
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hk : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      gmpKilledEndpointKernel r U hU t x =
        gmpKilledEndpointKernel r' U hU t x)
    {ι : Type*} (J : Finset ι) (starts : ι → Vec d) (observations : ι → Finset ℕ)
    (hstarts : ∀ i ∈ J, starts i ∈ U) :
    ∀ i ∈ J,
      (r.pathLaw (starts i)).map (fun γ => (observations i).restrict (localityKilledTrace U γ)) =
      (r'.pathLaw (starts i)).map (fun γ => (observations i).restrict (localityKilledTrace U γ)) := by
  intro i hi
  exact s7_supplied_killed_trace_fdd_of_endpoint_kernel_equality hd Λ hΛ ω ω' hω hω'
    lam h0 h1 r r' U hU hk (starts i) (hstarts i hi) (observations i)

example {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hk : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      gmpKilledEndpointKernel r U hU t x = gmpKilledEndpointKernel r' U hU t x)
    (J : Finset ℕ) (starts : ℕ → Vec d) (observations : ℕ → Finset ℕ)
    (hstarts : ∀ i ∈ J, starts i ∈ U) (i : ℕ) (hi : i ∈ J) :
    (r.pathLaw (starts i)).map (fun γ => (observations i).restrict (localityKilledTrace U γ)) =
    (r'.pathLaw (starts i)).map (fun γ => (observations i).restrict (localityKilledTrace U γ)) := by
  exact s7_supplied_killed_trace_fdd_finite_family_of_endpoint_kernel_equality
    hd Λ hΛ ω ω' hω hω' lam h0 h1 r r' U hU hk J starts observations hstarts i hi

universe u

example : type_of% @s7_supplied_killed_trace_fdd_finite_family_of_endpoint_kernel_equality.{u} =
    (∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
      (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
      (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
      (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (hk : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
        gmpKilledEndpointKernel r U hU t x = gmpKilledEndpointKernel r' U hU t x)
      {ι : Type u} (J : Finset ι) (starts : ι → Vec d) (observations : ι → Finset ℕ)
      (hstarts : ∀ i ∈ J, starts i ∈ U),
      ∀ i ∈ J,
        (r.pathLaw (starts i)).map (fun γ => (observations i).restrict (localityKilledTrace U γ)) =
        (r'.pathLaw (starts i)).map (fun γ => (observations i).restrict (localityKilledTrace U γ))) := rfl

open Lean Elab Command in
run_cmd do
  let name := `EinsteinFull.s7_supplied_killed_trace_fdd_finite_family_of_endpoint_kernel_equality
  liftTermElabM <| withOptions (fun opts => opts.setBool `smartUnfolding false) <|
    Meta.withTransparency .all do
      let ci ← getConstInfo name
      Meta.check ci.type
      let some value := ci.value? (allowOpaque := true) | throwError "Missing value for {name}"
      Meta.check value
      unless ← Meta.isDefEq (← Meta.inferType value) ci.type do
        throwError "Type/value mismatch in {name}"

#print axioms s7_supplied_killed_trace_fdd_finite_family_of_endpoint_kernel_equality

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let name := `EinsteinFull.s7_supplied_killed_trace_fdd_finite_family_of_endpoint_kernel_equality
  let decls := #[name]
  let linters ← liftCoreM (getChecks true none none)
  let results ← liftCoreM (lintCore decls linters)
  let msg ← liftCoreM <| formatLinterResults results decls false
    "in s7 finite-family endpoint application" true .medium linters.size
  if results.any (!·.2.isEmpty) then logError msg else logInfo msg
  let axioms ← collectAxioms name
  for ax in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"S7 finite-family audit: {linters.size} linters and standard axioms"

/-- A uniform local-coefficient comparison of killed endpoints supplies the S2 interface. -/
theorem s7_supplied_killed_fdd_locality_of_endpoint_locality
    (endpoint : ∀ {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
      (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
      (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
      (U : Set (Vec d)) (hU : IsOpen U)
      (_hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0),
      ∀ x : Vec d, gmpKilledEndpointKernel G U hU t x =
        gmpKilledEndpointKernel G' U hU t x) : S2SuppliedKilledFDDLocality := by
  intro d hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag
  apply s7_supplied_killed_trace_fdd_of_endpoint_kernel_equality hd L hL ω ω'
    hω hω' lam h0 h1 G G' U hU
  intro t x _
  exact endpoint hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag t x


/-- Supplied killed endpoint comparison entails the S2 killed-trace interface. -/
theorem s7_supplied_killed_fdd_locality_of_killed_marginals
    (hpart : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
      (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
      (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
      (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
      (U : Set (Vec d)), IsOpen U →
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
      ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
        ∀ A : Set (Vec d), MeasurableSet A →
        (r.pathLaw x) {γ | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ ∧ γ t ∈ A} =
        (r'.pathLaw x) {γ | (t : ℝ≥0∞) < Diffusion.localityExitTime U γ ∧ γ t ∈ A}) :
    S2SuppliedKilledFDDLocality := by
  intro d hd Λ hΛ ω ω' hω hω' lam h0 h1 r r' U hU hfields
  exact s7_supplied_killed_trace_fdd_of_killed_marginals hd Λ hΛ ω ω' hω hω'
    lam h0 h1 r r' U hU (hpart hd Λ hΛ ω ω' hω hω' lam h0 h1 r r' U hU hfields)

/-- Positive-time killed rows of the supplied law are absolutely continuous. -/
theorem s7_supplied_killed_kernel_absolutelyContinuous
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    s7SuppliedKilledKernel G.pathLaw U hU t x ≪ (volume : Measure (Vec d)) := by
  have heq : s7SuppliedKilledKernel G.pathLaw U hU t x =
      ((G.pathLaw x).restrict
        {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ}).map (pathPosition t) := by
    apply Measure.ext
    intro A hA
    rw [s7SuppliedKilledKernel_apply G.pathLaw U hU t x hA,
      Measure.map_apply (measurable_pathPosition t) hA,
      Measure.restrict_apply ((measurable_pathPosition t) hA)]
    congr 1
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, pathPosition]
    tauto
  rw [heq]
  exact u1_supplied_killed_marginal_absolutelyContinuous hd L hL ω hω lam h0 h1 G U t ht x




/-- The actual killed endpoint measures form a measurable family in time. -/
theorem s7_supplied_killed_kernel_measurable_time
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) :
    Measurable (fun t : ℝ => s7SuppliedKilledKernel G.pathLaw U hU t.toNNReal x) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let B : Set (ℝ × Path d) := {p |
    (p.1.toNNReal : ℝ≥0∞) < localityExitTime U p.2 ∧ p.2 p.1.toNNReal ∈ A}
  have hB : MeasurableSet B := by
    apply MeasurableSet.inter
    · exact measurableSet_lt
        (ENNReal.continuous_coe.measurable.comp
          (continuous_real_toNNReal.measurable.comp measurable_fst))
        ((measurable_localityExitTime U hU).comp measurable_snd)
    · exact hA.preimage (continuous_eval.comp
        (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hs : Measurable (fun t : ℝ => (G.pathLaw x) (Prod.mk t ⁻¹' B)) :=
    measurable_measure_prodMk_left hB
  convert hs using 1
  funext t
  rw [s7SuppliedKilledKernel_apply G.pathLaw U hU t.toNNReal x hA]
  rfl

/-- Integrating the positive-time supplied killed rows gives an absolutely continuous measure. -/
theorem s7_supplied_killed_integrated_kernel_absolutelyContinuous
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (ω : FieldPair d) (hω : IsRegular L ω) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (x : Vec d) :
    Measure.bind (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))
      (fun t => s7SuppliedKilledKernel G.pathLaw U hU t.toNNReal x) ≪
      (volume : Measure (Vec d)) := by
  refine Measure.AbsolutelyContinuous.mk fun N hN hnull => ?_
  rw [Measure.bind_apply hN
    (s7_supplied_killed_kernel_measurable_time hd L hL ω hω lam h0 h1 G U hU x).aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (s7_supplied_killed_kernel_absolutelyContinuous hd L hL ω hω lam h0 h1
    G U hU t.toNNReal (Real.toNNReal_pos.mpr ht.1) x) hnull

end EinsteinFull
