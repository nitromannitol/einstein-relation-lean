import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Reconstruction of complete exit-stopped paths

The literal exit-stopped path has a Borel decoder from countably many killed
observations. This reconstructs complete stopped laws from killed finite-dimensional
laws, including finite-exit boundary values and infinite exits. The actual GMP
killed-kernel comparison and every-start upgrade remain separate obligations.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion

noncomputable section

/-- Membership of a stopped position in the open domain is exactly strict survival.
At a finite exit the stopped position is outside, including an immediate exit. -/
theorem localityStoppedPath_mem_iff {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) (t : ℝ≥0) :
    localityStoppedPath U γ t ∈ U ↔ (t : ℝ≥0∞) < localityExitTime U γ := by
  by_cases ht : (t : ℝ≥0∞) < localityExitTime U γ
  · rw [localityStoppedPath_eq_of_le_exit U γ t ht.le]
    exact iff_of_true ((lt_localityExitTime_iff U hU γ t).mp ht t le_rfl) ht
  · have hle := le_of_not_gt ht
    have hf := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    rw [localityStoppedPath_apply, min_eq_right hle]
    exact iff_of_false (localityExitTime_mem_compl U hU γ hf) ht

/-- Stopping at exit preserves the literal exit time, including infinity. -/
theorem localityExitTime_stopped {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) : localityExitTime U (localityStoppedPath U γ) = localityExitTime U γ := by
  apply le_antisymm
  · by_cases hf : localityExitTime U γ = ⊤
    · rw [hf]; exact le_top
    · apply iInf_le_of_le (localityExitTime U γ).toNNReal
      apply iInf_le_of_le
        (show localityStoppedPath U γ (localityExitTime U γ).toNNReal ∉ U from by
          rw [localityStoppedPath_mem_iff U hU, ENNReal.coe_toNNReal hf]
          exact lt_irrefl _)
      exact (ENNReal.coe_toNNReal hf).le
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    exact le_of_not_gt (fun h => ht ((localityStoppedPath_mem_iff U hU γ t).mpr h))

/-- The literal exit-stopping map is a measurable retraction onto its fixed paths. -/
theorem localityStoppedPath_idempotent {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) : localityStoppedPath U (localityStoppedPath U γ) = localityStoppedPath U γ := by
  apply ContinuousMap.ext
  intro t
  rw [localityStoppedPath_apply, localityExitTime_stopped U hU]
  have hf : min (t : ℝ≥0∞) (localityExitTime U γ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [localityStoppedPath_eq_of_le_exit U γ _ (by
    rw [ENNReal.coe_toNNReal hf]
    exact min_le_right _ _)]
  exact (localityStoppedPath_apply U γ t).symm

/-- Countably many killed observations, together with exit time and initial position.
The initial coordinate retains immediate exits; the exit coordinate includes infinity. -/
def localityKilledRecord {d : ℕ} (U : Set (Vec d)) (γ : Path d) :
    ℝ≥0∞ × Vec d × (ℕ → (ℝ × Vec d)) :=
  (localityExitTime U γ, γ 0, fun n =>
    if (TopologicalSpace.denseSeq ℝ≥0 n : ℝ≥0∞) < localityExitTime U γ then
      (1, γ (TopologicalSpace.denseSeq ℝ≥0 n)) else (0, 0))

/-- The killed record is measurable, without a process or regularity premise. -/
theorem measurable_localityKilledRecord {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (localityKilledRecord U) := by
  apply (measurable_localityExitTime U hU).prodMk
  apply (measurable_pathPosition 0).prodMk
  apply Measurable.of_eval
  intro n
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_localityExitTime U hU))
    (measurable_const.prodMk (measurable_pathPosition _)) measurable_const

/-- Exit stopping changes none of the killed record. -/
theorem localityKilledRecord_stopped {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) : localityKilledRecord U (localityStoppedPath U γ) = localityKilledRecord U γ := by
  unfold localityKilledRecord
  rw [localityExitTime_stopped U hU, localityStoppedPath_zero]
  congr 2
  funext n
  split_ifs with h
  · rw [localityStoppedPath_eq_of_le_exit U γ _ h.le]
  · rfl

private theorem eq_before_exit_of_record_eq {d : ℕ} (U : Set (Vec d))
    (γ η : Path d) (he : localityKilledRecord U γ = localityKilledRecord U η)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) < localityExitTime U γ) : γ t = η t := by
  have hexit := congrArg Prod.fst he
  change localityExitTime U γ = localityExitTime U η at hexit
  by_contra hne
  let O : Set ℝ≥0 := {s | (s : ℝ≥0∞) < localityExitTime U γ ∧ γ s ≠ η s}
  have hopen : IsOpen O :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).inter
      (isClosed_eq γ.continuous η.continuous).isOpen_compl
  obtain ⟨s, hs, n, hn⟩ := (TopologicalSpace.denseRange_denseSeq ℝ≥0).inter_open_nonempty
    O hopen ⟨t, ht, hne⟩
  have hv := congrFun (congrArg (fun r => r.2.2) he) n
  change (if (TopologicalSpace.denseSeq ℝ≥0 n : ℝ≥0∞) < localityExitTime U γ then
    (1, γ (TopologicalSpace.denseSeq ℝ≥0 n)) else (0, 0)) =
    (if (TopologicalSpace.denseSeq ℝ≥0 n : ℝ≥0∞) < localityExitTime U η then
    (1, η (TopologicalSpace.denseSeq ℝ≥0 n)) else (0, 0)) at hv
  rw [hn] at hv
  rw [if_pos hs.1, ← hexit, if_pos hs.1] at hv
  exact hs.2 (congrArg Prod.snd hv)

/-- Killed records determine the entire exit-stopped continuous path. Boundary values
are recovered by continuity from below; an infinite exit retains every coordinate. -/
theorem localityStoppedPath_eq_of_killedRecord_eq {d : ℕ} (U : Set (Vec d))
    (γ η : Path d) (he : localityKilledRecord U γ = localityKilledRecord U η) :
    localityStoppedPath U γ = localityStoppedPath U η := by
  have hexit := congrArg Prod.fst he
  change localityExitTime U γ = localityExitTime U η at hexit
  have hzero := congrArg (fun r => r.2.1) he
  change γ 0 = η 0 at hzero
  have hbefore := eq_before_exit_of_record_eq U γ η he
  apply ContinuousMap.ext
  intro t
  rw [localityStoppedPath_apply, localityStoppedPath_apply, ← hexit]
  by_cases hf : localityExitTime U γ = ⊤
  · simp only [hf, min_top_right, ENNReal.toNNReal_coe]
    exact hbefore t (hf ▸ ENNReal.coe_lt_top)
  · let a := (localityExitTime U γ).toNNReal
    have ha : (a : ℝ≥0∞) = localityExitTime U γ := ENNReal.coe_toNNReal hf
    have hclosed : IsClosed {s : ℝ≥0 | γ s = η s} := isClosed_eq γ.continuous η.continuous
    have hle : (min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal ≤ a := by
      rw [← ha, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      exact min_le_right _ _
    by_cases ha0 : a = 0
    · have hz : (min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal = 0 :=
        le_antisymm (ha0 ▸ hle) zero_le
      simpa only [hz] using hzero
    · have hsub : Set.Iio a ⊆ {s : ℝ≥0 | γ s = η s} := by
        intro s hs
        apply hbefore
        rw [← ha]
        exact ENNReal.coe_lt_coe.mpr hs
      have hc := hclosed.closure_subset_iff.mpr hsub
      rw [closure_Iio' (show (Set.Iio a).Nonempty from ⟨0, bot_lt_iff_ne_bot.mpr ha0⟩)] at hc
      exact hc hle

/-- A countable killed trace. Each observation records the initial position, a
survival flag (one or zero), and the position on survival (zero after killing).
No exit time or boundary value is supplied to this trace. -/
def localityKilledTrace {d : ℕ} (U : Set (Vec d)) (γ : Path d) :
    ℕ → Vec d × ℝ × Vec d :=
  fun n => (γ 0, (localityKilledRecord U γ).2.2 n)

/-- Every coordinate of the countable killed trace is Borel measurable. -/
theorem measurable_localityKilledTrace {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (localityKilledTrace U) := by
  apply Measurable.of_eval
  intro n
  exact (measurable_pathPosition 0).prodMk
    ((measurable_pi_apply n).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_localityKilledRecord U hU))))

private theorem not_exit_lt_of_trace_eq {d : ℕ} (U : Set (Vec d)) (γ η : Path d)
    (he : localityKilledTrace U γ = localityKilledTrace U η) :
    ¬ localityExitTime U γ < localityExitTime U η := by
  intro hlt
  obtain ⟨b, hb, hb'⟩ := exists_between hlt
  obtain ⟨a, ha, ha'⟩ := ENNReal.lt_iff_exists_coe.mp hb'
  let O : Set ℝ≥0 := {s | localityExitTime U γ < (s : ℝ≥0∞) ∧
    (s : ℝ≥0∞) < localityExitTime U η}
  have hopen : IsOpen O := (isOpen_lt continuous_const ENNReal.continuous_coe).inter
    (isOpen_lt ENNReal.continuous_coe continuous_const)
  obtain ⟨s, hs, n, hn⟩ := (TopologicalSpace.denseRange_denseSeq ℝ≥0).inter_open_nonempty
    O hopen ⟨a, ha ▸ hb, ha'⟩
  have hv := congrArg (fun f => (f n).2.1) he
  dsimp only [localityKilledTrace, localityKilledRecord] at hv
  rw [hn, if_neg (not_lt_of_ge hs.1.le), if_pos hs.2] at hv
  exact zero_ne_one hv

/-- The exit time itself is determined by countably many strict-survival observations.
This covers finite, infinite and immediate exits. -/
theorem localityExitTime_eq_of_killedTrace_eq {d : ℕ} (U : Set (Vec d))
    (γ η : Path d) (he : localityKilledTrace U γ = localityKilledTrace U η) :
    localityExitTime U γ = localityExitTime U η :=
  le_antisymm (le_of_not_gt (not_exit_lt_of_trace_eq U η γ he.symm))
    (le_of_not_gt (not_exit_lt_of_trace_eq U γ η he))

/-- The countable trace determines every coordinate of the complete stopped path,
including its finite-exit boundary position. -/
theorem localityStoppedPath_eq_of_killedTrace_eq {d : ℕ} (U : Set (Vec d))
    (γ η : Path d) (he : localityKilledTrace U γ = localityKilledTrace U η) :
    localityStoppedPath U γ = localityStoppedPath U η := by
  apply localityStoppedPath_eq_of_killedRecord_eq U γ η
  apply Prod.ext (localityExitTime_eq_of_killedTrace_eq U γ η he)
  refine Prod.ext (show γ 0 = η 0 from congrArg (fun f => (f 0).1) he) ?_
  exact funext (fun n => congrArg (fun f => (f n).2) he)

/-- Killing the already stopped path gives exactly the same countable trace. -/
theorem localityKilledTrace_stopped {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) : localityKilledTrace U (localityStoppedPath U γ) = localityKilledTrace U γ := by
  unfold localityKilledTrace
  rw [localityKilledRecord_stopped U hU, localityStoppedPath_zero]

/-- There is a Borel decoder from the countable killed trace to the COMPLETE
exit-stopped continuous path. The decoder is constructed on the Borel space of
fixed stopped paths, using the proved injectivity, rather than a uniqueness premise. -/
theorem exists_measurable_killedTrace_decoder {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) :
    ∃ D : (ℕ → Vec d × ℝ × Vec d) → Path d, Measurable D ∧
      ∀ γ : Path d, D (localityKilledTrace U γ) = localityStoppedPath U γ := by
  let S : Set (Path d) := {γ | localityStoppedPath U γ = γ}
  have hS : MeasurableSet S := measurableSet_eq_fun (measurable_localityStoppedPath U hU)
    measurable_id
  haveI : PolishSpace (Path d) := by
    haveI : CompleteSpace (Path d) := inferInstance
    haveI : Filter.IsCountablyGenerated (uniformity (Path d)) := inferInstance
    haveI : SecondCountableTopology (Path d) := inferInstance
    infer_instance
  haveI : StandardBorelSpace S := hS.standardBorel
  haveI : Nonempty S := ⟨⟨localityStoppedPath U (ContinuousMap.const _ 0),
    localityStoppedPath_idempotent U hU _⟩⟩
  let f : S → (ℕ → Vec d × ℝ × Vec d) := fun γ => localityKilledTrace U γ.val
  have hm : Measurable f := (measurable_localityKilledTrace U hU).comp measurable_subtype_coe
  have hi : Function.Injective f := by
    intro γ η he
    apply Subtype.ext
    exact γ.property.symm.trans ((localityStoppedPath_eq_of_killedTrace_eq U γ.val η.val he).trans
      η.property)
  haveI : MeasurableSpace.CountablyGenerated (ℕ → Vec d × ℝ × Vec d) := inferInstance
  haveI : MeasurableSpace.SeparatesPoints (ℕ → Vec d × ℝ × Vec d) := inferInstance
  let e := hm.measurableEmbedding hi
  refine ⟨fun r => (e.invFun r).val, measurable_subtype_coe.comp e.measurable_invFun, ?_⟩
  intro γ
  let σ : S := ⟨localityStoppedPath U γ, localityStoppedPath_idempotent U hU γ⟩
  have hrecord : localityKilledTrace U γ = f σ := (localityKilledTrace_stopped U hU γ).symm
  change (e.invFun (localityKilledTrace U γ)).val = localityStoppedPath U γ
  rw [hrecord, e.leftInverse_invFun σ]

/-- Equality of countable killed-trace laws reconstructs equality of complete
stopped laws for arbitrary measures; no finiteness or process uniqueness is needed. -/
theorem map_localityStoppedPath_eq_of_killedTrace_law_eq {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (μ ν : Measure (Path d))
    (he : μ.map (localityKilledTrace U) = ν.map (localityKilledTrace U)) :
    μ.map (localityStoppedPath U) = ν.map (localityStoppedPath U) := by
  obtain ⟨D, hD, hdecode⟩ := exists_measurable_killedTrace_decoder U hU
  have h := congrArg (Measure.map D) he
  rw [Measure.map_map hD (measurable_localityKilledTrace U hU),
    Measure.map_map hD (measurable_localityKilledTrace U hU)] at h
  have hc : D ∘ localityKilledTrace U = localityStoppedPath U := funext hdecode
  rwa [hc] at h

/-- Finite-dimensional killed observations determine the complete stopped law.
All finite exits, the infinite exit, and boundary positions are already handled
by the constructed decoder. This lemma does not supply the killed FDD comparison. -/
theorem map_localityStoppedPath_eq_of_killedTrace_fdd_eq {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (μ ν : Measure (Path d)) [IsFiniteMeasure ν]
    (he : ∀ I : Finset ℕ,
      μ.map (fun γ => I.restrict (localityKilledTrace U γ)) =
        ν.map (fun γ => I.restrict (localityKilledTrace U γ))) :
    μ.map (localityStoppedPath U) = ν.map (localityStoppedPath U) := by
  apply map_localityStoppedPath_eq_of_killedTrace_law_eq U hU μ ν
  have hμ := ProbabilityTheory.isProjectiveLimit_map
    ((measurable_localityKilledTrace U hU).aemeasurable (μ := μ))
  have hν := ProbabilityTheory.isProjectiveLimit_map
    ((measurable_localityKilledTrace U hU).aemeasurable (μ := ν))
  simp_rw [he] at hμ
  exact hμ.unique hν


/-- Conversely, the killed trace is a measurable observable of the stopped path. -/
theorem map_killedTrace_eq_of_localityStoppedPath_law_eq {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (μ ν : Measure (Path d))
    (he : μ.map (localityStoppedPath U) = ν.map (localityStoppedPath U)) :
    μ.map (localityKilledTrace U) = ν.map (localityKilledTrace U) := by
  have h := congrArg (Measure.map (localityKilledTrace U)) he
  rw [Measure.map_map (measurable_localityKilledTrace U hU)
      (measurable_localityStoppedPath U hU),
    Measure.map_map (measurable_localityKilledTrace U hU)
      (measurable_localityStoppedPath U hU)] at h
  have hc : localityKilledTrace U ∘ localityStoppedPath U = localityKilledTrace U :=
    funext (localityKilledTrace_stopped U hU)
  rwa [hc] at h

/-- The literal raw stopping formula has a measurable law, for EVERY map satisfying
that formula. Killed-trace FDD comparison therefore also reconstructs exactly the
raw-function law used in GMPKernelLocality, rather than just a chosen path version. -/
theorem raw_stoppedLaw_eq_of_killedTrace_fdd_eq {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (μ ν : Measure (Path d)) [IsFiniteMeasure ν]
    (he : ∀ I : Finset ℕ,
      μ.map (fun γ => I.restrict (localityKilledTrace U γ)) =
        ν.map (fun γ => I.restrict (localityKilledTrace U γ)))
    (stop : Path d → ℝ≥0 → Vec d)
    (hstop : ∀ (γ : Path d) (t : ℝ≥0), stop γ t =
      γ ((min (t : ℝ≥0∞) (⨅ (s : ℝ≥0) (_ : γ s ∉ U), (s : ℝ≥0∞))).toNNReal)) :
    Measurable stop ∧ μ.map stop = ν.map stop := by
  refine ⟨measurable_stoppingMap_of_exit_formula U hU stop hstop, ?_⟩
  have h := congrArg (Measure.map (fun γ : Path d => fun t : ℝ≥0 => γ t))
    (map_localityStoppedPath_eq_of_killedTrace_fdd_eq U hU μ ν he)
  have hm : Measurable (fun γ : Path d => fun t : ℝ≥0 => γ t) :=
    Measurable.of_eval (fun t => measurable_pathPosition t)
  rw [Measure.map_map hm (measurable_localityStoppedPath U hU),
    Measure.map_map hm (measurable_localityStoppedPath U hU)] at h
  have hc : (fun γ : Path d => fun t : ℝ≥0 => γ t) ∘ localityStoppedPath U = stop := by
    funext γ t
    exact (localityStoppedPath_apply U γ t).trans (hstop γ t).symm
  rwa [hc] at h

end
end EinsteinFull
