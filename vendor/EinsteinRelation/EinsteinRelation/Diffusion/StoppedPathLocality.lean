import EinsteinRelation.External.GMPLocalityInput
import EinsteinRelation.Probability.ContinuousFieldDecoder
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Order.Compact

/-!
# Finite path segments from the frozen stopped-law locality input

Source `paper/main.tex:377–381`. A path segment constrained to an open
subset of the locality region can be recovered from the stopped path.
Thus the frozen locality input identifies its restricted finite-horizon
law, without assuming locality of the coupled construction.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Diffusion

/-- The exit time appearing literally in the frozen locality statement. -/
def localityExitTime {d : ℕ} (U : Set (Vec d)) (γ : Path d) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : γ t ∉ U), (t : ℝ≥0∞)

/-- A continuous path stopped at a deterministic finite time. -/
def stopPathAt {d : ℕ} (T : ℝ≥0) (γ : Path d) : Path d :=
  ⟨fun t => γ (min t T), γ.continuous.comp (continuous_id.min continuous_const)⟩

/-- The continuous path stopped at the first exit, with the unbounded
exit-time case retaining the entire path. -/
def localityStoppedPath {d : ℕ} (U : Set (Vec d)) (γ : Path d) : Path d :=
  if localityExitTime U γ = ⊤ then γ else stopPathAt (localityExitTime U γ).toNNReal γ

theorem localityStoppedPath_apply {d : ℕ} (U : Set (Vec d)) (γ : Path d) (t : ℝ≥0) :
    localityStoppedPath U γ t =
      γ ((min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal) := by
  by_cases h : localityExitTime U γ = ⊤
  · simp [localityStoppedPath, h]
  · have hmin : (min (t : ℝ≥0∞) (localityExitTime U γ)).toNNReal =
        min t (localityExitTime U γ).toNNReal := by
      rw [← ENNReal.coe_toNNReal h, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      rfl
    simp [localityStoppedPath, h, stopPathAt, hmin]

theorem continuous_stopPathAt {d : ℕ} (T : ℝ≥0) :
    Continuous (stopPathAt (d := d) T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_fst.eval (continuous_snd.min continuous_const)

/-- A finite exit from an open region is attained outside that region. -/
theorem localityExitTime_mem_compl {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) (hfinite : localityExitTime U γ ≠ ⊤) :
    γ (localityExitTime U γ).toNNReal ∉ U := by
  let S : Set ℝ≥0 := {t | γ t ∉ U}
  have hS : IsClosed S := hU.isClosed_compl.preimage γ.continuous
  have hne : S.Nonempty := by
    by_contra hn
    apply hfinite
    apply le_antisymm le_top
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact (hn ⟨t, ht⟩).elim
  have heq : (↑(sInf S) : ℝ≥0∞) = localityExitTime U γ := ENNReal.coe_sInf hne
  have hval : (localityExitTime U γ).toNNReal = sInf S := by
    rw [← heq, ENNReal.toNNReal_coe]
  rw [hval]
  exact hS.csInf_mem hne (OrderBot.bddBelow S)

/-- A path remaining inside an open region through a finite horizon has
not reached its exit time at that horizon. -/
theorem lt_localityExitTime_of_stays {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) (T : ℝ≥0) (hstay : ∀ t : ℝ≥0, t ≤ T → γ t ∈ U) :
    (T : ℝ≥0∞) < localityExitTime U γ := by
  by_contra h
  have hle := not_lt.mp h
  have hfinite : localityExitTime U γ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  have ht : (localityExitTime U γ).toNNReal ≤ T :=
    ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfinite] using hle)
  exact localityExitTime_mem_compl U hU γ hfinite (hstay _ ht)

theorem localityStoppedPath_eq_of_le_exit {d : ℕ} (U : Set (Vec d)) (γ : Path d)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ localityExitTime U γ) :
    localityStoppedPath U γ t = γ t := by
  rw [localityStoppedPath_apply, min_eq_left ht, ENNReal.toNNReal_coe]

/-- Staying in a smaller region is determined by the stopped path through
the same horizon. This is the support condition needed by the killed kernels. -/
theorem localityStoppedPath_stays_iff {d : ℕ} (U V : Set (Vec d)) (hU : IsOpen U)
    (hVU : V ⊆ U) (γ : Path d) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t ≤ T → localityStoppedPath U γ t ∈ V) ↔
      ∀ t : ℝ≥0, t ≤ T → γ t ∈ V := by
  constructor
  · intro hstay
    have hbefore : (T : ℝ≥0∞) < localityExitTime U γ := by
      by_contra h
      have hle := not_lt.mp h
      have hfinite : localityExitTime U γ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
      have ht : (localityExitTime U γ).toNNReal ≤ T :=
        ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfinite] using hle)
      have hbad := hVU (hstay _ ht)
      rw [localityStoppedPath_eq_of_le_exit U γ _
        (le_of_eq (ENNReal.coe_toNNReal hfinite))] at hbad
      exact localityExitTime_mem_compl U hU γ hfinite hbad
    intro t ht
    simpa only [localityStoppedPath_eq_of_le_exit U γ t
      ((ENNReal.coe_le_coe.mpr ht).trans hbefore.le)] using hstay t ht
  · intro hstay t ht
    have hbefore := lt_localityExitTime_of_stays U hU γ T (fun t ht => hVU (hstay t ht))
    simpa only [localityStoppedPath_eq_of_le_exit U γ t
      ((ENNReal.coe_le_coe.mpr ht).trans hbefore.le)] using hstay t ht

/-- A finite segment constrained to a smaller open region has the same
law whenever the two exit-stopped laws agree. -/
theorem map_restrict_stopPathAt_eq_of_stoppedLaw_eq {d : ℕ}
    (U V : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (T : ℝ≥0) (μ ν : Measure (Path d)) (hstop : Measurable (localityStoppedPath U))
    (heq : μ.map (localityStoppedPath U) = ν.map (localityStoppedPath U)) :
    (μ.restrict {γ | ∀ t : ℝ≥0, t ≤ T → γ t ∈ V}).map (stopPathAt T) =
      (ν.restrict {γ | ∀ t : ℝ≥0, t ≤ T → γ t ∈ V}).map (stopPathAt T) := by
  let S : Set (Path d) := {γ | ∀ t : ℝ≥0, t ≤ T → γ t ∈ V}
  have hS : MeasurableSet S := by
    have hopen := ContinuousMap.isOpen_setOf_mapsTo (X := ℝ≥0) (Y := Vec d)
      (K := Set.Icc (0 : ℝ≥0) T) isCompact_Icc hV
    simpa only [Set.MapsTo, Set.mem_Icc, zero_le, true_and] using hopen.measurableSet
  have hpre : localityStoppedPath U ⁻¹' S = S :=
    Set.ext fun γ => localityStoppedPath_stays_iff U V hU hVU γ T
  have hfinite : ∀ γ ∈ S,
      stopPathAt T (localityStoppedPath U γ) = stopPathAt T γ := by
    intro γ hγ
    have hbefore := lt_localityExitTime_of_stays U hU γ T (fun t ht => hVU (hγ t ht))
    apply ContinuousMap.ext
    intro t
    exact localityStoppedPath_eq_of_le_exit U γ (min t T)
      ((ENNReal.coe_le_coe.mpr (min_le_right _ _)).trans hbefore.le)
  have htransport : ∀ ξ : Measure (Path d),
      ((ξ.map (localityStoppedPath U)).restrict S).map (stopPathAt T) =
        (ξ.restrict S).map (stopPathAt T) := by
    intro ξ
    rw [Measure.restrict_map hstop hS, hpre,
      Measure.map_map (continuous_stopPathAt T).measurable hstop]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hS] with γ hγ
    exact hfinite γ hγ
  change (μ.restrict S).map (stopPathAt T) = (ν.restrict S).map (stopPathAt T)
  rw [← htransport μ, heq, htransport ν]

/-- The frozen raw stopped-law equality also holds on the continuous-path
carrier. Decoding is legitimate because the displayed stopped paths are continuous. -/
theorem realization_map_localityStoppedPath_eq (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (U : Set (Vec d)) (hU : IsOpen U)
    (ω ω' : FieldPair d) (hω : IsRegular Λ₀ ω) (hω' : IsRegular Λ₀ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam h0 h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω' hω' lam h0 h1) (x : Vec d) (hx : x ∈ U) :
    Measurable (localityStoppedPath U) ∧
      (r.pathLaw x).map (localityStoppedPath U) =
        (r'.pathLaw x).map (localityStoppedPath U) := by
  let raw : Path d → ℝ≥0 → Vec d := fun γ t => localityStoppedPath U γ t
  obtain ⟨hm, heqraw⟩ := hLoc d hd Λ₀ hΛ₀ U hU ω ω' hω hω' lam h0 h1 heq r r' x hx
    raw (localityStoppedPath_apply U)
  obtain ⟨D, hD, hdecode⟩ :=
    Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)
  have hfun : D ∘ raw = localityStoppedPath U := funext fun γ => hdecode _
  have hmeas : Measurable (localityStoppedPath U) := hfun ▸ hD.comp hm
  refine ⟨hmeas, ?_⟩
  have h := congrArg (Measure.map D) heqraw
  simpa only [Measure.map_map hD hm, hfun] using h


end EinsteinRelation.Diffusion
