import EinsteinRelation.Regeneration.CouplingSpatialMaps
import EinsteinRelation.Regeneration.RenewalCarriers
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.CompactOpen

/-! # Measurability of killed segments

Source `paper/main.tex:268,377–378`. Staying in the coupling ball on the
compact one-interval time set is an open event in the starting point and
continuous path together.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration.Renewal

/-- The killed-segment event is jointly open in its centre and path. -/
theorem isOpen_killedSegment_event {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    IsOpen {p : Vec d × Path d | ∀ t : ℝ≥0, t ≤ Δ →
      p.2 t ∈ couplingRegion i R p.1} := by
  have hn : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun j _ => (continuous_apply j).mul (continuous_apply j))
  have hU : IsOpen (couplingRegion i R (0 : Vec d)) :=
    isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const
  have ho := ContinuousMap.isOpen_setOf_mapsTo (isCompact_Icc : IsCompact (Set.Icc 0 Δ)) hU
  have heq : {p : Vec d × Path d | ∀ t : ℝ≥0, t ≤ Δ →
      p.2 t ∈ couplingRegion i R p.1} =
      (fun p : Vec d × Path d => recenterPath p.1 p.2) ⁻¹'
        {γ : Path d | Set.MapsTo γ (Set.Icc 0 Δ) (couplingRegion i R 0)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.MapsTo, Set.mem_Icc]
    constructor
    · intro hp t ht
      simpa only [recenterPath_apply, sub_self] using
        (sub_mem_couplingRegion_iff i R p.1 (p.2 t) p.1).2 (hp t ht.2)
    · intro hp t ht
      have h := hp (show t ∈ Set.Icc 0 Δ from ⟨zero_le, ht⟩)
      exact (sub_mem_couplingRegion_iff i R p.1 (p.2 t) p.1).1
        (by simpa only [recenterPath_apply, sub_self] using h)
  rw [heq]
  exact ho.preimage Probability.continuous_path_recenter

/-- The killed segment laws form a finite kernel in the starting point whenever
all unrestricted fibres at the fixed environment are probabilities. -/
theorem exists_killedSegmentKernel {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (ω : FieldPair d)
    (hP : ∀ z : Vec d, IsProbabilityMeasure (P (z, ω))) :
    ∃ κ : ProbabilityTheory.Kernel (Vec d) (Path d),
      ProbabilityTheory.IsFiniteKernel κ ∧ ∀ z, κ z = killedSegmentLaw Δ R i P z ω := by
  classical
  let p := P.comap (fun z : Vec d => (z, ω)) (measurable_id.prodMk measurable_const)
  haveI : ProbabilityTheory.IsMarkovKernel p := ⟨hP⟩
  let S := {p : Vec d × Path d | ∀ t : ℝ≥0, t ≤ Δ →
    p.2 t ∈ couplingRegion i R p.1}
  have hS : MeasurableSet S := (isOpen_killedSegment_event Δ R i).measurableSet
  let f : Vec d → Path d → ℝ≥0∞ := fun z γ => S.indicator (fun _ => 1) (z, γ)
  have hf : Measurable (Function.uncurry f) := measurable_const.indicator hS
  have hw : ProbabilityTheory.IsFiniteKernel (p.withDensity f) :=
    ProbabilityTheory.Kernel.isFiniteKernel_withDensity_of_bounded p
      (B := 1) ENNReal.one_ne_top (by
        intro z γ
        by_cases h : (z, γ) ∈ S <;> simp [f, h])
  refine ⟨p.withDensity f, hw, ?_⟩
  intro z
  rw [ProbabilityTheory.Kernel.withDensity_apply p hf]
  change (p z).withDensity ((Prod.mk z ⁻¹' S).indicator 1) = _
  rw [withDensity_indicator_one (measurable_prodMk_left hS)]
  rfl

/-- Bounded measurable segment tests have measurable killed expectations. -/
theorem measurable_killedSegment_integral {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (P : QuenchedPathLaws d) (ω : FieldPair d)
    (hP : ∀ z : Vec d, IsProbabilityMeasure (P (z, ω)))
    (F : Path d → ℝ) (hF : Measurable F) :
    Measurable (fun z => ∫ γ, F γ ∂killedSegmentLaw Δ R i P z ω) := by
  obtain ⟨κ, hκ, hκeq⟩ := exists_killedSegmentKernel Δ R i P ω hP
  letI : ProbabilityTheory.IsFiniteKernel κ := hκ
  simp_rw [← hκeq]
  exact (hF.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'.measurable

end EinsteinRelation.Regeneration.Renewal
