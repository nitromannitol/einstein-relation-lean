import EinsteinRelation.Correctors.ProbabilityAverageIntegration
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
open MeasureTheory
open scoped ENNReal
open Set
namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:743-745`. Measurable local random majorants
with a uniform moment bound control the normalized average on the region. -/
theorem lintegral_laverage_le_of_measurable_local_majorants
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) (μ : Measure X) [SFinite P] [SFinite μ]
    (U : Set X) (hU : MeasurableSet U) (hU0 : μ U ≠ 0) (hUt : μ U ≠ ⊤)
    (F : Ω → X → ℝ≥0∞) (hF : Measurable (Function.uncurry F)) (B : ℝ≥0∞)
    (hlocal : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ M : Ω → ℝ≥0∞, AEMeasurable M P ∧ (∫⁻ ω, M ω ∂P) ≤ B ∧
        ∀ᵐ ω ∂P, ∀ᵐ y ∂μ.restrict V, F ω y ≤ M ω) :
    (∫⁻ ω, (⨍⁻ x in U, F ω x ∂μ) ∂P) ≤ B := by
  classical
  choose V hVo hx M hm hB hb using fun x : U => hlocal x x.property
  have hcover : U ⊆ ⋃ x : U, V x := fun x hxU => Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  obtain ⟨t, ht, hsub⟩ := (HereditarilyLindelof_LindelofSets U).elim_countable_subcover V hVo hcover
  have hsections (x : U) : ∀ᵐ y ∂μ.restrict (V x), (∫⁻ ω, F ω y ∂P) ≤ B := by
    have hswap : ∀ᵐ y ∂μ.restrict (V x), ∀ᵐ ω ∂P, F ω y ≤ (hm x).mk (M x) ω := by
      apply (Measure.ae_ae_comm (p := fun (ω : Ω) (y : X) => F ω y ≤ (hm x).mk (M x) ω) (measurableSet_le hF ((hm x).measurable_mk.comp measurable_fst))).mp
      filter_upwards [hb x, (hm x).ae_eq_mk] with ω hω heq
      exact hω.mono fun y hy => by rwa [← heq]
    filter_upwards [hswap] with y hy
    exact (lintegral_mono_ae hy).trans_eq ((lintegral_congr_ae (hm x).ae_eq_mk).symm) |>.trans (hB x)
  have hall : ∀ᵐ y ∂μ.restrict (⋃ x ∈ t, V x), (∫⁻ ω, F ω y ∂P) ≤ B :=
    (ae_restrict_biUnion_iff V ht _).mpr fun x _ => hsections x
  have hbound := ae_restrict_of_ae_restrict_of_subset hsub hall
  exact lintegral_average_le_of_ae_section_bound P (μ.restrict U)
    (by simpa using hU0) (by simpa using hUt) F hF B hbound
end EinsteinRelation.Correctors
