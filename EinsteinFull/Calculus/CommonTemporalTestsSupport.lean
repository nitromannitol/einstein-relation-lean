import EinsteinFull.Calculus.CommonSpatialTestsSupport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.ProjIcc

/-!
# Temporal test continuity from local space-time integrability

Countable dense parameter events extend through continuous pairings. Compact
spatial multipliers need only local space-time L1, including near time zero.
These ordinary support lemmas assume no square-integrable temporal gradient.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull.CommonTemporalTests

/-- A countable dense parameter set removes the parameter-dependent null set.
The second test index need not be countable. -/
theorem ae_all_parameters_of_ae_fixed {A B X : Type*} [MeasurableSpace A]
    [TopologicalSpace X] [SecondCountableTopology X] (μ : Measure A) (S : Set X)
    (F : A → B → X → ℂ)
    (hcont : ∀ᵐ a ∂μ, ∀ b, Continuous (fun x : S => F a b x))
    (hfixed : ∀ x ∈ S, ∀ᵐ a ∂μ, ∀ b, F a b x = 0) :
    ∀ᵐ a ∂μ, ∀ x ∈ S, ∀ b, F a b x = 0 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  letI : Countable D := hDc.to_subtype
  have hD : ∀ᵐ a ∂μ, ∀ x : D, ∀ b, F a b x.1 = 0 :=
    ae_all_iff.mpr fun x => hfixed x.1 x.1.2
  filter_upwards [hcont, hD] with a hc hd
  intro x hx b
  have hclosed : IsClosed {y : S | F a b y = 0} := isClosed_eq (hc b) continuous_const
  have hsub : D ⊆ {y : S | F a b y = 0} := fun y hy => hd ⟨y, hy⟩ b
  have hcl := closure_minimal hsub hclosed
  rw [hDd.closure_eq] at hcl
  exact hcl (Set.mem_univ (⟨x, hx⟩ : S))

/-- Integration against an L1 field is continuous in the uniform temporal weight. -/
theorem continuous_integral_weight {A T : Type*} [MeasurableSpace A]
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T] [CompactSpace T]
    (μ : Measure A) {f : A → ℂ} (hf : Integrable f μ)
    {g : A → T} (hg : Measurable g) :
    Continuous (fun w : C(T, ℝ) => ∫ a, (w (g a) : ℂ) * f a ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro w₀
  apply continuousAt_of_dominated
    (bound := fun a => (‖w₀‖ + 1) * ‖f a‖)
  · exact Filter.Eventually.of_forall fun w =>
      (((Complex.continuous_ofReal.comp w.continuous).measurable.comp hg).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
  · have he : ∀ᶠ w : C(T, ℝ) in 𝓝 w₀, ‖w‖ < ‖w₀‖ + 1 :=
      (continuous_norm.tendsto w₀).eventually (gt_mem_nhds (by linarith))
    filter_upwards [he] with w hw
    exact ae_of_all _ fun a => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right ((w.norm_coe_le_norm _).trans hw.le) (norm_nonneg _)
  · exact hf.norm.const_mul _
  · exact ae_of_all _ fun a =>
      ((Complex.continuous_ofReal.comp ((ContinuousMap.evalCLM ℝ (g a)).continuous)).mul
        continuous_const).continuousAt

open EinsteinRelation

/-- A compact spatial multiplier turns local space-time L1 into global L1. -/
theorem integrable_spatial_mul {d : ℕ} {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {F : Vec d × T → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K →
      Integrable F ((volume.restrict K).prod ν))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p => F p * ψ p.1) (volume.prod ν) := by
  let K := tsupport ψ
  have hK : IsCompact K := hψc
  obtain ⟨C, hC⟩ := (hψc.isCompact_range hψ).isBounded.exists_norm_le
  have hb : ∀ x, ‖ψ x‖ ≤ C := fun x => hC _ ⟨x, rfl⟩
  have hi := (hF K hK).mul_bdd (hψ.measurable.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ fun p => hb p.1)
  have hl : IntegrableOn (fun p : Vec d × T => F p * ψ p.1)
      (K ×ˢ Set.univ) (volume.prod ν) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ, Function.comp_def] using! hi
  have he : (K ×ˢ Set.univ).indicator (fun p : Vec d × T => F p * ψ p.1) =
      fun p => F p * ψ p.1 := by
    funext p
    by_cases hp : p ∈ K ×ˢ Set.univ
    · exact Set.indicator_of_mem hp _
    · have hx : p.1 ∉ tsupport ψ := fun hx => hp ⟨hx, Set.mem_univ _⟩
      simp only [Set.indicator_of_notMem hp, image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [← integrable_indicator_iff (hK.measurableSet.prod MeasurableSet.univ), he] at hl
  exact hl

/-- Integrating a continuous temporal weight and a compact spatial multiplier
can be written as one product integral, with genuine outer integrability. -/
theorem spatial_temporal_pairing {d : ℕ} {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {F : Vec d × T → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K → Integrable F ((volume.restrict K).prod ν))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {η : T → ℝ} (hη : Measurable η) {C : ℝ} (hC : ∀ t, ‖η t‖ ≤ C) :
    Integrable (fun x => (∫ t, (η t : ℂ) * F (x, t) ∂ν) * ψ x) volume ∧
    (∫ x, (∫ t, (η t : ℂ) * F (x, t) ∂ν) * ψ x) =
      ∫ p : Vec d × T, (η p.2 : ℂ) * (F p * ψ p.1) ∂(volume.prod ν) := by
  have hi := (integrable_spatial_mul hF hψ hψc).bdd_mul
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).aestronglyMeasurable
    (ae_of_all _ fun p => by simpa only [Function.comp_apply, Complex.norm_real] using hC p.2)
  have he : (fun x => ∫ t, (η t : ℂ) * (F (x, t) * ψ x) ∂ν) =
      (fun x => (∫ t, (η t : ℂ) * F (x, t) ∂ν) * ψ x) := by
    funext x
    simp only [← mul_assoc, integral_mul_const]
  exact ⟨by simpa only [Function.comp_apply, he] using hi.integral_prod_left,
    by simpa only [Function.comp_apply, he] using (integral_prod _ hi).symm⟩

/-- Local space-time L1 makes the separated pairing continuous for uniform
continuous weights on any compact temporal parameter space. -/
theorem continuous_spatial_temporal_pairing {d : ℕ} {T Z : Type*}
    [MeasurableSpace T] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [CompactSpace Z] {ν : Measure T} [SFinite ν] {F : Vec d × T → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K → Integrable F ((volume.restrict K).prod ν))
    {ψ : Vec d → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {g : T → Z} (hg : Measurable g) :
    Continuous (fun w : C(Z, ℝ) =>
      ∫ x, (∫ t, (w (g t) : ℂ) * F (x, t) ∂ν) * ψ x) := by
  have hc := continuous_integral_weight (volume.prod ν)
    (integrable_spatial_mul hF hψ hψc) (hg.comp measurable_snd)
  have he (w : C(Z, ℝ)) := (spatial_temporal_pairing hF hψ hψc
    (w.continuous.measurable.comp hg) (fun t => w.norm_coe_le_norm (g t))).2
  exact hc.congr fun w => (he w).symm

/-- Spatial integration of a finite matrix flux can be split into its scalar
pairings when each pairing is integrable. -/
theorem integral_matrix_pairing {d : ℕ} {ν : Measure ℝ}
    {F : Fin d → Vec d × ℝ → ℂ}
    (hF : ∀ k K, IsCompact K → Integrable (F k) ((volume.restrict K).prod ν))
    (a : Fin d → Fin d → Vec d → ℂ) (ha : ∀ j k, Continuous (a j k))
    (ψ : Fin d → Vec d → ℂ) (hψ : ∀ j, Continuous (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j))
    {η : ℝ → ℝ} (hη : Measurable η) {C : ℝ} (hC : ∀ t, ‖η t‖ ≤ C)
    [SFinite ν] :
    (∫ x, ∑ j, (∑ k, a j k x * (∫ t, (η t : ℂ) * F k (x, t) ∂ν)) * ψ j x) =
      ∑ j, ∑ k, ∫ x, (∫ t, (η t : ℂ) * F k (x, t) ∂ν) * (a j k x * ψ j x) := by
  have hi (j k : Fin d) := (spatial_temporal_pairing (hF k)
    ((ha j k).fun_mul (hψ j)) ((hψc j).mul_left) hη hC).1
  simp_rw [Finset.sum_mul]
  have he (j k : Fin d) : (fun x => (a j k x *
      (∫ t, (η t : ℂ) * F k (x, t) ∂ν)) * ψ j x) =
      (fun x => (∫ t, (η t : ℂ) * F k (x, t) ∂ν) * (a j k x * ψ j x)) := by
    funext x; ring
  simp_rw [show ∀ j k x, (a j k x * (∫ t, (η t : ℂ) * F k (x, t) ∂ν)) * ψ j x =
    (∫ t, (η t : ℂ) * F k (x, t) ∂ν) * (a j k x * ψ j x) from
    fun j k x => congrFun (he j k) x]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  exact Finset.sum_congr rfl fun j _ => integral_finset_sum _ (fun k _ => hi j k)

end EinsteinFull.CommonTemporalTests
