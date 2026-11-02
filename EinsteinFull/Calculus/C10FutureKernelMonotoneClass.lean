import Batteries.Tactic.Lint.Basic
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Local measurable versions of indicator masses yield local versions of bounded test integrals.
The finite ambient measure and sigma-algebra inclusion are retained to match the consumer interface;
the simple-function limit argument itself does not require them. -/
@[nolint unusedArguments]
theorem local_kernel_bounded_test_version_of_indicator_versions
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω)
    (hm : m ≤ ‹MeasurableSpace Ω›) (K : Ω → Measure S)
    (hK : ∀ ω, (K ω) Set.univ ≤ 1)
    (hlocal : ∀ s : Set S, MeasurableSet s → ∃ B : Ω → ℝ,
      Measurable[m] B ∧ (fun ω => ((K ω) s).toReal) =ᵐ[μ] B) :
    ∀ Φ : S → ℝ, Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∃ B : Ω → ℝ, Measurable[m] B ∧
        (fun ω => ∫ z, Φ z ∂K ω) =ᵐ[μ] B := by
  classical
  intro Φ hΦ hbound
  choose V hVm hVeq using hlocal
  have hsimp (f : SimpleFunc S ℝ) : ∃ B : Ω → ℝ, Measurable[m] B ∧
      (fun ω => f.integral (K ω)) =ᵐ[μ] B := by
    refine ⟨fun ω => ∑ x ∈ f.range, V (f ⁻¹' {x}) (f.measurableSet_fiber x) ω * x, ?_, ?_⟩
    · exact Finset.measurable_sum _ (fun x hx =>
        (hVm (f ⁻¹' {x}) (f.measurableSet_fiber x)).mul measurable_const)
    · have heq := (eventually_all_finset f.range).2 (fun x hx =>
        hVeq (f ⁻¹' {x}) (f.measurableSet_fiber x))
      filter_upwards [heq] with ω hω
      rw [SimpleFunc.integral_eq]
      exact Finset.sum_congr rfl (fun x hx => by
        rw [Measure.real, hω x hx, smul_eq_mul])
  let f : ℕ → SimpleFunc S ℝ := SimpleFunc.approxOn Φ hΦ (Set.range Φ ∪ {0}) 0 (by simp)
  choose B hBm hBeq using fun n => hsimp (f n)
  refine ⟨fun ω => limUnder atTop (fun n => B n ω),
    (StronglyMeasurable.limUnder (fun n => (hBm n).stronglyMeasurable)).measurable, ?_⟩
  have heq := ae_all_iff.2 hBeq
  filter_upwards [heq] with ω hω
  have : IsFiniteMeasure (K ω) := ⟨(hK ω).trans_lt ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := hbound
  have hi : Integrable Φ (K ω) := Integrable.of_bound hΦ.aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have ht := tendsto_integral_approxOn_of_measurable_of_range_subset hΦ hi
    (Set.range Φ ∪ {0}) (Subset.refl _)
  have htB : Tendsto (fun n => B n ω) atTop (𝓝 (∫ z, Φ z ∂K ω)) := by
    simpa only [← hω] using ht
  exact htB.limUnder_eq.symm
end EinsteinFull.Blueprint
