import EinsteinRelation.Correctors.CommonScalarOrbitTests
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Transport of spatial Sobolev properties through parameter maps

Source: `paper/main.tex:693-702`. Local square integrability, each fixed
weak test, and spatial L² convergence are measurable parameter events.
Separability supplies the common event for all weak tests after transport.
-/

open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open StationaryCurlRealization

/-- A jointly measurable field has a measurable local L² event. -/
theorem measurableSet_local_square_integrable {d : ℕ} {A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : A → Vec d → E) (hf : Measurable (fun p : A × Vec d => f p.1 p.2)) :
    MeasurableSet {a | ∀ n : ℕ, MemLp (f a) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ)))} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro n
  have he : {a | MemLp (f a) 2 (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ)))} =
      {a | Integrable (fun x => ‖f a x‖ ^ 2)
        (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ)))} := by
    ext a
    exact memLp_two_iff_integrable_sq_norm
      ((hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  rw [he]
  exact measurableSet_integrable (hf.norm.pow_const 2).stronglyMeasurable

/-- Local L² on every compact transfers through a measurable parameter map. -/
theorem ae_local_square_integrable_of_pullback {d : ℕ} {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure B) (π : B → A) (hπ : Measurable π)
    (f : A → Vec d → E) (hf : Measurable (fun p : A × Vec d => f p.1 p.2))
    (hlocal : ∀ᵐ b ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (f (π b)) 2 (volume.restrict K)) :
    ∀ᵐ a ∂Measure.map π μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (f a) 2 (volume.restrict K) := by
  have hn : ∀ᵐ a ∂Measure.map π μ, ∀ n : ℕ,
      MemLp (f a) 2 (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
    (ae_map_iff hπ.aemeasurable (measurableSet_local_square_integrable f hf)).mpr
      (hlocal.mono fun b hb n => hb _ (isCompact_closedBall _ _))
  filter_upwards [hn] with a ha
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  exact (ha n).mono_measure (Measure.restrict_mono_set volume
    (hR.trans (Metric.closedBall_subset_closedBall hn.le)))

/-- Each fixed spatial weak test has a measurable event. -/
theorem measurableSet_spatial_weak_test {d : ℕ} {A : Type*} [MeasurableSpace A]
    (f g : A → Vec d → ℝ)
    (hf : Measurable (fun p : A × Vec d => f p.1 p.2))
    (hg : Measurable (fun p : A × Vec d => g p.1 p.2))
    (i : Fin d) (ψ : SpatialTest d) :
    MeasurableSet {a | (∫ x, f a x * coordinateDerivative i ψ x) =
      -(∫ x, g a x * ψ x)} := by
  have hd : Continuous (coordinateDerivative i ψ) :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  exact measurableSet_eq_fun
    ((hf.mul (hd.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable)
    ((hg.mul (ψ.contDiff.continuous.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable.neg)

/-- Actual weak gradients transfer through fixed measurable test events;
the countable-density argument is applied after transport. -/
theorem ae_spatial_weakGradient_of_pullback {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure B) (π : B → A) (hπ : Measurable π)
    (u : A → Vec d → ℝ) (g : A → Vec d → Vec d)
    (hu : Measurable (fun p : A × Vec d => u p.1 p.2))
    (hg : Measurable (fun p : A × Vec d => g p.1 p.2))
    (hlocal : ∀ᵐ b ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (u (π b)) 2 (volume.restrict K) ∧ MemLp (g (π b)) 2 (volume.restrict K))
    (hweak : ∀ᵐ b ∂μ, HasWeakGradient Set.univ (u (π b)) (g (π b))) :
    ∀ᵐ a ∂Measure.map π μ, HasWeakGradient Set.univ (u a) (g a) := by
  apply ae_all_iff.mpr
  intro i
  have hgi : Measurable (fun p : A × Vec d => g p.1 p.2 i) :=
    (measurable_pi_apply i).comp hg
  have hlu := ae_local_square_integrable_of_pullback μ π hπ u hu
    (hlocal.mono fun b hb K hK => (hb K hK).1)
  have hlg := ae_local_square_integrable_of_pullback μ π hπ g hg
    (hlocal.mono fun b hb K hK => (hb K hK).2)
  apply SpatialScalar.ae_hasWeakPartialDerivative_of_ae_fixedTest (Measure.map π μ)
    u (fun a x => g a x i) i
  · filter_upwards [hlu, hlg] with a hua hga
    intro K hK
    exact ⟨hua K hK, ((ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).comp_memLp'
      (hga K hK))⟩
  · intro ψ
    apply (ae_map_iff hπ.aemeasurable (measurableSet_spatial_weak_test u
      (fun a x => g a x i) hu hgi i ψ)).mpr
    filter_upwards [hweak] with b hb
    simpa only [Measure.restrict_univ] using
      (hb i).2.2 ψ ⟨ψ.contDiff, ψ.hasCompactSupport, Set.subset_univ _⟩

/-- Spatial integral convergence transfers through its measurable event. -/
theorem ae_spatial_L2_limit_of_pullback {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure B) (π : B → A) (hπ : Measurable π)
    (g : ℕ → A → Vec d → EuclideanSpace ℝ (Fin d))
    (G : A → Vec d → EuclideanSpace ℝ (Fin d))
    (hg : ∀ n, Measurable (fun p : A × Vec d => g n p.1 p.2))
    (hG : Measurable (fun p : A × Vec d => G p.1 p.2))
    (K : Set (Vec d))
    (hconv : ∀ᵐ b ∂μ, Tendsto (fun n => ∫ x in K,
      ‖g n (π b) x - G (π b) x‖ ^ 2) atTop (𝓝 0)) :
    ∀ᵐ a ∂Measure.map π μ, Tendsto (fun n => ∫ x in K,
      ‖g n a x - G a x‖ ^ 2) atTop (𝓝 0) := by
  apply (ae_map_iff hπ.aemeasurable ?_).mpr hconv
  apply measurableSet_tendsto_fun _ measurable_const
  intro n
  exact (((hg n).sub hG).norm.pow_const 2).stronglyMeasurable.integral_prod_right.measurable

end EinsteinRelation.Correctors
