import EinsteinRelation.Calculus.SpatialPropertyPushforward
import Mathlib.MeasureTheory.Integral.Average

/-! Source: `paper/main.tex:693-698`. The uniform integer-radius error event is countable and measurable. -/
open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

theorem ae_integerCube_uniform_errors_of_pullback {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure B) (π : B → A) (hπ : Measurable π)
    (g : ℕ → A → Vec d → EuclideanSpace ℝ (Fin d))
    (G : A → Vec d → EuclideanSpace ℝ (Fin d))
    (hg : ∀ n, Measurable (fun p : A × Vec d => g n p.1 p.2))
    (hG : Measurable (fun p : A × Vec d => G p.1 p.2))
    (h : ∀ᵐ b ∂μ, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        ‖g n (π b) x - G (π b) x‖^2 ∂volume) ≤ (1 / 2 : ℝ)^n) :
    ∀ᵐ a ∂Measure.map π μ, ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        ‖g n a x - G a x‖^2 ∂volume) ≤ (1 / 2 : ℝ)^n := by
  have hm (n k : ℕ) : Measurable (fun a =>
      ⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
        ‖g n a x - G a x‖^2 ∂volume) := by
    have hi : Measurable (fun a =>
        ∫ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1),
          ‖g n a x - G a x‖^2 ∂volume) :=
      (((hg n).sub hG).norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
    simpa only [average_eq, smul_eq_mul] using hi.const_mul
      ((volume.restrict (Metric.closedBall (0 : Vec d) ((k : ℝ) + 1))).real Set.univ)⁻¹
  apply (ae_map_iff hπ.aemeasurable ?_).mpr h
  simp only [eventually_atTop, Set.setOf_exists, Set.setOf_forall]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ : N ≤ n => MeasurableSet.iInter fun k =>
      measurableSet_le (hm n k) measurable_const

theorem ae_scalar_integerCube_sublinearity_of_pullback {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure B) (π : B → A) (hπ : Measurable π)
    (u : A → Vec d → ℝ) (hu : Measurable (fun p : A × Vec d => u p.1 p.2))
    (h : ∀ᵐ b ∂μ, Tendsto (fun k : ℕ => (((k : ℝ) + 1)^2)⁻¹ *
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1), |u (π b) x|^2 ∂volume))
        atTop (𝓝 0)) :
    ∀ᵐ a ∂Measure.map π μ, Tendsto (fun k : ℕ => (((k : ℝ) + 1)^2)⁻¹ *
      (⨍ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1), |u a x|^2 ∂volume))
        atTop (𝓝 0) := by
  apply (ae_map_iff hπ.aemeasurable ?_).mpr h
  apply measurableSet_tendsto_fun _ measurable_const
  intro k
  have hi : Measurable (fun a =>
      ∫ x in Metric.closedBall (0 : Vec d) ((k : ℝ) + 1), |u a x|^2 ∂volume) :=
    (hu.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  simpa only [average_eq, smul_eq_mul] using
    (hi.const_mul ((volume.restrict (Metric.closedBall (0 : Vec d) ((k : ℝ) + 1))).real
      Set.univ)⁻¹).const_mul ((((k : ℝ) + 1)^2)⁻¹)


end EinsteinRelation.Correctors
