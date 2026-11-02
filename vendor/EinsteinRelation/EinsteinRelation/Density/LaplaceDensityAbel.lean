import EinsteinRelation.Clock.AbelLimit
import EinsteinRelation.Clock.LaplaceIntegrationByParts
import EinsteinRelation.Density.LaplaceDensityIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact

/-! # The density limit of a bounded observable

Let `ρ_s` be the reduced Laplace-time density of the environment law `Q` at rate `s > 0`, and
let `g` be a bounded measurable function on the reduced canonical space. Writing
`G(t) = E[g(ω_t)]` for the fixed-time expectation under the annealed joint law, the density
integral `∫ ρ_s g d(map reduce Q)` equals `s ∫_{(0,∞)} e^{-st} G(t) dt` by
`integral_mul_density_eq_setIntegral_Ici`. Integration by parts in time
(`EinsteinRelation.Clock.laplace_eq_laplace_primitive`) rewrites this as
`s² ∫_{(0,∞)} e^{-st} F(t) dt` with `F(t) = ∫₀ᵗ G`. If `F(t)/t → η` as `t → ∞`, the Abel limit
`EinsteinRelation.Clock.abel_tendsto_of_bounded_rate` gives convergence to `η` as `s → 0⁺`.

This is the density limit used in the proof of the main theorem (`paper/main.tex`, lines
1185–1189).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace EinsteinRelation.Density

/-- The fixed-time expectation `t ↦ E[g(ω_t)]` of a function of the reduced observation, under
the annealed joint law of the environment and the path. -/
def observationMean {d : ℕ} (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (g : FieldPair d → ℝ) (t : ℝ) : ℝ :=
  ∫ z, g (Carriers.reducedObservationAt t.toNNReal z) ∂(Carriers.annealedCoordinateJoint Q P op)

/-- The fixed-time expectation is measurable in the time. -/
private lemma measurable_observationMean {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (g : FieldPair d → ℝ)
    (hg : Measurable g) : Measurable (observationMean Q P op g) :=
  measurable_integral_reducedObservationAt Q P op g hg

/-- A bound `|g| ≤ B` passes to the fixed-time expectation. -/
private lemma abs_observationMean_le {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (g : FieldPair d → ℝ) {B : ℝ}
    (hB : ∀ w, |g w| ≤ B) (t : ℝ) : |observationMean Q P op g t| ≤ B :=
  abs_integral_reducedObservationAt_le Q P op g hB t

/-- The fixed-time expectation is interval integrable in the time. -/
private lemma intervalIntegrable_observationMean {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (g : FieldPair d → ℝ)
    (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B) (a b : ℝ) :
    IntervalIntegrable (observationMean Q P op g) volume a b := by
  have hfin : volume (Set.uIcc a b) ≠ ⊤ :=
    (isCompact_uIcc (a := a) (b := b)).measure_lt_top.ne
  have hint : IntegrableOn (observationMean Q P op g) (Set.uIcc a b) volume :=
    Measure.integrableOn_of_bounded (M := B) hfin
      (measurable_observationMean Q P op g hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs]
        exact abs_observationMean_le Q P op g hB u)
  exact hint.intervalIntegrable

/-- The running integral `t ↦ ∫₀ᵗ E[g(ω_u)] du` is measurable in `t`. -/
private lemma measurable_primitive_observationMean {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (g : FieldPair d → ℝ)
    (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B) :
    Measurable (fun t : ℝ => ∫ u in (0:ℝ)..t, observationMean Q P op g u) :=
  (intervalIntegral.continuous_primitive
    (fun a b => intervalIntegrable_observationMean Q P op g hg hB a b) 0).measurable

/-- The running integral of a function bounded by `B` satisfies `|∫₀ᵗ E[g(ω_u)] du| ≤ B t` for
`t ≥ 0`. -/
private lemma abs_primitive_observationMean_le {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (g : FieldPair d → ℝ) {B : ℝ}
    (hB : ∀ w, |g w| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    |∫ u in (0:ℝ)..t, observationMean Q P op g u| ≤ B * t := by
  have h : ‖∫ u in (0:ℝ)..t, observationMean Q P op g u‖ ≤ B * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs]
      exact abs_observationMean_le Q P op g hB u
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h
  exact h

/-- Rewrites the density integral of a bounded observable at rate `s > 0` as
`s²` times the Laplace transform of the running integral of the fixed-time expectation. -/
private lemma integral_mul_density_eq_laplace_primitive {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (rho : {r : ℝ // 0 < r} → FieldPair d → ℝ)
    (hrho : ∀ s, Carriers.IsReducedLaplaceDensity Q P op s (rho s))
    (g : FieldPair d → ℝ) (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B)
    {s : ℝ} (hs : 0 < s) :
    ∫ w, rho ⟨s, hs⟩ w * g w ∂(Measure.map reduce Q) =
      s ^ 2 * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) *
        ∫ u in (0:ℝ)..t, observationMean Q P op g u := by
  have h1 := integral_mul_density_eq_setIntegral_Ici Q P op ⟨s, hs⟩ (rho ⟨s, hs⟩)
    (hrho ⟨s, hs⟩) g hg hB
  have h2 := EinsteinRelation.Clock.laplace_eq_laplace_primitive (observationMean Q P op g)
    (measurable_observationMean Q P op g hg) B (fun t => abs_observationMean_le Q P op g hB t) hs
  calc ∫ w, rho ⟨s, hs⟩ w * g w ∂(Measure.map reduce Q)
      = ∫ t in Set.Ici (0:ℝ), s * Real.exp (-(s * t)) * observationMean Q P op g t := h1
    _ = ∫ t in Set.Ioi (0:ℝ), s * Real.exp (-(s * t)) * observationMean Q P op g t :=
        MeasureTheory.integral_Ici_eq_integral_Ioi
    _ = ∫ t in Set.Ioi (0:ℝ), s * (Real.exp (-(s * t)) * observationMean Q P op g t) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => mul_assoc _ _ _)
    _ = s * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * observationMean Q P op g t :=
        MeasureTheory.integral_const_mul _ _
    _ = s ^ 2 * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) *
          ∫ u in (0:ℝ)..t, observationMean Q P op g u := h2

/-- **Density limit.** For reduced Laplace-time densities `ρ_s` of the environment law `Q` and a
bounded measurable observable `g`, if the fixed-time expectation `t ↦ ∫₀ᵗ E[g(ω_u)] du` has
`F(t)/t → η` as `t → ∞`, then `∫ ρ_s g d(map reduce Q) → η` as `s → 0⁺`. -/
theorem tendsto_integral_mul_density {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (rho : {r : ℝ // 0 < r} → FieldPair d → ℝ)
    (hrho : ∀ s, Carriers.IsReducedLaplaceDensity Q P op s (rho s))
    (g : FieldPair d → ℝ) (hg : Measurable g) {B : ℝ} (hB : ∀ w, |g w| ≤ B) (η : ℝ)
    (hlim : Tendsto (fun t : ℝ => (∫ u in (0:ℝ)..t, observationMean Q P op g u) / t) atTop
      (𝓝 η)) :
    Tendsto (fun s : ℝ => if hs : 0 < s then
      ∫ w, rho ⟨s, hs⟩ w * g w ∂(Measure.map reduce Q) else 0) (𝓝[>] 0) (𝓝 η) := by
  have hF_bound : ∀ t : ℝ, 0 ≤ t → |∫ u in (0:ℝ)..t, observationMean Q P op g u| ≤ B * t :=
    fun t ht => abs_primitive_observationMean_le Q P op g hB ht
  have hA := EinsteinRelation.Clock.abel_tendsto_of_bounded_rate
    (fun t : ℝ => ∫ u in (0:ℝ)..t, observationMean Q P op g u)
    (measurable_primitive_observationMean Q P op g hg hB) B η hF_bound hlim
  refine Filter.Tendsto.congr' ?_ hA
  filter_upwards [self_mem_nhdsWithin] with s hmem
  have hs' : 0 < s := Set.mem_Ioi.mp hmem
  show _ = (if hs : 0 < s then ∫ w, rho ⟨s, hs⟩ w * g w ∂(Measure.map reduce Q) else 0)
  rw [dif_pos hs', integral_mul_density_eq_laplace_primitive Q P op rho hrho g hg hB hs']

end EinsteinRelation.Density
