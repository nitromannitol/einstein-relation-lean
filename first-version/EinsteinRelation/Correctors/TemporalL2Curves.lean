import EinsteinRelation.Correctors.L2WeightedFiniteParameterCurve
import EinsteinRelation.Correctors.L2VectorCurve
import Mathlib.Analysis.Calculus.Deriv.Support

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Actual finite-interval temporal convolution is differentiable in spatial
L², with the literal differentiated kernel. Source: `paper/main.tex:798–806`. -/
theorem exists_differentiable_temporal_L2_curve {X : Type*} [MeasurableSpace X]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    {f : ℝ × X → ℝ} (hf : MemLp f 2 (μ.prod ν))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    ∃ F F' : ℝ → Lp ℝ 2 ν,
      (∀ t, (F t : X → ℝ) =ᵐ[ν] fun x => ∫ s, ρ (t-s) * f (s,x) ∂μ) ∧
      (∀ t, (F' t : X → ℝ) =ᵐ[ν] fun x => ∫ s, deriv ρ (t-s) * f (s,x) ∂μ) ∧
      ∀ t, HasDerivAt F (F' t) t := by
  obtain ⟨C,hC⟩ := hρc.exists_bound_of_continuous hρ.continuous
  obtain ⟨D,hD⟩ := hρc.deriv.exists_bound_of_continuous
    (hρ.continuous_deriv (by norm_num))
  have hC0 : 0 ≤ C := (norm_nonneg (ρ 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg (deriv ρ 0)).trans (hD 0)
  apply exists_differentiable_L2_finite_integral μ ν hf
    (fun t z => ρ (t-z.1)) (fun t z => deriv ρ (t-z.1))
    (fun t => ((hρ.continuous.measurable.comp (measurable_const.sub measurable_fst)).aestronglyMeasurable))
    (fun t => (((hρ.continuous_deriv (by norm_num)).measurable.comp
      (measurable_const.sub measurable_fst)).aestronglyMeasurable))
    (fun t z => ?_) hC0 hD0 (fun t z => by simpa only [Real.norm_eq_abs] using hC (t-z.1))
      (fun t z => by simpa only [Real.norm_eq_abs] using hD (t-z.1))
  simpa only [mul_one] using
    ((hρ.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp t
      ((hasDerivAt_id t).sub_const z.1)

/-- Assemble the temporal convolutions of all actual gradient coordinates
as one differentiable Euclidean-valued L² curve. Source: `paper/main.tex:798–806`. -/
theorem exists_differentiable_temporal_vector_L2_curve {X : Type*}
    [MeasurableSpace X] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (ν : Measure X) [IsFiniteMeasure ν] {d : ℕ} {G : ℝ × X → Fin d → ℝ}
    (hG : ∀ i, MemLp (fun z => G z i) 2 (μ.prod ν))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    ∃ F F' : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 ν,
      (∀ t i, (fun x => F t x i) =ᵐ[ν] fun x => ∫ s, ρ (t-s) * G (s,x) i ∂μ) ∧
      (∀ t i, (fun x => F' t x i) =ᵐ[ν] fun x => ∫ s, deriv ρ (t-s) * G (s,x) i ∂μ) ∧
      ∀ t, HasDerivAt F (F' t) t := by
  choose f f' hf hf' hd using fun i =>
    exists_differentiable_temporal_L2_curve μ ν (hG i) hρ hρc
  obtain ⟨F,F',hF,hF',hder⟩ := exists_differentiable_L2_euclidean_curve ν
    (fun t i => f i t) (fun t i => f' i t) (fun t i => hd i t)
  exact ⟨F,F',fun t i => (hF t i).trans (hf i t),
    fun t i => (hF' t i).trans (hf' i t),hder⟩

end EinsteinRelation.Correctors
