import EinsteinFull.Regeneration.LaterCycleMaximum

/-!
# Coordinate velocity and quenched path laws

Coordinatewise velocity convergence is a measurable path event. The actual path marginal
of the regeneration coupling transfers its annealed almost-sure convergence to the
corresponding quenched diffusion laws.
-/

open MeasureTheory Filter EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Convergence of one coordinate of path velocity is a measurable set of paths. -/
theorem measurableSet_coordinate_velocity {d : ℕ} (i : Fin d) (v : ℝ) :
    MeasurableSet {γ : Path d | Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 v)} := by
  let A : ℕ → ℕ → Set (Path d) := fun m n =>
    ⋂ t : ℝ≥0, ⋂ (_ : (n : ℝ≥0) ≤ t),
      {γ : Path d | dist ((t : ℝ)⁻¹ * γ t i) v ≤ 1 / ((m : ℝ) + 1)}
  have hA (m n : ℕ) : IsClosed (A m n) := by
    dsimp [A]
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro _
    apply isClosed_le
    · have heval : Continuous (fun γ : Path d => γ t i) :=
        (continuous_apply i).comp (continuous_eval_const t)
      exact (heval.const_mul _).dist continuous_const
    · exact continuous_const
  have heq : {γ : Path d | Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 v)} =
      ⋂ m : ℕ, ⋃ n : ℕ, A m n := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, A]
    constructor
    · intro h m
      have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp h _ hε
      obtain ⟨n, hn⟩ := exists_nat_ge T
      refine ⟨n, fun t ht => ?_⟩
      exact (hT t (le_trans hn ht)).le
    · intro h
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨n, hn⟩ := h m
      refine ⟨(n : ℝ≥0), fun t ht => ?_⟩
      exact lt_of_le_of_lt (hn t ht) hm
  rw [heq]
  exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n => (hA m n).measurableSet

/-- Coordinate velocity under the annealed coupling transfers to almost every quenched
origin path law through the supplied path marginal. -/
theorem quenched_coordinate_velocity_of_annealed {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P) (i : Fin d) (v : ℝ)
    (hvel : ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ωz.2.1 t i) atTop (𝓝 v)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P (0, ω), Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 v) := by
  have hdis := Measure.ae_ae_of_ae_compProd hvel
  filter_upwards [hK.1, hpath.1, hdis] with ω hprob hmap hω
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω] at hω
  rw [← hmap]
  exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_coordinate_velocity i v)).mpr hω

/-- Coordinatewise quenched convergence gives the vector-valued quenched velocity. -/
theorem quenched_velocity_of_coordinates {d : ℕ}
    (Q : Measure (FieldPair d)) (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (v : Vec d)
    (h : ∀ i : Fin d, ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P ω, Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 (v i))) :
    HasQuenchedVelocity Q P v := by
  filter_upwards [ae_all_iff.mpr h] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with γ hγ
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul] using hγ i

end EinsteinFull.Regeneration
