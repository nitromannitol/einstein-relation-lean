import EinsteinFull.Calculus.U2GMPHeatAbsoluteContinuity

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- A Feller kernel inherits a fixed measure lower bound from compact-test
inequalities holding almost everywhere on an open set, at every start in it. -/
theorem u2_kernel_lower_of_ae_compact_tests {d : ℕ}
    (K : ProbabilityTheory.Kernel (Vec d) (Vec d)) [ProbabilityTheory.IsMarkovKernel K]
    (ν : Measure (Vec d)) [IsLocallyFiniteMeasure ν] [ν.InnerRegular]
    (U : Set (Vec d)) (hU : IsOpen U)
    (hcont : ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      Continuous (fun x => ∫ y, f y ∂K x))
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)).restrict U,
        (∫ y, f y ∂ν) ≤ ∫ y, f y ∂K x) :
    ∀ x ∈ U, ν ≤ K x := by
  intro x hxU
  apply u2_measure_le_of_compact_continuous_tests
  intro f hf hfc hfn
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have hc : Continuous (fun x => ∫ y, f y ∂K x) := hcont g
  have hclosed : IsClosed (Uᶜ ∪ {x : Vec d | (∫ y, f y ∂ν) ≤ ∫ y, f y ∂K x}) :=
    hU.isClosed_compl.union (isClosed_le continuous_const hc)
  have hae : ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ Uᶜ ∪ {x : Vec d | (∫ y, f y ∂ν) ≤ ∫ y, f y ∂K x} := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp (hbound f hf hfc hfn)] with x hx
    by_cases h : x ∈ U
    · exact Or.inr (hx h)
    · exact Or.inl h
  have hdense := Measure.dense_of_ae hae
  change Dense (Uᶜ ∪ {x : Vec d | (∫ y, f y ∂ν) ≤ ∫ y, f y ∂K x}) at hdense
  have hall : Uᶜ ∪ {x : Vec d | (∫ y, f y ∂ν) ≤ ∫ y, f y ∂K x} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hx : x ∈ Uᶜ ∪ {x : Vec d | (∫ y, f y ∂ν) ≤ ∫ y, f y ∂K x} := by
    rw [hall]
    exact Set.mem_univ x
  exact hx.resolve_left (by simpa using hxU)

end EinsteinFull
