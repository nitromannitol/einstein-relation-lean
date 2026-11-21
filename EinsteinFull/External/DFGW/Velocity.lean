import EinsteinFull.External.DFGW.Trajectory

/-! # Centering of the mean forward velocity

The strong `L¹` limit defining the mean forward velocity inherits the zero mean of the
antisymmetric increments.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The mean forward velocity of a reversible antisymmetric family has zero mean. -/
theorem integral_velocity_eq_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0)) :
    ∫ x, φ x ∂μ = 0 := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hφint : Integrable φ μ := hφ.integrable one_le_two
  have hev : Measurable (fun η : C(ℝ, S) => η 0) := (continuous_eval_const 0).measurable
  have hφpath : Integrable (fun η : C(ℝ, S) => φ (η 0)) P := by
    apply (integrable_map_measure (by rw [hP.marginal]; exact hφint.aestronglyMeasurable) hev.aemeasurable).1
    rw [hP.marginal]
    exact hφint
  have hφmap : (∫ η : C(ℝ, S), φ (η 0) ∂P) = ∫ x, φ x ∂μ := by
    have h := integral_map (μ := P) hev.aemeasurable (f := φ) (by
      rw [hP.marginal]
      exact hφint.aestronglyMeasurable)
    rw [hP.marginal] at h
    exact h.symm
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le 0
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ‖∫ x, φ x ∂μ‖ ≤
        ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hcond : Integrable (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) P :=
      integrable_condExp
    have hzero : (∫ η, (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η ∂P) = 0 := by
      rw [integral_condExp hσ, integral_increment_eq_zero hP hX hδ.le]
    have hs := hcond.smul δ⁻¹
    have hsint : (∫ η, (δ⁻¹ • P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η ∂P) =
        δ⁻¹ • (∫ η, (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η ∂P) := by
      simpa only [Pi.smul_apply] using
        (integral_smul δ⁻¹ (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]))
    have h := norm_integral_le_integral_norm (μ := P)
      (fun η => δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0))
    change ‖∫ η, ((δ⁻¹ • P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η -
      φ (η 0)) ∂P‖ ≤ _ at h
    rw [integral_sub hs hφpath, hsint, hzero, smul_zero,
      zero_sub, norm_neg, hφmap] at h
    exact h
  have hzero : ‖∫ x, φ x ∂μ‖ ≤ 0 := ge_of_tendsto hlim hbound
  exact norm_le_zero_iff.mp hzero

end EinsteinFull.External.DFGW
