import EinsteinRelation.Correctors.StationarySpatialHorizontal
import EinsteinRelation.Correctors.StationarySpatialDivergenceFull
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Mobility.DriftWeakDivergence

/-! # Horizontal equations for stationary local correctors

Source: `paper/main.tex:926–938`. The spatial scalar and row-divergence
equations of the center averages give the exact horizontal equations in
Proposition 5.3. Square integrability of their flux residual follows from
the actual coefficient bound and the four fields' square integrability.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The spatial equations of stationary local fields give the precise
horizontal local-corrector equations, including the coefficient at zero,
the common mean flux and the error. Source: `paper/main.tex:926–938`. -/
theorem stationary_localFlux_equations {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (φ : FieldPair d → ℝ) (S : FieldPair d → Mat d)
    (G F : FieldPair d → Vec d)
    (hφm : Measurable φ) (hSm : Measurable S)
    (hGm : Measurable G) (hFm : Measurable F)
    (hφ2 : MemLp φ 2 (reducedEnvironmentLaw Q))
    (hS2 : ∀ j k, MemLp (fun ω => S ω j k) 2 (reducedEnvironmentLaw Q))
    (hG2 : ∀ j, MemLp (fun ω => G ω j) 2 (reducedEnvironmentLaw Q))
    (hF2 : ∀ j, MemLp (fun ω => F ω j) 2 (reducedEnvironmentLaw Q))
    (hspatial : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakGradient Set.univ (orbit φ ω) (fun x => G (translate x ω)) ∧
        HasWeakRowDivergence Set.univ (fun x => S (translate x ω))
          (fun x => (ω.1 x).mulVec (unitVector i + G (translate x ω)) -
            (expectedCorrectorFlux Q i).ofLp - F (translate x ω))) :
    HasWeakHorizontalGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) φ G ∧
      ∀ j, HasWeakHorizontalDivergence (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) (fun ω k => S ω j k)
        (fun ω => (∑ k, (ω.1 0) j k * (unitVector i k + G ω k)) -
          (expectedCorrectorFlux Q i).ofLp j - F ω j) := by
  let q : FieldPair d → Vec d := fun ω =>
    (ω.1 0).mulVec (unitVector i + G ω) - (expectedCorrectorFlux Q i).ofLp - F ω
  have hqm : Measurable q := by
    apply measurable_pi_lambda
    intro j
    apply Measurable.sub _ ((measurable_pi_apply j).comp hFm)
    apply Measurable.sub _ measurable_const
    change Measurable (fun ω => ∑ k, (ω.1 0) j k * (unitVector i k + G ω k))
    apply Finset.measurable_fun_sum
    intro k _
    have hA : Measurable (fun ω : FieldPair d => ω.1 0 j k) :=
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
    exact hA.mul (measurable_const.add ((measurable_pi_apply k).comp hGm))
  obtain ⟨K, hK0, hK⟩ := DriftH5.exists_ae_abs_entry_le d Λ₀ r₀
  have hq2 : ∀ j, MemLp (fun ω => q ω j) 2 (reducedEnvironmentLaw Q) := by
    intro j
    have hprod (k : Fin d) : MemLp
        (fun ω : FieldPair d => (ω.1 0) j k * (unitVector i k + G ω k)) 2
        (reducedEnvironmentLaw Q) := by
      have hbase := (memLp_const (unitVector i k) :
        MemLp (fun _ : FieldPair d => unitVector i k) 2 (reducedEnvironmentLaw Q)).add (hG2 k)
      have hAm : Measurable (fun ω : FieldPair d => ω.1 0 j k) :=
        (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
      apply (hbase.const_mul K).of_le
        (hAm.aestronglyMeasurable.mul hbase.aestronglyMeasurable)
      filter_upwards [hK Q] with ω hω
      simp only [Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
      exact mul_le_mul_of_nonneg_right (hω j k) (abs_nonneg _)
    simpa only [q, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.add_apply] using
      (((memLp_finset_sum Finset.univ fun k _ => hprod k).sub
        (memLp_const ((expectedCorrectorFlux Q i).ofLp j))).sub (hF2 j))
  refine ⟨weakHorizontalGradient_of_spatial (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) hφm hGm hφ2 hG2
    (hspatial.mono fun _ h => h.1), ?_⟩
  change ∀ j, HasWeakHorizontalDivergence (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (fun ω k => S ω j k) (fun ω => q ω j)
  apply weakHorizontalRowDivergence_of_spatial (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) hSm hqm hS2 hq2
  filter_upwards [hspatial] with ω hω
  convert hω.2 using 1
  ext x j
  simp only [q, Pi.sub_apply, translate_matrix, add_zero]

end EinsteinRelation.Correctors
