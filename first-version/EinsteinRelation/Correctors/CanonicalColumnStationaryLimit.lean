import EinsteinRelation.Correctors.ColumnGradientIncrement
import EinsteinRelation.Correctors.ColumnFiniteTimeLpEquations
import EinsteinRelation.Correctors.ColumnResidualLpDecay
import EinsteinRelation.Correctors.SpecifiedColumnCopyEstimates
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentification

/-! # Identification of the actual column integral with the canonical gradient

Source: `paper/main.tex:800–808`. Actual finite-time spatial potentials and
flux equations include time zero. Sharp local gradient decay makes their
stationary L2 gradients Cauchy, and scalar decay removes the endpoint
residual. The variational limit is the repository's canonical corrector.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Actual zero-based column integrals converge strongly to the canonical
stationary corrector gradient. All finite-time potentials, residuals and
spatial equations are constructed; only the cited frozen decay and
regularity estimates and the specified measurable canonical flow enter.
Source: `paper/main.tex:800–808`. -/
theorem exists_canonical_column_stationary_approximation
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L)
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hu : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u p.1 p.2))
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (hweak : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
      HasWeakGradient Set.univ (fun x => u A (t,x)) (fun x => G A (t,x))) :
    ∃ (v : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
      (Y : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (f : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q)),
      (∀ n, ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
        HasWeakGradient Set.univ (orbit (v n) ρ) (fun x => (Y n (translate x ρ)).ofLp) ∧
        HasWeakDivergence Set.univ
          (fun x => (ρ.1 x).mulVec (unitVector i + (Y n (translate x ρ)).ofLp)) (orbit (f n) ρ)) ∧
      (∀ n, ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        v n (translate x (reduce ω.1)) = r₀ * ∫ t in Set.Ioo 0 ((n : ℝ)+1),
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) ∧
        (Y n (translate x (reduce ω.1))).ofLp =
          (fun j => ∫ t in Set.Ioo 0 ((n : ℝ)+1),
            G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j) ∧
        f n (translate x (reduce ω.1)) = ((ellipticityScale L)⁻¹*r₀⁻¹) *
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) ((n : ℝ)+1,r₀⁻¹ • x)) ∧
      Tendsto f atTop (𝓝 0) ∧
      Tendsto Y atTop (𝓝 (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) := by
  choose v Y f hw he using fun n : ℕ => exists_column_finite_time_L2_equations
    Q i u G hu hG hflow (T := (n : ℝ)+1) (by positivity)
  obtain ⟨C,hC,hbound⟩ := canonical_column_gradient_decay_and_tail hdecay hreg d hd L r₀ hL
  have hcb := hbound Q i u G hu hG hflow hweak
  have hC2 : 0 < C 2 := hC 2 (by norm_num)
  have hα : 0 < (d : ℝ)/4 := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hb (t : ℝ) (ht : 1 ≤ t) :
      eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => G A (t,x))) 2
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C 2*t^(-1-(d : ℝ)/4)) := by
    simpa using (hcb.1 0 2 t (by norm_num) ht).2
  have hi (n m : ℕ) (hnm : n ≤ m) :
      ‖Y m-Y n‖ ≤ (C 2/((d : ℝ)/4))*((n : ℝ)+1)^(-((d : ℝ)/4)) := by
    apply column_gradient_increment_bound Q i u G hG hflow hC2 hα
      (T := (n : ℝ)+1) (S := (m : ℝ)+1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (by exact_mod_cast Nat.add_le_add_right hnm 1) hb (Y m) (Y n)
    · exact (he m).mono fun ω hω => hω.mono fun x hx => hx.2.1
    · exact (he n).mono fun ω hω => hω.mono fun x hx => hx.2.1
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hb0 : Tendsto (fun n : ℕ => (C 2/((d : ℝ)/4))*((n : ℝ)+1)^(-((d : ℝ)/4)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C 2/((d : ℝ)/4))).mul ((tendsto_rpow_neg_atTop hα).comp ht)
  have hCauchy : CauchySeq Y := Metric.cauchySeq_iff'.mpr fun ε hε => by
    obtain ⟨N,hN⟩ := (hb0.eventually (gt_mem_nhds hε)).exists
    refine ⟨N,fun m hNm => ?_⟩
    rw [dist_eq_norm]
    exact (hi N m hNm).trans_lt hN
  obtain ⟨B,_,hres⟩ := column_residual_L2_decay hdecay d hd L r₀ hL
  have hf0 := (hres Q i u G hu hflow f
    (fun n => (he n).mono fun ω hω => hω.mono fun x hx => hx.2.2)).2
  refine ⟨v,Y,f,hw,he,hf0,?_⟩
  exact akmLocal_tendsto_gradient_canonical_of_spatial_potentials Q i v Y f
    (fun n => (hw n).mono fun ρ hρ => hρ.1)
    (fun n => (hw n).mono fun ρ hρ => hρ.2) hf0 hCauchy

end EinsteinRelation.Correctors
