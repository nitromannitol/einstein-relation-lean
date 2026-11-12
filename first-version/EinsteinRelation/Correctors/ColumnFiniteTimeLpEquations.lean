import EinsteinRelation.Correctors.ReducedColumnScalarL2
import EinsteinRelation.Correctors.PhysicalColumnWeakEquations
import EinsteinRelation.Correctors.P53SourceSkewHeatSmoothedDivergence
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-! # Actual finite-time column equations in reduced-law L2

Source: `paper/main.tex:800–808`. All three L2 classes are constructed from
the specified actual flow. Their spatial potential and flux equations
include the initial layer and the literal physical normalization.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Finite-time potentials, integrated gradients and scalar residuals on
the actual reduced law, with both spatial weak equations and their actual
flow realizations. Source: `paper/main.tex:800–808`. -/
theorem exists_column_finite_time_L2_equations
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hu : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u p.1 p.2))
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {T : ℝ} (hT : 0 < T) :
    ∃ (v : Lp ℝ 2 (reducedEnvironmentLaw Q))
      (Y : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
      (f : Lp ℝ 2 (reducedEnvironmentLaw Q)),
      (∀ᵐ ρ ∂reducedEnvironmentLaw Q,
        HasWeakGradient Set.univ (orbit v ρ) (fun x => (Y (translate x ρ)).ofLp) ∧
        HasWeakDivergence Set.univ
          (fun x => (ρ.1 x).mulVec (unitVector i + (Y (translate x ρ)).ofLp)) (orbit f ρ)) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        v (translate x (reduce ω.1)) = r₀ * ∫ t in Set.Ioo 0 T,
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) ∧
        (Y (translate x (reduce ω.1))).ofLp =
          (fun j => ∫ t in Set.Ioo 0 T,
            G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j) ∧
        f (translate x (reduce ω.1)) = ((ellipticityScale L)⁻¹*r₀⁻¹) *
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (T,r₀⁻¹ • x) := by
  obtain ⟨v₀,f₀,hvm,hv,hfm,hf,hscalar⟩ :=
    exists_reduced_L2_column_scalar_realizations Q i u G hu hflow hT
  obtain ⟨Y₀,hYm,hY,hgradient⟩ :=
    exists_reduced_L2_integrated_gradient_realization Q i u G hG hflow hT
  let V : FieldPair d → ℝ := fun ρ => r₀*v₀ ρ
  let F : FieldPair d → ℝ := fun ρ => ((ellipticityScale L)⁻¹*r₀⁻¹)*f₀ ρ
  let Z : FieldPair d → EuclideanSpace ℝ (Fin d) := fun ρ => WithLp.toLp 2 (Y₀ ρ)
  have hV : MemLp V 2 (reducedEnvironmentLaw Q) := hv.const_mul r₀
  have hF : MemLp F 2 (reducedEnvironmentLaw Q) := hf.const_mul _
  have hZ : MemLp Z 2 (reducedEnvironmentLaw Q) :=
    memLp_piLp_iff.mpr fun j => (memLp_pi_iff.mp hY) j
  let v := hV.toLp V
  let f := hF.toLp F
  let Y := hZ.toLp Z
  have horbit : ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      v (translate x ρ) = V (translate x ρ) ∧
      Y (translate x ρ) = Z (translate x ρ) ∧
      f (translate x ρ) = F (translate x ρ) := by
    apply ae_ae_translate_of_ae _ (reducedEnvironmentLaw_stationary Q)
      (P := fun ρ => v ρ = V ρ ∧ Y ρ = Z ρ ∧ f ρ = F ρ)
    filter_upwards [hV.coeFn_toLp,hZ.coeFn_toLp,hF.coeFn_toLp] with ρ hvρ hYρ hfρ
    exact ⟨hvρ,hYρ,hfρ⟩
  have he : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      v (translate x (reduce ω.1)) = r₀ * ∫ t in Set.Ioo 0 T,
        u (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) ∧
      (Y (translate x (reduce ω.1))).ofLp =
        (fun j => ∫ t in Set.Ioo 0 T,
          G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j) ∧
      f (translate x (reduce ω.1)) = ((ellipticityScale L)⁻¹*r₀⁻¹) *
        u (project (r₀ := r₀) Q.ellipticity_parameter ω) (T,r₀⁻¹ • x) := by
    filter_upwards [hscalar,hgradient,
      (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae horbit]
      with ω hωs hωg hωr
    filter_upwards [hωs,hωg,hωr] with x hxs hxg hxr
    refine ⟨?_,?_,?_⟩
    · rw [hxr.1]
      exact congrArg (r₀*·) hxs.1
    · rw [hxr.2.1]
      exact hxg
    · rw [hxr.2.2]
      exact congrArg (((ellipticityScale L)⁻¹*r₀⁻¹)*·) hxs.2
  refine ⟨v,Y,f,?_,he⟩
  have hemb : MeasurableEmbedding (fun ω : PhysicalField d L => reduce ω.1) :=
    (Probability.measurableEmbedding_reduce d).comp
      (MeasurableEmbedding.subtype_coe (Sharpness.measurableSet_isRegular_fieldPair L))
  let P : FieldPair d → Prop := fun ρ =>
    HasWeakGradient Set.univ (orbit v ρ) (fun x => (Y (translate x ρ)).ofLp) ∧
    HasWeakDivergence Set.univ
      (fun x => (ρ.1 x).mulVec (unitVector i + (Y (translate x ρ)).ofLp)) (orbit f ρ)
  change ∀ᵐ ρ ∂reducedEnvironmentLaw Q, P ρ
  rw [← (measurePreserving_physicalReduction Q).map_eq]
  apply hemb.ae_map_iff.mpr
  filter_upwards [he,ae_physical_column_zero_time_weak_equations Q i u G hflow]
    with ω hωe hωw
  obtain ⟨hp,hflux⟩ := hωw T hT
  constructor
  · intro j
    apply (hp j).congr_ae
    · rw [Measure.restrict_univ]
      exact hωe.mono fun x hx => hx.1.symm
    · rw [Measure.restrict_univ]
      exact hωe.mono fun x hx => congrFun hx.2.1.symm j
  · apply hflux.congr_ae
    · rw [Measure.restrict_univ]
      exact hωe.mono fun x hx => by
        dsimp only
        rw [hx.2.1]
    · rw [Measure.restrict_univ]
      exact hωe.mono fun x hx => hx.2.2.symm

end EinsteinRelation.Correctors
