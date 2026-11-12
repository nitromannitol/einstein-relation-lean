import EinsteinRelation.Correctors.ReducedIntegratedGradientL2

/-! # Reduced-law L2 scalar potentials and residuals

Source: `paper/main.tex:800–808,842–849`. The actual uniform scalar bound
and covariance give reduced-law observables for the finite-time potential
and its endpoint residual. These use the same specified column flow as
the gradient construction.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Both scalar quantities in the finite-time column equations have actual
stationary reduced-law L2 representatives. Spatial scaling is explicit;
the multiplicative physical normalization can subsequently be applied to
these representatives. Source: `paper/main.tex:800–808`. -/
theorem exists_reduced_L2_column_scalar_realizations
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hu : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {T : ℝ} (hT : 0 < T) :
    ∃ v f : FieldPair d → ℝ,
      Measurable v ∧ MemLp v 2 (reducedEnvironmentLaw Q) ∧
      Measurable f ∧ MemLp f 2 (reducedEnvironmentLaw Q) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        v (translate x (reduce ω.1)) = ∫ t in Set.Ioo 0 T,
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) ∧
        f (translate x (reduce ω.1)) =
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) (T,r₀⁻¹ • x) := by
  let B : ℝ := (d : ℝ)*akmColumnLipschitzConstant d L r₀
  let F (A : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) := u A (T,x)
  have hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      F p.1 p.2) :=
    hu.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hb := ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow
  have hFb : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ x, ‖F A x‖ ≤ B := by
    filter_upwards [hb] with A hA
    exact fun x => by simpa only [F,B,Real.norm_eq_abs] using hA T hT x
  have hFc (z : Vec d) : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)), F (translateCoefficient z A) x = F A (x+z) := by
    filter_upwards [ae_actual_column_flow_and_integrated_gradient_covariant
      Q i u G hflow z] with A hA
    exact ae_of_all _ fun x => by simpa only [F,add_comm] using hA.1 T hT x
  obtain ⟨f,hfm,hfLp,hfe⟩ := exists_reduced_L2_realization_of_bounded_covariant_field
    Q F hF hFb hFc
  let V (A : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :=
    ∫ t in Set.Ioo 0 T, u A (t,x)
  have hV : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d =>
      V p.1 p.2) := by
    have hm : Measurable (fun p :
        (Coefficient d (AKMUpperEllipticity L) × Vec d) × ℝ => u p.1.1 (p.2,p.1.2)) :=
      hu.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hVb : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ x, ‖V A x‖ ≤ T*B := by
    filter_upwards [hb] with A hA
    intro x
    have hh := norm_setIntegral_le_of_norm_le_const_ae (f := fun t => u A (t,x)) (C := B)
      (show volume (Set.Ioo (0 : ℝ) T) < ⊤ from measure_Ioo_lt_top)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        simpa only [B,Real.norm_eq_abs] using hA t ht.1 x)
    simpa only [V,Real.volume_real_Ioo_of_le hT.le,sub_zero,mul_comm] using hh
  have hVc (z : Vec d) : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)), V (translateCoefficient z A) x = V A (x+z) := by
    filter_upwards [ae_actual_column_flow_and_integrated_gradient_covariant
      Q i u G hflow z] with A hA
    refine ae_of_all _ fun x => integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [add_comm] using hA.1 t ht.1 x
  obtain ⟨v,hvm,hvLp,hve⟩ := exists_reduced_L2_realization_of_bounded_covariant_field
    Q V hV hVb hVc
  refine ⟨v,f,hvm,hvLp,hfm,hfLp,?_⟩
  filter_upwards [hve,hfe] with ω hωv hωf
  filter_upwards [hωv,hωf] with x hxv hxf
  exact ⟨hxv,hxf⟩

end EinsteinRelation.Correctors
