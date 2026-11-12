import EinsteinRelation.Correctors.KernelSpatialTranslation
import EinsteinRelation.Correctors.AKMCanonicalFlowUniqueness
import EinsteinRelation.Correctors.SemigroupZeroDivergence
import EinsteinRelation.Calculus.WeakGradientTranslation
import EinsteinRelation.Calculus.WeakGradientUniqueness
import EinsteinRelation.Correctors.AKMCarrierIdentificationTransport

/-! # Covariance of the actual represented column flow

Source: `paper/main.tex:777–808,842–849`. Translation of E.1 and the proved
kernel uniqueness theorem identify the specified scalar flows. Their
actual time-integrated weak gradients are therefore covariant as well,
including the initial layer. No covariance premise on selected kernels
or uniqueness premise for arbitrary weak parabolic solutions is used.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The literal Green-gradient representation survives spatial translation.
Source: `paper/main.tex:777–784`; AKM (9.2), p. 347. -/
theorem canonicalKernelRepresentation_spatial_translation
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} (hrep : HasCanonicalKernelRepresentation A g u) (v : Vec d) :
    HasCanonicalKernelRepresentation (translateCoefficient v A) (fun x => g (v+x))
      (fun z => u (z.1,v+z.2)) := by
  obtain ⟨C,P,X,Y,H,hC,hP,hu⟩ := hrep
  refine ⟨C,(fun t x y => P t (v+x) (v+y)),
    (fun t x y => X t (v+x) (v+y)),(fun t x y => Y t (v+x) (v+y)),
    (fun t x y => H t (v+x) (v+y)),hC,
    heatKernelProperties_spatial_translation hP v,?_⟩
  intro t ht x
  obtain ⟨hi,he⟩ := hu t ht (v+x)
  exact ⟨(measurePreserving_add_left volume v).integrable_comp_of_integrable hi,
    he.trans ((congrArg Neg.neg (integral_add_left_eq_self
      (fun y => dot (g y) (Y t (v+x) y)) v)).symm)⟩

/-- Specified continuous column flows are covariant at every positive time
and every spatial point, independently of the kernels chosen to represent
them. Source: `paper/main.tex:779–808,842`. -/
theorem canonical_column_flow_covariant {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} (i : Fin d) (v : Vec d)
    {u w : ℝ × Vec d → ℝ} {G H : ℝ × Vec d → Vec d}
    (hu : IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) u G)
    (hw : IsSemigroupSolution (translateCoefficient v A)
      (fun x => ((translateCoefficient v A) x).mulVec (unitVector i)) w H)
    (hurep : HasCanonicalKernelRepresentation A
      (fun x => (A x).mulVec (unitVector i)) u)
    (hwrep : HasCanonicalKernelRepresentation (translateCoefficient v A)
      (fun x => ((translateCoefficient v A) x).mulVec (unitVector i)) w) :
    ∀ t : ℝ, 0 < t → ∀ x : Vec d, w (t,x) = u (t,v+x) := by
  exact canonicalKernelRepresentations_eq hK hw.1
    (semigroupSolution_spatial_translation hu v).1 hwrep
    (canonicalKernelRepresentation_spatial_translation hurep v)

/-- The zero-based finite-time gradients of the same represented column
flows inherit covariance from their actual weak scalar potentials.
Source: `paper/main.tex:800–808,842–849`. -/
theorem canonical_column_integrated_gradient_covariant
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} (i : Fin d) (v : Vec d)
    {u w : ℝ × Vec d → ℝ} {G H : ℝ × Vec d → Vec d}
    (hu : IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) u G)
    (hw : IsSemigroupSolution (translateCoefficient v A)
      (fun x => ((translateCoefficient v A) x).mulVec (unitVector i)) w H)
    (hurep : HasCanonicalKernelRepresentation A
      (fun x => (A x).mulVec (unitVector i)) u)
    (hwrep : HasCanonicalKernelRepresentation (translateCoefficient v A)
      (fun x => ((translateCoefficient v A) x).mulVec (unitVector i)) w)
    {B : ℝ} (hbound : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T : ℝ} (hT : 0 < T) :
    (fun x j => ∫ t in Set.Ioo 0 T, H (t,x) j) =ᵐ[volume]
      (fun x j => ∫ t in Set.Ioo 0 T, G (t,v+x) j) := by
  have hcov := canonical_column_flow_covariant hK i v hu hw hurep hwrep
  have hwb (t : ℝ) (ht : 0 < t) (x : Vec d) : |w (t,x)| ≤ B := by
    rw [hcov t ht x]
    exact hbound t ht (v+x)
  have hgrad := (semigroup_integrated_gradient_from_zero hK hu hbound hT).translated v
  have he : (fun x => ∫ t in Set.Ioo 0 T, u (t,v+x)) =
      (fun x => ∫ t in Set.Ioo 0 T, w (t,x)) := by
    funext x
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hcov t ht.1 x).symm
  change HasWeakGradient Set.univ (fun x => ∫ t in Set.Ioo 0 T, u (t,v+x))
    (fun x j => ∫ t in Set.Ioo 0 T, G (t,v+x) j) at hgrad
  rw [he] at hgrad
  exact (semigroup_integrated_gradient_from_zero hK hw hwb hT).ae_eq_of_same_potential hgrad

/-- Any specified actual column family is covariant almost surely for
each real spatial shift. Both the scalar flow and its zero-based gradient
integrals use the original witnesses. Source: `paper/main.tex:779–808`. -/
theorem ae_actual_column_flow_and_integrated_gradient_covariant
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (v : Vec d) :
    ∀ᵐ A ∂actualCoefficientLaw Q,
      (∀ t : ℝ, 0 < t → ∀ x : Vec d,
        u (translateCoefficient v A) (t,x) = u A (t,v+x)) ∧
      (∀ T : ℝ, 0 < T →
        (fun x j => ∫ t in Set.Ioo 0 T, G (translateCoefficient v A) (t,x) j) =ᵐ[volume]
          (fun x j => ∫ t in Set.Ioo 0 T, G A (t,v+x) j)) := by
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hpres : MeasurePreserving (translateCoefficient v)
      (actualCoefficientLaw Q) (actualCoefficientLaw Q) :=
    ⟨measurable_translateCoefficient v,actualCoefficientLaw_translation_invariant_real Q v⟩
  filter_upwards [hflow,hpres.quasiMeasurePreserving.ae hflow,
    ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow] with A hA hAv hb
  exact ⟨canonical_column_flow_covariant hK i v hA.1 hAv.1 hA.2 hAv.2,
    fun _ hT => canonical_column_integrated_gradient_covariant
      hK i v hA.1 hAv.1 hA.2 hAv.2 hb hT⟩

/-- The zero-based integrated gradients satisfy the actual source's
stationary-field predicate, with covariance discharged by kernel uniqueness.
Source: `paper/main.tex:800–808`. -/
theorem actual_column_integrated_gradient_stationary
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {T : ℝ} (hT : 0 < T) :
    IsStationaryField (actualCoefficientLaw Q)
      (fun A x j => ∫ t in Set.Ioo 0 T, G A (t,x) j) := by
  refine ⟨?_,?_⟩
  · apply measurable_pi_lambda
    intro j
    have hm : Measurable (fun p :
        (Coefficient d (AKMUpperEllipticity L) × Vec d) × ℝ => G p.1.1 (p.2,p.1.2) j) :=
      (measurable_pi_apply j).comp (hG.comp
        (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  · intro z
    filter_upwards [ae_actual_column_flow_and_integrated_gradient_covariant
      Q i u G hflow (latticeShift z)] with A hA
    filter_upwards [hA.2 T hT] with x hx
    simpa only [add_comm] using hx.symm

end EinsteinRelation.Correctors
