import EinsteinRelation.Correctors.SemigroupZeroFlux

/-! # Zero-based coefficient-column flux equation

Source: `paper/main.tex:800–808`. The finite-time potential has exactly the
flux equation needed for stationary corrector identification. Local
integrability of the coefficient flux follows from ellipticity.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem coefficient_mul_locallyIntegrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) (j k : Fin d)
    {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x => A x j k * f x) volume := by
  intro x
  obtain ⟨s,hs,hsi⟩ := hf x
  refine ⟨s,hs,?_⟩
  have hbound (y : Vec d) : ‖A y j k‖ ≤ K := by
    rw [Real.norm_eq_abs]
    apply abs_entry_le_of_quadratic_bounds hK.le (A y) (A.symmetric y)
    · intro v
      exact (euclideanSq_nonneg_fisher v).trans (A.elliptic y v).1
    · exact fun v => (A.elliptic y v).2
  have hi := hsi.mul_bdd
    ((A.locally_integrable j k).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    (.of_forall hbound)
  simpa only [mul_comm] using hi

/-- The integrated column flow satisfies its actual whole-space flux
equation with lower endpoint zero. Source: `paper/main.tex:800–808`. -/
theorem semigroup_column_time_integral_divergence_from_zero
    {d : ℕ} {K : ℝ} (hK : 0 < K) {A : Coefficient d K} (i : Fin d)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) u G)
    {B : ℝ} (hbound : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T : ℝ} (hT : 0 < T) :
    HasWeakDivergence Set.univ
      (fun x => (A x).mulVec (unitVector i + (fun j => ∫ t in Set.Ioo 0 T, G (t,x) j)))
      (fun x => u (T,x)) := by
  let V := fun x j => ∫ t in Set.Ioo 0 T, G (t,x) j
  have hgrad := semigroup_integrated_gradient_from_zero hK hsol hbound hT
  have hcol (j : Fin d) : LocallyIntegrable
      (fun x => ((A x).mulVec (unitVector i)) j) volume := by
    simpa only [unitVector,Matrix.mulVec_single_one,Matrix.col] using A.locally_integrable j i
  have hflux (j : Fin d) : LocallyIntegrable (fun x => ((A x).mulVec (V x)) j) volume := by
    have hi (k : Fin d) := coefficient_mul_locallyIntegrable hK A j k
      (locallyIntegrableOn_univ.mp (hgrad k).2.1)
    simpa only [Matrix.mulVec,dotProduct] using
      locallyIntegrable_finset_sum Finset.univ (fun k _ => hi k)
  have huc : Continuous (fun x => u (T,x)) :=
    hsol.1.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hT,Set.mem_univ _⟩)
  refine ⟨fun j => ?_,huc.locallyIntegrable.locallyIntegrableOn _,?_⟩
  · simpa only [Matrix.mulVec_add,Pi.add_apply] using
      ((hcol j).add (hflux j)).locallyIntegrableOn Set.univ
  · intro ψ hψ
    obtain ⟨n,hs⟩ := akm_compact_subset_originBall hψ.2.1.isCompact
    let R : ℝ := (n:ℝ)+1
    have hR : 0 < R := by positivity
    have hψR : IsSpatialTest (originBall d R) ψ := ⟨hψ.1,hψ.2.1,hs⟩
    have he := semigroup_time_integral_flux_identity_from_zero
      hK hsol hbound hT hR hψR
    have hleft : (∫ x in originBall d R, dot ((A x).mulVec (V x)) (gradient ψ x)) =
        ∫ x, dot ((A x).mulVec (V x)) (gradient ψ x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hs h))
      simp only [dot,gradient,coordinateDerivative,hd,ContinuousLinearMap.zero_apply,
        mul_zero,Finset.sum_const_zero]
    have hright : (∫ x in originBall d R, u (T,x)*ψ x) = ∫ x, u (T,x)*ψ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),mul_zero]
    rw [hleft,hright] at he
    have hint (F : Vec d → Vec d) (hF : ∀ j, LocallyIntegrable (fun x => F x j) volume) :
        Integrable (fun x => dot (F x) (gradient ψ x)) volume := by
      apply integrable_finset_sum Finset.univ
      intro j _
      simpa only [IntegrableOn,Measure.restrict_univ,gradient] using integrableOn_mul_spatialTest
        ((hF j).locallyIntegrableOn Set.univ) (isSpatialTest_coordinateDerivative hψ j)
    rw [Measure.restrict_univ]
    change (∫ x, dotProduct ((A x).mulVec (unitVector i + V x)) (gradient ψ x)) = _
    simp_rw [Matrix.mulVec_add,add_dotProduct]
    change (∫ x, dot ((A x).mulVec (unitVector i)) (gradient ψ x) +
      dot ((A x).mulVec (V x)) (gradient ψ x)) = _
    rw [integral_add (hint _ hcol) (hint _ hflux)]
    linarith only [he]

/-- Any specified represented actual column flow has the whole-space
zero-based potential and flux equations simultaneously at every endpoint.
Source: `paper/main.tex:800–808`. -/
theorem ae_actual_column_zero_time_weak_equations
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) :
    ∀ᵐ A ∂actualCoefficientLaw Q, ∀ T : ℝ, 0 < T →
      HasWeakGradient Set.univ (fun x => ∫ t in Set.Ioo 0 T, u A (t,x))
        (fun x j => ∫ t in Set.Ioo 0 T, G A (t,x) j) ∧
      HasWeakDivergence Set.univ
        (fun x => (A x).mulVec (unitVector i + (fun j => ∫ t in Set.Ioo 0 T, G A (t,x) j)))
        (fun x => u A (T,x)) := by
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
    with A hA hb
  intro T hT
  exact ⟨semigroup_integrated_gradient_from_zero hK hA.1 hb hT,
    semigroup_column_time_integral_divergence_from_zero hK i hA.1 hb hT⟩

end EinsteinRelation.Correctors
