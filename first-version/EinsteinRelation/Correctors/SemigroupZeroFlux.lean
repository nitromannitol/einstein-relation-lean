import EinsteinRelation.Correctors.SemigroupZeroPotential
import EinsteinRelation.Correctors.AKMFiniteTimeInitialTrace
import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace

/-! # The source flux identity through time zero

Source: `paper/main.tex:800–808`. The actual local gradient energy permits
Fubini down to zero. The distributional initial datum then fixes the source
flux, without choosing a time-zero gradient representative.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The literal zero-based time integral has the source's initial flux.
Source: `paper/main.tex:800–808`. -/
theorem semigroup_time_integral_flux_identity_from_zero
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {B : ℝ} (hbound : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest (originBall d R) ψ) :
    (∫ x in originBall d R,
      dot ((A x).mulVec (fun j => ∫ t in Set.Ioo 0 T, G (t,x) j)) (gradient ψ x)) =
      -(∫ x, dot (g x) (gradient ψ x)) - (∫ x in originBall d R, u (T,x)*ψ x) := by
  have hc := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hzero := semigroup_parabolic_from_zero hK hsol hbound hT hR
  let q := fun t : ℝ => ∫ x in originBall d R, dot ((A x).mulVec (G (t,x))) (gradient ψ x)
  have hqi : IntegrableOn q (Set.Ioo 0 T) :=
    (parabolicSolution_spatial_pairings_integrable hK A hzero hψ.1 hψ.2.1).2
  have hpair (t : ℝ) : (∫ x in originBall d R, u (t,x)*ψ x) = ∫ x, u (t,x)*ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψ.2.2 h)),mul_zero]
  have hψu : IsSpatialTest Set.univ ψ := ⟨hψ.1,hψ.2.1,Set.subset_univ _⟩
  have hlim : Tendsto (fun a => ∫ t in Set.Ioo a T, q t)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (-(∫ x, dot (g x) (gradient ψ x)) - (∫ x in originBall d R, u (T,x)*ψ x))) := by
    apply ((hsol.2.2 ψ hψu).sub_const (∫ x in originBall d R, u (T,x)*ψ x)).congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with a ha haT
    rw [← hpair a]
    exact (by
      rw [← parabolicSolution_time_integral_flux_pairing hK A
        (hsol.2.1 a T R ha haT hR) hψ]
      exact (akmLocal_semigroup_time_integral_flux_identity hK hsol ha haT hR hψ).symm)
  have hcover : AECover (volume.restrict (Set.Ioo 0 T)) (nhdsWithin 0 (Set.Ioi 0))
      (fun a : ℝ => Set.Ioo a T) :=
    aecover_Ioo_of_Ioo (show Tendsto (fun a : ℝ => a) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)
      from nhdsWithin_le_nhds) tendsto_const_nhds
  have he := hcover.integral_eq_of_tendsto _ hqi (hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo ha.le le_rfl)]))
  rw [parabolicSolution_time_integral_flux_pairing hK A hzero hψ]
  exact he

/-- Physical coefficient regularity discharges the entire initial-strip
energy obligation for any specified represented column flow.
Source: `paper/main.tex:800–808,842–844`. -/
theorem ae_actual_column_parabolic_from_zero
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) :
    ∀ᵐ A ∂actualCoefficientLaw Q, ∀ T R : ℝ, 0 < T → 0 < R →
      IsParabolicSolution A (Set.Ioo 0 T) (originBall d R) (u A) (G A) := by
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  filter_upwards [hflow, ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
    with A hA hb
  exact fun _ _ hT hR => semigroup_parabolic_from_zero hK hA.1 hb hT hR

/-- The same actual measurable-flow witnesses have zero-based spatial
potentials and the correct distributional source flux, simultaneously for
all positive endpoints. Source: `paper/main.tex:800–808`. -/
theorem ae_actual_column_zero_time_potential_and_flux
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) :
    ∀ᵐ A ∂actualCoefficientLaw Q, ∀ T : ℝ, 0 < T →
      HasWeakGradient Set.univ (fun x => ∫ t in Set.Ioo 0 T, u A (t,x))
        (fun x j => ∫ t in Set.Ioo 0 T, G A (t,x) j) ∧
      ∀ R : ℝ, 0 < R → ∀ ψ : Vec d → ℝ, IsSpatialTest (originBall d R) ψ →
        (∫ x in originBall d R,
          dot ((A x).mulVec (fun j => ∫ t in Set.Ioo 0 T, G A (t,x) j)) (gradient ψ x)) =
          -(∫ x, dot ((A x).mulVec (unitVector i)) (gradient ψ x)) -
            (∫ x in originBall d R, u A (T,x)*ψ x) := by
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  filter_upwards [hflow, ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
    with A hA hb
  intro T hT
  exact ⟨semigroup_integrated_gradient_from_zero hK hA.1 hb hT,
    fun R hR ψ hψ => semigroup_time_integral_flux_identity_from_zero
      hK hA.1 hb hT hR hψ⟩

end EinsteinRelation.Correctors
