import EinsteinRelation.Correctors.AKMFiniteTimeFluxIdentity
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationFiniteTime
import EinsteinRelation.Mobility.DriftBoundPointwise

/-! # The actual finite-time source-flow divergence

Source: `paper/main.tex:808–816`. The coefficient flux of the integrated
parabolic gradient has divergence equal to the difference of the original
endpoint scalar fields, on the whole spatial domain. Local integrability
and the endpoint equation are derived from the actual solution.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem locallyIntegrable_coefficient_mul {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) (j k : Fin d)
    {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x => A x j k * f x) volume := by
  intro x
  obtain ⟨s, hs, hsi⟩ := hf x
  refine ⟨s, hs, ?_⟩
  have hbound (y : Vec d) : ‖A y j k‖ ≤ K := by
    rw [Real.norm_eq_abs]
    apply abs_entry_le_of_quadratic_bounds hK.le (A y) (A.symmetric y)
    · intro ξ
      exact (show 0 ≤ euclideanSq ξ from by
        change 0 ≤ ∑ k, ξ k * ξ k
        exact Finset.sum_nonneg fun k _ => mul_self_nonneg _).trans (A.elliptic y ξ).1
    · exact fun ξ => (A.elliptic y ξ).2
  have hi := hsi.mul_bdd
    ((A.locally_integrable j k).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
    (Filter.Eventually.of_forall hbound)
  simpa only [mul_comm] using hi

/-- The literal finite-time coefficient flux solves its whole-space weak
divergence equation with the actual endpoint scalar difference.
Source: `paper/main.tex:808–816`. -/
theorem akmLocal_semigroup_time_integral_divergence {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasWeakDivergence Set.univ
      (fun x => (A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j))
      (fun x => u (b,x) - u (a,x)) := by
  have hgrad := akmLocal_semigroup_integrated_gradient hsol ha hab
  have hF (j : Fin d) : LocallyIntegrable
      (fun x => ((A x).mulVec (fun k => ∫ t in Set.Ioo a b, G (t,x) k)) j) volume := by
    have hi (k : Fin d) := locallyIntegrable_coefficient_mul hK A j k
      (locallyIntegrableOn_univ.mp (hgrad k).2.1)
    simpa only [Matrix.mulVec, dotProduct] using
      locallyIntegrable_finset_sum Finset.univ (fun k _ => hi k)
  have huc (t : ℝ) (ht : 0 < t) : Continuous (fun x => u (t,x)) :=
    hsol.1.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, Set.mem_univ _⟩)
  refine ⟨fun j => (hF j).locallyIntegrableOn _,
    ((huc b (ha.trans hab)).sub (huc a ha)).locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  have hc := hψ.2.1.isCompact.image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hs : tsupport ψ ⊆ originBall d (R + 1) := by
    intro x hx
    have hb := hbound (WithLp.toLp 2 x) ⟨x, hx, rfl⟩
    change euclideanNorm x < R + 1
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    linarith
  have htest : IsSpatialTest (originBall d (R + 1)) ψ := ⟨hψ.1, hψ.2.1, hs⟩
  have he := akmLocal_semigroup_time_integral_flux_identity hK hsol ha hab
    (by linarith : 0 < R + 1) htest
  have hleft : (∫ x in originBall d (R + 1),
      dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j)) (gradient ψ x)) =
      ∫ x, dot ((A x).mulVec (fun j => ∫ t in Set.Ioo a b, G (t,x) j)) (gradient ψ x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx (hs h))
    simp only [dot, gradient, coordinateDerivative, hd, ContinuousLinearMap.zero_apply,
      mul_zero, Finset.sum_const_zero]
  have hright (t : ℝ) : (∫ x in originBall d (R + 1), u (t,x) * ψ x) =
      ∫ x, u (t,x) * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  have hui (t : ℝ) (ht : 0 < t) : Integrable (fun x => u (t,x) * ψ x) volume :=
    ((huc t ht).mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  rw [hleft, hright a, hright b] at he
  rw [Measure.restrict_univ]
  simp_rw [sub_mul]
  rw [integral_sub (hui b (ha.trans hab)) (hui a ha)]
  linarith

end EinsteinRelation.Correctors
