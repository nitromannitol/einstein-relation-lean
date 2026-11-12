import EinsteinRelation.Correctors.EuclideanTimeSpaceCauchy
import EinsteinRelation.Entropy.FisherCauchySchwarz
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The power-cutoff dissipation controls the unweighted gradient on its
plateau, including integrability at time zero. Source: `paper/main.tex:848–856`. -/
theorem power_cutoff_plateau_spacetime_energy
    {d n : ℕ} {I : Set ℝ} {U V : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (χ : Vec d → ℝ) (hχm : Measurable χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχV : ∀ x ∈ V, χ x = 1)
    (G : ℝ × Vec d → Vec d) (hGm : Measurable G)
    (hslice : ∀ᵐ t ∂volume.restrict I,
      Integrable (fun x => χ x^(2*n) * euclideanSq (G (t,x))) (volume.restrict U))
    (henergy : Integrable (fun t => ∫ x in U,
      χ x^(2*n) * euclideanSq (G (t,x))) (volume.restrict I)) :
    MemLp G 2 ((volume.restrict I).prod (volume.restrict V)) ∧
      (∫ t in I, ∫ x in V, euclideanSq (G (t,x))) ≤
        ∫ t in I, ∫ x in U, χ x^(2*n) * euclideanSq (G (t,x)) := by
  let e := fun z : ℝ × Vec d => χ z.2^(2*n) * euclideanSq (G z)
  have he0 (z) : 0 ≤ e z :=
    mul_nonneg (pow_nonneg (hχ0 _) _) (euclideanSq_nonneg_fisher _)
  have hem : Measurable e := by
    have hsq : Measurable (fun z => euclideanSq (G z)) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hGm).mul ((measurable_pi_apply j).comp hGm)
    exact ((hχm.comp measurable_snd).pow_const (2*n)).mul hsq
  have he : Integrable e ((volume.restrict I).prod (volume.restrict U)) := by
    apply (integrable_prod_iff hem.aestronglyMeasurable).mpr
    refine ⟨hslice, henergy.congr ?_⟩
    exact Filter.Eventually.of_forall fun t =>
      integral_congr_ae (Filter.Eventually.of_forall fun x =>
        (Real.norm_of_nonneg (he0 (t,x))).symm)
  have he' := he
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at he'
  have hev := he'.mono_measure
    (Measure.restrict_mono_set volume (Set.prod_mono (Set.Subset.refl I) hVU))
  have heq : e =ᵐ[volume.restrict (I ×ˢ V)] fun z => euclideanSq (G z) := by
    filter_upwards [ae_restrict_mem (hI.prod hV)] with z hz
    simp only [e, hχV z.2 hz.2, one_pow, one_mul]
  have hsq := hev.congr heq
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hsq
  have hnorm : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict V)) := by
    have hm : Measurable (fun z => euclideanNorm (G z)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using hsq
  have hv : MemLp G 2 ((volume.restrict I).prod (volume.restrict V)) := by
    apply hnorm.of_le hGm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      change (G z j)^2 ≤ ∑ k, G z k * G z k
      rw [sq]
      exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
  refine ⟨hv, ?_⟩
  have hle := setIntegral_mono_set he'
    ((ae_restrict_iff' (hI.prod hU)).mpr (Filter.Eventually.of_forall fun z _ => he0 z))
    (Filter.Eventually.of_forall (show I ×ˢ V ⊆ I ×ˢ U from
      Set.prod_mono (Set.Subset.refl I) hVU))
  change (∫ z in I ×ˢ V, e z) ≤ (∫ z in I ×ˢ U, e z) at hle
  have hleft : (∫ z in I ×ˢ V, e z) = ∫ z, euclideanSq (G z)
      ∂((volume.restrict I).prod (volume.restrict V)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact integral_congr_ae heq
  rw [hleft, integral_prod _ hsq] at hle
  simpa only [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ he] using hle

end EinsteinRelation.Correctors
