import EinsteinRelation.Correctors.AKMParabolicIntegrability

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Global scalar and gradient energies make the duality flux integrable.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem akm_global_duality_flux_integrable {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) {I : Set ℝ} {u v : ℝ × Vec d → ℝ}
    {G H : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (I ×ˢ Set.univ)))
    (hv : MemLp v 2 (volume.restrict (I ×ˢ Set.univ)))
    (hGm : AEStronglyMeasurable G (volume.restrict (I ×ˢ Set.univ)))
    (hHm : AEStronglyMeasurable H (volume.restrict (I ×ˢ Set.univ)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (I ×ˢ Set.univ)))
    (hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (I ×ˢ Set.univ))) (j : Fin d) :
    Integrable (fun z => v z * ((A z.2).mulVec (G z)) j -
      u z * ((A z.2).mulVec (H z)) j)
      (volume.restrict (I ×ˢ Set.univ)) := by
  let μ : Measure (ℝ × Vec d) := volume.restrict (I ×ˢ Set.univ)
  have hAm (i k : Fin d) : AEStronglyMeasurable (fun z : ℝ × Vec d => A z.2 i k) μ :=
    (A.locally_integrable i k).aestronglyMeasurable.comp_snd.mono_measure
      Measure.restrict_le_self
  have hGm_comp (k : Fin d) : AEStronglyMeasurable (fun z => G z k) μ :=
    (continuous_apply k).comp_aestronglyMeasurable hGm
  have hHm_comp (k : Fin d) : AEStronglyMeasurable (fun z => H z k) μ :=
    (continuous_apply k).comp_aestronglyMeasurable hHm
  have hGm_coord : AEStronglyMeasurable (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j) μ := by
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply] using
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ => (hAm j k).mul (hGm_comp k))
  have hHm_coord : AEStronglyMeasurable (fun z : ℝ × Vec d => ((A z.2).mulVec (H z)) j) μ := by
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply] using
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ => (hAm j k).mul (hHm_comp k))
  have h_ell_lower (z : ℝ × Vec d) (ξ : Vec d) : 0 ≤ dot ξ ((A z.2).mulVec ξ) := by
    have hnonneg : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg (ξ k)
    exact hnonneg.trans (A.elliptic z.2 ξ).1
  have h_ell_upper (z : ℝ × Vec d) (ξ : Vec d) :
      dot ξ ((A z.2).mulVec ξ) ≤ K * euclideanSq ξ :=
    (A.elliptic z.2 ξ).2
  have hG_flux_memLp : MemLp (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j) 2 μ :=
    hG.of_le_mul hGm_coord (c := K)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
        have h_tri : |((A z.2).mulVec (G z)) j| ≤ euclideanNorm ((A z.2).mulVec (G z)) := by
          apply Real.abs_le_sqrt
          change ((A z.2).mulVec (G z)) j ^ 2 ≤
            ∑ k : Fin d, ((A z.2).mulVec (G z)) k * ((A z.2).mulVec (G z)) k
          rw [sq]
          exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
        exact h_tri.trans
          (mulVec_euclideanNorm_le_of_quadratic (A z.2) hK (A.symmetric z.2)
            (h_ell_lower z) (h_ell_upper z) (G z)))
  have hH_flux_memLp : MemLp (fun z : ℝ × Vec d => ((A z.2).mulVec (H z)) j) 2 μ :=
    hH.of_le_mul hHm_coord (c := K)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ euclideanNorm (H z) from Real.sqrt_nonneg _)]
        have h_tri : |((A z.2).mulVec (H z)) j| ≤ euclideanNorm ((A z.2).mulVec (H z)) := by
          apply Real.abs_le_sqrt
          change ((A z.2).mulVec (H z)) j ^ 2 ≤
            ∑ k : Fin d, ((A z.2).mulVec (H z)) k * ((A z.2).mulVec (H z)) k
          rw [sq]
          exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
        exact h_tri.trans
          (mulVec_euclideanNorm_le_of_quadratic (A z.2) hK (A.symmetric z.2)
            (h_ell_lower z) (h_ell_upper z) (H z)))
  have h_int_G : Integrable (fun z => v z * ((A z.2).mulVec (G z)) j) μ :=
    hv.integrable_mul hG_flux_memLp
  have h_int_H : Integrable (fun z => u z * ((A z.2).mulVec (H z)) j) μ :=
    hu.integrable_mul hH_flux_memLp
  exact h_int_G.sub h_int_H

end EinsteinRelation.Correctors
