import EinsteinRelation.Correctors.AKMHeatKernelGaussianData
import EinsteinRelation.Correctors.AKMHeatKernelConsequences
import EinsteinRelation.Correctors.AKMHeatKernelLebesguePoint
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! # Almost-everywhere initial convergence for bounded data

Source: AKM Proposition E.1, (E.10)–(E.11), p. 501;
`paper/main.tex:850`. Lebesgue differentiation is applied on Euclidean
space and transported back by the volume-preserving coordinate map.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Almost every point of bounded measurable data is a Euclidean Lebesgue point.
Source: AKM (E.11), p. 501; `paper/main.tex:850`. -/
theorem akm_bounded_ae_lebesgue_points {d : ℕ} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hb : ∀ᵐ x ∂volume, |f x| ≤ B) :
    ∀ᵐ y ∂volume, IsHeatKernelLebesguePoint f y := by
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun z => f (WithLp.ofLp z)
  have hF : AEStronglyMeasurable F volume :=
    hf.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin d))
  have hB : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |F z| ≤ B :=
    (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae hb
  have hl : LocallyIntegrable F volume :=
    (memLp_top_of_bound hF B (by simpa only [Real.norm_eq_abs] using hB)).locallyIntegrable
      (by simp)
  have hd := (Besicovitch.vitaliFamily
    (volume : Measure (EuclideanSpace ℝ (Fin d)))).ae_tendsto_average_norm_sub hl
  have hlim : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      Tendsto (fun r : ℝ => ⨍ w in Metric.closedBall z r, |F w - F z| ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    filter_upwards [hd] with z hz
    simpa only [Real.norm_eq_abs] using hz.comp (Besicovitch.tendsto_filterAt volume z)
  have hback := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae hlim
  simpa only [IsHeatKernelLebesguePoint, F, WithLp.ofLp_toLp] using hback

/-- Bounded data have the scalar initial limit of Proposition E.1 almost
everywhere. Source: AKM (E.10)–(E.11), p. 501; `paper/main.tex:850`. -/
theorem akm_heatKernel_initial_of_bounded {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hB : ∀ᵐ x ∂volume, |f x| ≤ B) :
    ∀ᵐ x ∂volume, Tendsto (fun t => ∫ y, P t x y * f y ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (f x)) := by
  have hfl : LocallyIntegrable f volume :=
    (memLp_top_of_bound hf B (by simpa only [Real.norm_eq_abs] using hB)).locallyIntegrable
      (by simp)
  filter_upwards [akm_bounded_ae_lebesgue_points hf hB] with x hx
  exact akm_heatKernel_initial_at_lebesgue_point h hfl
    ⟨1, zero_le_one, by simpa only [neg_mul, one_mul] using
      akm_bounded_gaussian_integrable hf hB x⟩ hx

end EinsteinRelation.Correctors
