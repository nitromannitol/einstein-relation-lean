import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Euclidean energy transfer for a spatial weak gradient dominated by an
L² vector field, paper/main.tex:880–883. -/
theorem memLp_euclideanNorm_of_weakGradient_domination {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) {σ : Vec d → ℝ}
    {H G : Vec d → Vec d} (hσ : HasWeakGradient U σ H)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    {C : ℝ} (hC : 0 ≤ C)
    (hdom : ∀ x ∈ U, euclideanNorm (H x) ≤ C * euclideanNorm (G x)) :
    MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict U) := by
  have hm (j : Fin d) : AEStronglyMeasurable (fun x => H x j) (volume.restrict U) :=
    (hσ j).2.1.aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun x => euclideanSq (H x)) (volume.restrict U) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => (hm j).mul (hm j)
  have hn : AEStronglyMeasurable (fun x => euclideanNorm (H x)) (volume.restrict U) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hs
  apply hG.of_le_mul hn (c := |C|)
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm (H x) from Real.sqrt_nonneg _),
    abs_of_nonneg (show 0 ≤ euclideanNorm (G x) from Real.sqrt_nonneg _),
    abs_of_nonneg hC] using hdom x hx

end EinsteinRelation.Correctors
