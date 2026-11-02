import EinsteinRelation.Correctors.AKMHeatKernelWeakIdentification
import EinsteinRelation.Correctors.AKML2MollifiedPairing

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Actual whole-space L² weak divergence can be paired with compact H¹
functions. Source: `paper/main.tex:792`; AKM Lemma 8.2 energy testing. -/
theorem weakDivergence_test_compact_H1 {d : ℕ}
    {F Df : Vec d → Vec d} {h f : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ F h)
    (hweak : HasWeakGradient Set.univ f Df)
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (hDf : ∀ i, MemLp (fun x => Df x i) 2 volume)
    (hF : ∀ i, MemLp (fun x => F x i) 2 volume)
    (hh : MemLp h 2 volume) :
    (∫ x, dot (F x) (Df x)) = -(∫ x, h x * f x) := by
  have hfi : Integrable f volume := by
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    exact (hf.locallyIntegrable one_le_two).integrableOn_isCompact hfc
  let ρ : ℕ → Vec d → ℝ := fun n => (akmTraceBump d n).normed volume
  have hρ n : ContDiff ℝ (⊤ : ℕ∞) (ρ n) := (akmTraceBump d n).contDiff_normed
  have hρc n : HasCompactSupport (ρ n) := (akmTraceBump d n).hasCompactSupport_normed
  have hlim i := akm_L2_mollification_pairing_tendsto (hF i) (hDf i)
  have hright := akm_L2_mollification_pairing_tendsto hh hf
  have heq (n : ℕ) : (∑ i, ∫ x, F x i * (∫ y, Df y i * ρ n (x-y))) =
      -(∫ x, h x * (∫ y, f y * ρ n (x-y))) := by
    have htest := hdiv.2.2 _ (akm_convolution_isSpatialTest hfi hfc (hρ n) (hρc n))
    simp only [Measure.restrict_univ] at htest
    rw [← integral_finset_sum _ (fun i _ => (hlim i).1 n)]
    convert htest using 1
    apply integral_congr_ae
    filter_upwards with x
    unfold dot gradient
    apply Finset.sum_congr rfl
    intro i _
    rw [akm_coordinateDerivative_convolution hfi hweak (hρ n) (hρc n)]
  have he := tendsto_nhds_unique
    (tendsto_finset_sum Finset.univ fun i _ => (hlim i).2)
    (hright.2.neg.congr fun n => (heq n).symm)
  unfold dot
  rw [integral_finset_sum _ (fun i _ => show Integrable (fun x => F x i * Df x i) volume
    from (hF i).integrable_mul (hDf i))]
  exact he

end EinsteinRelation.Correctors
