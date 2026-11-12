import EinsteinRelation.Correctors.PairedPDEWeakTesting

/-! # Energy-test limits without a strong time derivative

Source: `paper/main.tex:832–840`. For a solution-dependent energy test,
its temporal derivative need not converge in L². The weak equation can
instead be closed using convergence of its temporal pairing. Constructing
the regularized tests and establishing that pairing limit remain separate.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Closing the weak equation needs only a scalar limit for the temporal
pairing, together with strong L² convergence of the spatial test gradients.
No temporal derivative of the solution is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_flux_test_of_pairing_approximation {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    (ψ : ℕ → ℝ × Vec d → ℝ)
    (hψ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k))
    (hψc : ∀ k, HasCompactSupport (ψ k))
    (hψsupp : ∀ k, tsupport (ψ k) ⊆ interior I ×ˢ U)
    {H : ℝ × Vec d → Vec d} {E : ℝ}
    (hH : ∀ j, MemLp (fun z => H z j) 2 (volume.restrict (I ×ˢ U)))
    (hHx : ∀ j, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (ψ k) z (0, unitVector j) - H z j) 2
        (volume.restrict (I ×ˢ U))) atTop (𝓝 0))
    (hT : Tendsto (fun k => ∫ z in I ×ˢ U,
      u z * fderiv ℝ (ψ k) z (1, 0)) atTop (𝓝 E)) :
    Integrable (fun z => dot ((A z.2).mulVec (G z)) (H z))
      (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, dot ((A z.2).mulVec (G z)) (H z)) = E := by
  let μ := volume.restrict (I ×ˢ U)
  have hDm (k : ℕ) (v : ℝ × Vec d) :
      MemLp (fun z => fderiv ℝ (ψ k) z v) 2 μ := by
    have hc : Continuous (fun z => fderiv ℝ (ψ k) z v) :=
      ((contDiff_infty_iff_fderiv.mp (hψ k)).2.clm_apply contDiff_const).continuous
    exact (hc.memLp_of_hasCompactSupport ((hψc k).fderiv_apply ℝ v)).mono_measure
      Measure.restrict_le_self
  have hflux (j : Fin d) := parabolicSolution_flux_coordinate_memLp hK A hsol j
  have hpair (j : Fin d) := Entropy.tendsto_integral_mul_of_eLpNorm_two (hflux j)
    (fun k => hDm k (0, unitVector j)) (hH j) (hHx j)
  have hsum := tendsto_finset_sum Finset.univ fun j _ => hpair j
  have hi : Integrable (fun z => dot ((A z.2).mulVec (G z)) (H z)) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hflux j).integrable_mul (hH j)
  have hid (k : ℕ) :
      (∑ j : Fin d, ∫ z, ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j) ∂μ) =
      ∫ z, u z * fderiv ℝ (ψ k) z (1, 0) ∂μ := by
    have hiX : Integrable (fun z => ∑ j : Fin d, ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j)) μ :=
      integrable_finset_sum Finset.univ fun j _ => (hflux j).integrable_mul (hDm k _)
    have hiT : Integrable (fun z => u z * fderiv ℝ (ψ k) z (1, 0)) μ :=
      hsol.1.integrable_mul (hDm k _)
    have heq := hsol.2.2.2.2 (ψ k) (hψ k) (hψc k) (hψsupp k)
    change (∫ z, -(u z) * fderiv ℝ (ψ k) z (1, 0) +
      ∑ j : Fin d, ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j) ∂μ) = 0 at heq
    simp_rw [neg_mul] at heq
    have hiNeg : Integrable (fun z => -(u z * fderiv ℝ (ψ k) z (1, 0))) μ := hiT.neg
    rw [integral_add hiNeg hiX] at heq
    simp only [integral_neg] at heq
    rw [← integral_finset_sum Finset.univ (fun j _ =>
      show Integrable (fun z => ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j)) μ from
        (hflux j).integrable_mul (hDm k _))]
    linarith only [heq]
  have hE := tendsto_nhds_unique (hsum.congr hid) hT
  refine ⟨hi, ?_⟩
  change (∫ z, ∑ j : Fin d, ((A z.2).mulVec (G z)) j * H z j ∂μ) = E
  rw [integral_finset_sum Finset.univ (fun j _ =>
    show Integrable (fun z => ((A z.2).mulVec (G z)) j * H z j) μ from
      (hflux j).integrable_mul (hH j))]
  exact hE

end EinsteinRelation.Correctors
