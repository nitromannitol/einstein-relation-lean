import EinsteinRelation.Correctors.PairedPDEEnergyTesting

/-! # Closing weak flux equations by energy approximation

Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof.
The flux is independent of the spatial gradient, so the result also applies
to sums of forward and backward solutions.
-/
open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Closing the weak equation needs only a scalar limit for the temporal
pairing, together with strong L² convergence of the spatial test gradients.
No temporal derivative of the solution is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicFlux_test_of_pairing_approximation {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {F : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hflux : ∀ j, MemLp (fun z => F z j) 2 (volume.restrict (I ×ˢ U)))
    (hweak : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ interior I ×ˢ U →
      (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1,0) +
        dot (F z) (fun j => fderiv ℝ ψ z (0,unitVector j))) = 0)
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
    Integrable (fun z => dot (F z) (H z))
      (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, dot (F z) (H z)) = E := by
  let μ := volume.restrict (I ×ˢ U)
  have hDm (k : ℕ) (v : ℝ × Vec d) :
      MemLp (fun z => fderiv ℝ (ψ k) z v) 2 μ := by
    have hc : Continuous (fun z => fderiv ℝ (ψ k) z v) :=
      ((contDiff_infty_iff_fderiv.mp (hψ k)).2.clm_apply contDiff_const).continuous
    exact (hc.memLp_of_hasCompactSupport ((hψc k).fderiv_apply ℝ v)).mono_measure
      Measure.restrict_le_self
  have hpair (j : Fin d) := Entropy.tendsto_integral_mul_of_eLpNorm_two (hflux j)
    (fun k => hDm k (0, unitVector j)) (hH j) (hHx j)
  have hsum := tendsto_finset_sum Finset.univ fun j _ => hpair j
  have hi : Integrable (fun z => dot (F z) (H z)) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hflux j).integrable_mul (hH j)
  have hid (k : ℕ) :
      (∑ j : Fin d, ∫ z, (F z) j *
        fderiv ℝ (ψ k) z (0, unitVector j) ∂μ) =
      ∫ z, u z * fderiv ℝ (ψ k) z (1, 0) ∂μ := by
    have hiX : Integrable (fun z => ∑ j : Fin d, (F z) j *
        fderiv ℝ (ψ k) z (0, unitVector j)) μ :=
      integrable_finset_sum Finset.univ fun j _ => (hflux j).integrable_mul (hDm k _)
    have hiT : Integrable (fun z => u z * fderiv ℝ (ψ k) z (1, 0)) μ :=
      hu.integrable_mul (hDm k _)
    have heq := hweak (ψ k) (hψ k) (hψc k) (hψsupp k)
    change (∫ z, -(u z) * fderiv ℝ (ψ k) z (1, 0) +
      ∑ j : Fin d, (F z) j *
        fderiv ℝ (ψ k) z (0, unitVector j) ∂μ) = 0 at heq
    simp_rw [neg_mul] at heq
    have hiNeg : Integrable (fun z => -(u z * fderiv ℝ (ψ k) z (1, 0))) μ := hiT.neg
    rw [integral_add hiNeg hiX] at heq
    simp only [integral_neg] at heq
    rw [← integral_finset_sum Finset.univ (fun j _ =>
      show Integrable (fun z => (F z) j *
        fderiv ℝ (ψ k) z (0, unitVector j)) μ from
        (hflux j).integrable_mul (hDm k _))]
    linarith only [heq]
  have hE := tendsto_nhds_unique (hsum.congr hid) hT
  refine ⟨hi, ?_⟩
  change (∫ z, ∑ j : Fin d, (F z) j * H z j ∂μ) = E
  rw [integral_finset_sum Finset.univ (fun j _ =>
    show Integrable (fun z => (F z) j * H z j) μ from
      (hflux j).integrable_mul (hH j))]
  exact hE

end EinsteinRelation.Correctors
