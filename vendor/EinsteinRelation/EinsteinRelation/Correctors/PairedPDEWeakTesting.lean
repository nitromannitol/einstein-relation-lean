import EinsteinRelation.Correctors.PairedPDETesting
import EinsteinRelation.Entropy.DivergenceSecondAssertion

/-! # Closing the weak parabolic test space

Source: `paper/main.tex:822–830`. The distributional equation extends to
limits of admissible smooth tests whenever their temporal and spatial
derivatives converge in L². Only derivative convergence is needed; every
pairing is integrable before taking the limit.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- The weak equation is closed under L² convergence of test derivatives.
This applies to energy-class solutions without a smoothness assumption on
those solutions. Source: `paper/main.tex:822–830`. -/
theorem parabolicSolution_test_of_L2_approximation {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    (ψ : ℕ → ℝ × Vec d → ℝ)
    (hψ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k))
    (hψc : ∀ k, HasCompactSupport (ψ k))
    (hψsupp : ∀ k, tsupport (ψ k) ⊆ interior I ×ˢ U)
    {D : ℝ × Vec d → ℝ} {H : ℝ × Vec d → Vec d}
    (hD : MemLp D 2 (volume.restrict (I ×ˢ U)))
    (hH : ∀ j, MemLp (fun z => H z j) 2 (volume.restrict (I ×ˢ U)))
    (hDt : Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (ψ k) z (1, 0) - D z) 2
        (volume.restrict (I ×ˢ U))) atTop (𝓝 0))
    (hHx : ∀ j, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (ψ k) z (0, unitVector j) - H z j) 2
        (volume.restrict (I ×ˢ U))) atTop (𝓝 0)) :
    Integrable (fun z => -(u z) * D z + dot ((A z.2).mulVec (G z)) (H z))
      (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, -(u z) * D z + dot ((A z.2).mulVec (G z)) (H z)) = 0 := by
  let μ := volume.restrict (I ×ˢ U)
  have hDm (k : ℕ) (v : ℝ × Vec d) :
      MemLp (fun z => fderiv ℝ (ψ k) z v) 2 μ := by
    have hc : Continuous (fun z => fderiv ℝ (ψ k) z v) :=
      ((contDiff_infty_iff_fderiv.mp (hψ k)).2.clm_apply contDiff_const).continuous
    exact (hc.memLp_of_hasCompactSupport ((hψc k).fderiv_apply ℝ v)).mono_measure
      Measure.restrict_le_self
  have hflux (j : Fin d) := parabolicSolution_flux_coordinate_memLp hK A hsol j
  have ht := Entropy.tendsto_integral_mul_of_eLpNorm_two hsol.1.neg
    (fun k => hDm k (1, 0)) hD hDt
  have hx (j : Fin d) := Entropy.tendsto_integral_mul_of_eLpNorm_two (hflux j)
    (fun k => hDm k (0, unitVector j)) (hH j) (hHx j)
  have hlim := ht.add (tendsto_finset_sum Finset.univ fun j _ => hx j)
  have hiT : Integrable (fun z => -(u z) * D z) μ := hsol.1.neg.integrable_mul hD
  have hiX : Integrable (fun z => ∑ j : Fin d,
      ((A z.2).mulVec (G z)) j * H z j) μ :=
    integrable_finset_sum Finset.univ fun j _ => (hflux j).integrable_mul (hH j)
  have hsum (k : ℕ) :
      (∫ z, ∑ j : Fin d, ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j) ∂μ) =
      ∑ j : Fin d, ∫ z, ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j) ∂μ :=
    integral_finset_sum Finset.univ (fun j _ =>
      show Integrable (fun z => ((A z.2).mulVec (G z)) j *
        fderiv ℝ (ψ k) z (0, unitVector j)) μ from
        (hflux j).integrable_mul (hDm k (0, unitVector j)))
  have hzero (k : ℕ) :
      (∫ z, -(u z) * fderiv ℝ (ψ k) z (1, 0) ∂μ) +
        ∑ j : Fin d, ∫ z, ((A z.2).mulVec (G z)) j *
          fderiv ℝ (ψ k) z (0, unitVector j) ∂μ = 0 := by
    rw [← hsum k, ← integral_add
      (show Integrable (fun z => -(u z) * fderiv ℝ (ψ k) z (1, 0)) μ from
        hsol.1.neg.integrable_mul (hDm k (1, 0)))
      (integrable_finset_sum Finset.univ fun j _ =>
        show Integrable (fun z => ((A z.2).mulVec (G z)) j *
          fderiv ℝ (ψ k) z (0, unitVector j)) μ from
          (hflux j).integrable_mul (hDm k (0, unitVector j)))]
    exact hsol.2.2.2.2 (ψ k) (hψ k) (hψc k) (hψsupp k)
  simp only [Pi.neg_apply] at hlim
  have hlim0 := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr (fun k => (hzero k).symm)
  have hid := tendsto_nhds_unique hlim hlim0
  refine ⟨hiT.add hiX, ?_⟩
  change (∫ z, -(u z) * D z + ∑ j : Fin d,
    ((A z.2).mulVec (G z)) j * H z j ∂μ) = 0
  rw [integral_add hiT hiX, integral_finset_sum Finset.univ
    (fun j _ => show Integrable (fun z => ((A z.2).mulVec (G z)) j * H z j) μ from
      (hflux j).integrable_mul (hH j))]
  exact hid

end EinsteinRelation.Correctors
