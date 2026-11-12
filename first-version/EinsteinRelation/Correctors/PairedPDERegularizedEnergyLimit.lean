import EinsteinRelation.Correctors.PairedPDERegularizationLimits
import EinsteinRelation.Correctors.ParabolicCutoffGlobalWeakGradient
import EinsteinRelation.Correctors.PairedPDERegularizedTimePairing
import EinsteinRelation.Correctors.PairedPDEEnergyTesting

/-! # Passing the actual regularized energy tests to the limit

Source: `paper/main.tex:832–840`. Spatial convolution approximates the
actual product-rule gradient in L². The even-kernel temporal cancellation
then closes the weak equation without a strong time derivative.
-/

open MeasureTheory Filter Metric
open scoped Topology ENNReal Convolution

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The double-cutoff tests converge in spatial energy, and their temporal
pairings converge to the cutoff derivative term. All approximation
properties are proved from the actual weak solution.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_regularized_energy_limit {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    (heven : ∀ k z, ρ k (-z) = ρ k z)
    {ε : ℕ → ℝ} (hεlim : Tendsto ε atTop (𝓝 0))
    (hρsupp : ∀ k, Function.support (ρ k) ⊆ closedBall 0 (ε k)) :
    let H := fun z j => fderiv ℝ ζ z (0, unitVector j) * (ζ z * u z) +
      ζ z * (ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j))
    Integrable (fun z => dot ((A z.2).mulVec (G z)) (H z))
      (volume.restrict (I ×ˢ U)) ∧
      (∫ z in I ×ˢ U, dot ((A z.2).mulVec (G z)) (H z)) =
        ∫ z in I ×ˢ U, (u z * fderiv ℝ ζ z (1, 0)) * (ζ z * u z) := by
  dsimp only
  let μ := volume.restrict (I ×ˢ U)
  let f := fun z => ζ z * u z
  let F := fun j z => ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)
  let C := fun k z => ∫ w : ℝ × Vec d, f w * ρ k (z - w)
  let D := fun k j z => ∫ w : ℝ × Vec d, F j w * ρ k (z - w)
  let ψ := fun k z => ζ z * C k z
  have hs : tsupport ζ ⊆ I ×ˢ U :=
    hζsupp.trans (Set.prod_mono interior_subset Set.Subset.rfl)
  have hf : MemLp f 2 volume :=
    parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol hζ.continuous hζc hs
  have hF (j : Fin d) : MemLp (F j) 2 volume :=
    parabolicSolution_cutoff_gradient_memLp_global hI hU hsol hζ hζc hs j
  have hCc (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (C k) :=
    (hρc k).contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      (hf.locallyIntegrable (by norm_num)) (hρ k)
  have hCcompact (k : ℕ) : HasCompactSupport (C k) :=
    hζc.mul_right.convolution (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (hρc k)
  have hCm (k : ℕ) : MemLp (C k) 2 volume :=
    (hCc k).continuous.memLp_of_hasCompactSupport (hCcompact k)
  have hClim : Tendsto (fun k => eLpNorm (fun z => C k z - f z) 2 volume)
      atTop (𝓝 0) :=
    paired_tendsto_regularization_L2 hf (fun k => (hρ k).continuous)
      hρc hρ0 hρ1 hεlim hρsupp
  have hDc (k : ℕ) (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (D k j) :=
    (hρc k).contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      ((hF j).locallyIntegrable (by norm_num)) (hρ k)
  have hDcompact (k : ℕ) (j : Fin d) : HasCompactSupport (D k j) :=
    (hζc.mul_right.add ((hζc.fderiv_apply ℝ (0, unitVector j)).mul_left)).convolution
      (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (hρc k)
  have hDm (k : ℕ) (j : Fin d) : MemLp (D k j) 2 volume :=
    (hDc k j).continuous.memLp_of_hasCompactSupport (hDcompact k j)
  have hDlim (j : Fin d) : Tendsto (fun k => eLpNorm
      (fun z => D k j z - F j z) 2 volume) atTop (𝓝 0) :=
    paired_tendsto_regularization_L2 (hF j) (fun k => (hρ k).continuous)
      hρc hρ0 hρ1 hεlim hρsupp
  have hζm : MemLp ζ ∞ volume := hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  have hζDm (v : ℝ × Vec d) : MemLp (fun z => fderiv ℝ ζ z v) ∞ volume :=
    ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
      |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ v) _
  have hgrad (k : ℕ) (z : ℝ × Vec d) (j : Fin d) :
      fderiv ℝ (ψ k) z (0, unitVector j) =
        fderiv ℝ ζ z (0, unitVector j) * C k z + ζ z * D k j z := by
    change fderiv ℝ (fun y => ζ y * C k y) z _ = _
    rw [fderiv_fun_mul (hζ.differentiable (by norm_cast) z)
      ((hCc k).differentiable (by norm_cast) z)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hder := parabolicSolution_cutoff_convolution_spatial_fderiv
      hI hU hsol hζ hζc hs (hρ k) (hρc k) z j
    change fderiv ℝ (C k) z (0, unitVector j) = D k j z at hder
    rw [hder]
    ring
  have hHx (j : Fin d) : Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (ψ k) z (0, unitVector j) -
        (fderiv ℝ ζ z (0, unitVector j) * f z + ζ z * F j z)) 2 μ)
      atTop (𝓝 0) := by
    simp_rw [hgrad]
    exact paired_tendsto_restrict_L2 _ (paired_tendsto_add_L2
      (hf.mul' (hζDm _)) ((hF j).mul' hζm)
      (fun k => (hCm k).mul' (hζDm _)) (fun k => (hDm k j).mul' hζm)
      (paired_tendsto_fixed_multiplier_L2 hf hCm (hζDm _) hClim)
      (paired_tendsto_fixed_multiplier_L2 (hF j) (fun k => hDm k j) hζm (hDlim j)))
  have hH (j : Fin d) : MemLp
      (fun z => fderiv ℝ ζ z (0, unitVector j) * f z + ζ z * F j z) 2 μ :=
    ((hf.mul' (hζDm _)).add ((hF j).mul' hζm)).mono_measure Measure.restrict_le_self
  have hψdata (k : ℕ) := parabolicSolution_regularized_cutoff_test hK
    hI hU.measurableSet hsol hζ hζc hζsupp (hρ k) (hρc k)
  have hUm : MemLp (fun z => u z * fderiv ℝ ζ z (1, 0)) 2 μ := by
    simpa only [mul_comm] using
      hsol.1.mul' (hζDm (1, 0) |>.mono_measure Measure.restrict_le_self)
  have hT := Entropy.tendsto_integral_mul_of_eLpNorm_two hUm
    (fun k => (hCm k).mono_measure Measure.restrict_le_self)
    (hf.mono_measure Measure.restrict_le_self)
    (paired_tendsto_restrict_L2 (I ×ˢ U) hClim)
  have hTeq (k : ℕ) : (∫ z in I ×ˢ U, u z * fderiv ℝ (ψ k) z (1, 0)) =
      ∫ z in I ×ˢ U, (u z * fderiv ℝ ζ z (1, 0)) * C k z :=
    parabolicSolution_regularized_time_pairing hI hU.measurableSet hsol
      hζ hζc hs (hρ k) (hρc k) (heven k)
  exact parabolicSolution_flux_test_of_pairing_approximation hK A hsol ψ
    (fun k => (hψdata k).1) (fun k => (hψdata k).2.1)
    (fun k => (hψdata k).2.2.1) hH hHx (hT.congr fun k => (hTeq k).symm)

end EinsteinRelation.Correctors
