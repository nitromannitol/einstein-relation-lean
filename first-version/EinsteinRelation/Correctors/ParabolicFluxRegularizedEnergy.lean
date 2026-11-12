import EinsteinRelation.Correctors.ParabolicFluxEnergyTesting
import EinsteinRelation.Correctors.ParabolicFluxTimePairing
import EinsteinRelation.Correctors.PairedPDERegularizedEnergyLimit

open MeasureTheory Filter Metric
open scoped Topology ENNReal Convolution
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The double-cutoff tests converge in spatial energy, and their temporal
pairings converge to the cutoff derivative term. All approximation
properties are proved from the actual weak solution.
Source: `paper/main.tex:832–840`. -/
theorem parabolicFlux_regularized_energy_limit {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    {J : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hflux : ∀ j, MemLp (fun z => J z j) 2 (volume.restrict (I ×ˢ U)))
    (hweak : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ interior I ×ˢ U →
      (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1,0) +
        dot (J z) (fun j => fderiv ℝ ψ z (0,unitVector j))) = 0)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    (hcut : MemLp (fun z => ζ z * u z) 2 volume ∧
      (∀ j, MemLp (fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0,unitVector j))
        2 volume) ∧
      ∀ᵐ t ∂(volume : Measure ℝ), HasWeakGradient Set.univ
        (fun x => ζ (t,x) * u (t,x))
        (fun x j => ζ (t,x) * G (t,x) j + u (t,x) * fderiv ℝ ζ (t,x) (0,unitVector j)))
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    (heven : ∀ k z, ρ k (-z) = ρ k z)
    {ε : ℕ → ℝ} (hεlim : Tendsto ε atTop (𝓝 0))
    (hρsupp : ∀ k, Function.support (ρ k) ⊆ closedBall 0 (ε k)) :
    let H := fun z j => fderiv ℝ ζ z (0, unitVector j) * (ζ z * u z) +
      ζ z * (ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j))
    Integrable (fun z => dot (J z) (H z))
      (volume.restrict (I ×ˢ U)) ∧
      (∫ z in I ×ˢ U, dot (J z) (H z)) =
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
  have hf : MemLp f 2 volume := hcut.1
  have hF (j : Fin d) : MemLp (F j) 2 volume := hcut.2.1 j
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
    have hder := paired_convolution_spatial_fderiv hf hF hcut.2.2 (hρ k) (hρc k) z j
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
  have hψsm (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ψ k) := hζ.mul (hCc k)
  have hψc (k : ℕ) : HasCompactSupport (ψ k) := hζc.mul_right
  have hψs (k : ℕ) : tsupport (ψ k) ⊆ interior I ×ˢ U :=
    tsupport_mul_subset_left.trans hζsupp
  have hUm : MemLp (fun z => u z * fderiv ℝ ζ z (1, 0)) 2 μ := by
    simpa only [mul_comm] using
      hu.mul' (hζDm (1, 0) |>.mono_measure Measure.restrict_le_self)
  have hT := Entropy.tendsto_integral_mul_of_eLpNorm_two hUm
    (fun k => (hCm k).mono_measure Measure.restrict_le_self)
    (hf.mono_measure Measure.restrict_le_self)
    (paired_tendsto_restrict_L2 (I ×ˢ U) hClim)
  have hTeq (k : ℕ) : (∫ z in I ×ˢ U, u z * fderiv ℝ (ψ k) z (1, 0)) =
      ∫ z in I ×ˢ U, (u z * fderiv ℝ ζ z (1, 0)) * C k z :=
    parabolicFlux_regularized_time_pairing hu hζ hζc hs hf (hρ k) (hρc k) (heven k)
  exact parabolicFlux_test_of_pairing_approximation hu hflux hweak ψ hψsm hψc hψs hH hHx (hT.congr fun k => (hTeq k).symm)

/-- Testing the actual weak equation by the square of a compact cutoff
and the solution gives the local energy identity. No smoothness or temporal
derivative of the solution, nor an energy identity, is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicFlux_cutoff_energy_identity {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    {J : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hflux : ∀ j, MemLp (fun z => J z j) 2 (volume.restrict (I ×ˢ U)))
    (hweak : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ interior I ×ˢ U →
      (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1,0) +
        dot (J z) (fun j => fderiv ℝ ψ z (0,unitVector j))) = 0)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    (hcut : MemLp (fun z => ζ z * u z) 2 volume ∧
      (∀ j, MemLp (fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0,unitVector j))
        2 volume) ∧
      ∀ᵐ t ∂(volume : Measure ℝ), HasWeakGradient Set.univ
        (fun x => ζ (t,x) * u (t,x))
        (fun x j => ζ (t,x) * G (t,x) j + u (t,x) * fderiv ℝ ζ (t,x) (0,unitVector j))) :
    Integrable (fun z => dot (J z)
      (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j)))
      (volume.restrict (I ×ˢ U)) ∧
      (∫ z in I ×ˢ U, dot (J z)
        (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j))) =
        ∫ z in I ×ˢ U, (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := one_div_pos.mpr (by positivity)
  let b (k : ℕ) : ContDiffBump (0 : ℝ × Vec d) :=
    ⟨ε k / 2, ε k, half_pos (hε k), half_lt_self (hε k)⟩
  let ρ := fun k => (b k).normed volume
  have hρsupp (k : ℕ) : Function.support (ρ k) ⊆ closedBall 0 (ε k) := by
    rw [← show tsupport (ρ k) = closedBall 0 (ε k) from (b k).tsupport_normed_eq]
    exact subset_tsupport _
  have hr := parabolicFlux_regularized_energy_limit hu hflux hweak hζ hζc hζsupp hcut
    (fun k => (b k).contDiff_normed) (fun k => (b k).hasCompactSupport_normed)
    (fun k => (b k).nonneg_normed) (fun k => (b k).integral_normed)
    (fun k => (b k).normed_neg)
    (show Tendsto ε atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat) hρsupp
  have hH (z : ℝ × Vec d) : (fun j => fderiv ℝ ζ z (0, unitVector j) * (ζ z * u z) +
      ζ z * (ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j))) =
      fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j) := by
    funext j
    ring
  have hE : (fun z => (u z * fderiv ℝ ζ z (1, 0)) * (ζ z * u z)) =
      fun z => (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0) := by
    funext z
    ring
  simpa only [hH, hE] using hr


end EinsteinRelation.Correctors
