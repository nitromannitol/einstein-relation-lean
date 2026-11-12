import EinsteinRelation.Correctors.PairedPDEApproximationLimits
import EinsteinRelation.Correctors.PairedPDELinearConvergence

/-! # Spatial limits for the actual double-cutoff tests

Source: `paper/main.tex:832–840`. The outer cutoff converts the actual
regularizations into admissible energy tests, and bounded multiplication
preserves their spatial derivative limits.
-/

open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The gradients of the actual double-cutoff tests converge strongly to
the energy-test gradient. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_double_cutoff_gradient_limit {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 (ε k)) (j : Fin d) :
    MemLp (fun z => ζ z ^ 2 * G z j +
      2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j))
        2 (volume.restrict (I ×ˢ U)) ∧
    Tendsto (fun k => eLpNorm (fun z : ℝ × Vec d =>
      fderiv ℝ (fun y : ℝ × Vec d => ζ y *
        ∫ w : ℝ × Vec d, ζ w * u w * ρ k (y - w)) z (0, unitVector j) -
      (ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j)))
        2 (volume.restrict (I ×ˢ U))) atTop (𝓝 0) := by
  let f := fun z => ζ z * u z
  let H := fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)
  let Dζ := fun z => fderiv ℝ ζ z (0, unitVector j)
  let C := fun k (z : ℝ × Vec d) => ∫ w : ℝ × Vec d, f w * ρ k (z - w)
  let DC := fun k (z : ℝ × Vec d) => fderiv ℝ (C k) z (0, unitVector j)
  have hf := parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol
    hζ.continuous hζc hζsupp
  have hH := parabolicSolution_cutoff_gradient_memLp_global hI hU hsol hζ hζc hζsupp j
  have hCsm (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (C k) ∧ HasCompactSupport (C k) := by
    obtain ⟨hc, hcc, _⟩ := paired_convolution_test_admissible hf hζc.mul_right
      (hρ k) (hρc k) (Set.subset_univ _)
    exact ⟨hc, hcc⟩
  have hC (k : ℕ) : MemLp (C k) 2 volume :=
    (hCsm k).1.continuous.memLp_of_hasCompactSupport (hCsm k).2
  have hDC (k : ℕ) : MemLp (DC k) 2 volume :=
    ((contDiff_infty_iff_fderiv.mp (hCsm k).1).2.clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport ((hCsm k).2.fderiv_apply ℝ (0, unitVector j))
  have hζm : MemLp ζ ∞ volume := hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  have hDζm : MemLp Dζ ∞ volume :=
    ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
      |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (0, unitVector j)) _
  have hClim := parabolicSolution_cutoff_regularization_limit hI hU hsol hζ hζc hζsupp
    hρ hρc hρ0 hρ1 hε hsupp
  have hDClim := parabolicSolution_cutoff_gradient_regularization_limit hI hU hsol hζ
    hζc hζsupp hρ hρc hρ0 hρ1 hε hsupp j
  have ha := paired_tendsto_fixed_mul_L2 hf hC hDζm hClim
  have hb := paired_tendsto_fixed_mul_L2 hH hDC hζm hDClim
  have hsum := paired_tendsto_add_L2 (hf.mul' hDζm) (hH.mul' hζm)
    (fun k => (hC k).mul' hDζm) (fun k => (hDC k).mul' hζm) ha hb
  have hmem : MemLp (fun z => ζ z ^ 2 * G z j +
      2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j)) 2 volume := by
    have hh : MemLp (fun z => Dζ z * f z + ζ z * H z) 2 volume :=
      (hf.mul' hDζm).add (hH.mul' hζm)
    convert hh using 1
    funext z
    dsimp only [f, H, Dζ]
    ring
  refine ⟨hmem.mono_measure Measure.restrict_le_self, ?_⟩
  apply paired_tendsto_eLpNorm_of_measure_le Measure.restrict_le_self
  convert hsum using 1
  funext k
  congr 1
  funext z
  rw [fderiv_fun_mul (hζ.differentiable (by norm_cast) z)
    ((hCsm k).1.differentiable (by norm_cast) z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  dsimp only [f, H, Dζ, DC]
  ring

end EinsteinRelation.Correctors
