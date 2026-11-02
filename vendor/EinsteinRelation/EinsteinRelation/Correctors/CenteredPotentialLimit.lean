import EinsteinRelation.Calculus.SpatialWeakDerivativeClosure
import EinsteinRelation.Calculus.WeakGradientSubtraction
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Correctors.CenteredL2Poincare
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Correctors.HarmonicRepresentativeNormalization

/-!
# Completing centered scalar spatial potentials

Source: `paper/main.tex:693-698,727-729`. Centering removes the constants,
Poincaré makes the scalar approximations Cauchy, and the closed spatial
weak derivative graph identifies the limit gradient.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- A convergent sequence of actual Sobolev gradients has an actual scalar
potential; the explicit GT Poincaré proposition is the only source input. -/
theorem exists_weakPotential_of_spatial_gradient_approximation
    (hP : BallPoincareEstimate) {d : ℕ} (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R)
    (u : ℕ → Vec d → ℝ) (g : ℕ → Vec d → EuclideanSpace ℝ (Fin d))
    (G : Vec d → EuclideanSpace ℝ (Fin d))
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict (ball 0 R)))
    (hg : ∀ n, MemLp (g n) 2 (volume.restrict (ball 0 R)))
    (hG : MemLp G 2 (volume.restrict (ball 0 R)))
    (hweak : ∀ n, HasWeakGradient (ball 0 R) (u n) (fun x => (g n x).ofLp))
    (hlim : Tendsto (fun n => ∫ x in ball 0 R, ‖g n x - G x‖ ^ 2) atTop (𝓝 0)) :
    ∃ v : Vec d → ℝ, MemLp v 2 (volume.restrict (ball 0 R)) ∧
      HasWeakGradient (ball 0 R) v (fun x => (G x).ofLp) := by
  let U := ball (0 : Vec d) R
  let μ := volume.restrict U
  have hfin : volume U ≠ ⊤ := (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfin
  let uc := fun n x => u n x - ⨍ y, u n y ∂μ
  have huc (n : ℕ) : MemLp (uc n) 2 μ := (hu n).sub (memLp_const _)
  let f := fun n => (huc n).toLp (uc n)
  let gn := fun n => (hg n).toLp (g n)
  let GG := hG.toLp G
  have hraw (n : ℕ) : MemLp (fun x => (g n x).ofLp) 2 μ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.comp_memLp' (hg n)
  have hcw (n : ℕ) : HasWeakGradient U (uc n) (fun x => (g n x).ofLp) := by
    have hz : WeakSolution U (fun _ => 0) (u n) (fun x => (g n x).ofLp) :=
      ⟨hu n, hraw n, hweak n, by simpa using hasWeakDivergence_zero U⟩
    exact (weakSolution_sub_const hz (⨍ y, u n y ∂μ)).2.2.1
  have hw (n : ℕ) : HasWeakGradient U (f n) (fun x => (gn n x).ofLp) := by
    intro i
    exact (hcw n i).congr_ae (huc n).coeFn_toLp.symm
      ((hg n).coeFn_toLp.symm.mono fun x hx => congrArg (fun z => z.ofLp i) hx)
  have hmean (n : ℕ) : (∫ x, f n x ∂μ) = 0 := by
    rw [integral_congr_ae (huc n).coeFn_toLp]
    exact integral_sub_average μ (u n)
  have hgnraw (n : ℕ) : MemLp (fun x => (gn n x).ofLp) 2 μ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.comp_memLp (gn n)
  obtain ⟨C, _, hC⟩ := centered_L2_poincare hP d hd
  have hb (n m : ℕ) : ‖f n - f m‖ ≤ C * R * ‖gn n - gn m‖ := by
    have hs := hasWeakGradient_sub_of_memLp U (f n) (f m)
      (fun x => (gn n x).ofLp) (fun x => (gn m x).ofLp)
      (Lp.memLp _) (Lp.memLp _) (hgnraw n) (hgnraw m) (hw n) (hw m)
    have hsw : HasWeakGradient U (f n - f m : Lp ℝ 2 μ) (fun x => ((gn n - gn m) x).ofLp) := by
      intro i
      exact (hs i).congr_ae (Lp.coeFn_sub (f n) (f m)).symm
        ((Lp.coeFn_sub (gn n) (gn m)).symm.mono fun x hx =>
          congrArg (fun z => z.ofLp i) hx)
    apply hC 0 R hR (f n - f m) (gn n - gn m) hsw
    rw [average_eq, integral_congr_ae (Lp.coeFn_sub (f n) (f m))]
    simp only [Pi.sub_apply]
    rw [integral_sub ((Lp.memLp (f n)).integrable (by norm_num))
        ((Lp.memLp (f m)).integrable (by norm_num)), hmean, hmean, sub_self, smul_zero]
  have ht : Tendsto gn atTop (𝓝 GG) :=
    tendsto_toLp_of_integral_sq_norm_sub_tendsto_zero μ g G hg hG hlim
  have hcf : CauchySeq f := cauchySeq_of_norm_sub_le f gn (C * R) ht.cauchySeq hb
  let proj := fun i : Fin d => (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ
  obtain ⟨v, hv⟩ := exists_weakPotential_of_cauchy_approximation U f
    (fun n i => proj i (gn n)) (fun i => proj i GG)
    (fun i => (proj i).continuous.tendsto GG |>.comp ht) hcf (fun n i => by
      exact (hw n i).congr_ae (Filter.EventuallyEq.rfl)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL (gn n)).symm)
  refine ⟨v, Lp.memLp v, fun i => ?_⟩
  exact (hv i).congr_ae Filter.EventuallyEq.rfl
    (((EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL GG).trans
      (hG.coeFn_toLp.mono fun x hx => congrArg (fun z => z.ofLp i) hx))

end EinsteinRelation.Correctors
