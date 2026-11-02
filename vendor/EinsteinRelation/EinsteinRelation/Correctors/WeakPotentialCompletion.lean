import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Function.L2Space

/-! # Completing local weak potentials in spatial L²

Source: `paper/main.tex:693–698,727–729`.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- Complete the scalar potentials when their weak gradients converge and
Poincaré controls their differences; source `paper/main.tex:693-698,727-729`.
The target gradient is coordinate-valued, with all coordinates in spatial L².
No existence, uniqueness or identification is assumed in the conclusion. -/
theorem exists_weakPotential_of_cauchy_approximation {d : ℕ}
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    (f : ℕ → Lp ℝ 2 (volume.restrict U))
    (g : ℕ → Fin d → Lp ℝ 2 (volume.restrict U))
    (G : Fin d → Lp ℝ 2 (volume.restrict U))
    (hg : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (G i)))
    (hf : CauchySeq f)
    (hweak : ∀ n i, HasWeakPartialDerivative U i (f n) (g n i)) :
    ∃ u : Lp ℝ 2 (volume.restrict U),
      ∀ i, HasWeakPartialDerivative U i u (G i) := by
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hf
  have hu_mem : MemLp u 2 (volume.restrict U) := Lp.memLp u
  refine ⟨u, fun i => ?_⟩
  have hloc_u : LocallyIntegrableOn u U volume :=
    IntegrableOn.locallyIntegrableOn (s := U) ((Lp.memLp u).integrable (by norm_num))
  have hloc_Gi : LocallyIntegrableOn (G i) U volume :=
    IntegrableOn.locallyIntegrableOn (s := U) ((Lp.memLp (G i)).integrable (by norm_num))
  refine ⟨hloc_u, hloc_Gi, ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative i φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  have h_cont_l : Continuous (fun (f' : Lp ℝ 2 (volume.restrict U)) =>
      ∫ x in U, f' x * coordinateDerivative i φ x) := by
    have hm : MemLp (coordinateDerivative i φ) 2 (volume.restrict U) :=
      hd.memLp_of_hasCompactSupport hdc
    let p : Lp ℝ 2 (volume.restrict U) := hm.toLp (coordinateDerivative i φ)
    have hp : p =ᵐ[volume.restrict U] coordinateDerivative i φ := hm.coeFn_toLp
    have heq : (fun (f' : Lp ℝ 2 (volume.restrict U)) =>
        ∫ x in U, f' x * coordinateDerivative i φ x) =
        fun f' => (innerSL ℝ p) f' := by
      funext f'
      simp only [innerSL_apply_apply, L2.inner_def, RCLike.inner_apply, conj_trivial]
      exact integral_congr_ae (hp.mono fun x hx => by dsimp only; rw [hx])
    rw [heq]
    exact (innerSL ℝ p).continuous
  have h_cont_r : Continuous (fun (f' : Lp ℝ 2 (volume.restrict U)) =>
      ∫ x in U, f' x * φ x) := by
    have hm : MemLp φ 2 (volume.restrict U) :=
      hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
    let p : Lp ℝ 2 (volume.restrict U) := hm.toLp φ
    have hp : p =ᵐ[volume.restrict U] φ := hm.coeFn_toLp
    have heq : (fun (f' : Lp ℝ 2 (volume.restrict U)) =>
        ∫ x in U, f' x * φ x) =
        fun f' => (innerSL ℝ p) f' := by
      funext f'
      simp only [innerSL_apply_apply, L2.inner_def, RCLike.inner_apply, conj_trivial]
      exact integral_congr_ae (hp.mono fun x hx => by dsimp only; rw [hx])
    rw [heq]
    exact (innerSL ℝ p).continuous
  have hl := (h_cont_l.tendsto u).comp hu
  have hr := ((h_cont_r.tendsto (G i)).comp (hg i)).neg
  apply tendsto_nhds_unique hl
  exact hr.congr (fun n => ((hweak n i).2.2 φ hφ).symm)

end EinsteinRelation.Correctors
