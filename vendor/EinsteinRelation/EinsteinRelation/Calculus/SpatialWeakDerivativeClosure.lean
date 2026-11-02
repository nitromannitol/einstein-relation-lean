import EinsteinRelation.Correctors.WeakPotentialCompletion
import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Calculus.PoincareCauchySupport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Closing spatial weak derivatives in L²

Source: `paper/main.tex:693-698,727-729`. Convergence of both the scalar
potential and its coordinate derivative in L² preserves the genuine
distributional equation. Completeness then supplies scalar potentials
from Cauchy approximations, without imposing a characterization premise.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace EinsteinRelation.Correctors

private theorem continuous_test_pairing {d : ℕ} (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U)] (φ : Vec d → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (fun f : Lp ℝ 2 (volume.restrict U) => ∫ x in U, f x * φ x) := by
  have hm : MemLp φ 2 (volume.restrict U) := hφ.memLp_of_hasCompactSupport hφc
  let p : Lp ℝ 2 (volume.restrict U) := hm.toLp φ
  have hp : p =ᵐ[volume.restrict U] φ := hm.coeFn_toLp
  have heq : (fun f : Lp ℝ 2 (volume.restrict U) => ∫ x in U, f x * φ x) =
      fun f => (innerSL ℝ p) f := by
    funext f
    simp only [innerSL_apply_apply, L2.inner_def, RCLike.inner_apply, conj_trivial]
    exact integral_congr_ae (hp.mono fun x hx => by dsimp only; rw [hx])
  rw [heq]
  exact (innerSL ℝ p).continuous

/-- The graph of each spatial weak coordinate derivative is closed in L². -/
theorem hasWeakPartialDerivative_of_tendsto_L2 {d : ℕ}
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    (i : Fin d) (f g : Lp ℝ 2 (volume.restrict U))
    (fn gn : ℕ → Lp ℝ 2 (volume.restrict U))
    (hf : Tendsto fn atTop (𝓝 f)) (hg : Tendsto gn atTop (𝓝 g))
    (hn : ∀ n, HasWeakPartialDerivative U i (fn n) (gn n)) :
    HasWeakPartialDerivative U i f g := by
  refine ⟨IntegrableOn.locallyIntegrableOn (s := U) ((Lp.memLp f).integrable (by norm_num)),
    IntegrableOn.locallyIntegrableOn (s := U) ((Lp.memLp g).integrable (by norm_num)), ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative i φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  have hl := (continuous_test_pairing U _ hd hdc).tendsto f |>.comp hf
  have hr := ((continuous_test_pairing U φ hφ.1.continuous hφ.2.1).tendsto g |>.comp hg).neg
  apply tendsto_nhds_unique hl
  exact hr.congr (fun n => ((hn n).2.2 φ hφ).symm)

/-- A Poincaré bound for centered differences supplies the Cauchy premise
needed to complete weak potentials. The norm on the finite coordinate
product is used only in this auxiliary convergence criterion. -/
theorem exists_weakPotential_of_poincare_approximation {d : ℕ}
    (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)]
    (f : ℕ → Lp ℝ 2 (volume.restrict U))
    (g : ℕ → Fin d → Lp ℝ 2 (volume.restrict U))
    (G : Fin d → Lp ℝ 2 (volume.restrict U)) (C : ℝ)
    (hg : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (G i)))
    (hbound : ∀ n m, ‖f n - f m‖ ≤ C * ‖g n - g m‖)
    (hweak : ∀ n i, HasWeakPartialDerivative U i (f n) (g n i)) :
    ∃ u : Lp ℝ 2 (volume.restrict U),
      ∀ i, HasWeakPartialDerivative U i u (G i) :=
  exists_weakPotential_of_cauchy_approximation U f g G hg
    (cauchySeq_of_norm_sub_le f g C (tendsto_pi_nhds.mpr hg).cauchySeq hbound) hweak

end EinsteinRelation.Correctors
