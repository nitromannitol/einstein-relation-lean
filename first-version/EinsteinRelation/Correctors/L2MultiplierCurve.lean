import EinsteinRelation.Correctors.L2DominatedLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory
open Set
open Filter
open scoped Topology
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Bounded differentiable scalar multipliers give the actual strong L²
curve and its derivative. Source: `paper/main.tex:798–806`; temporal smoothing. -/
theorem exists_differentiable_L2_multiplier_curve {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : Ω → ℝ} (hf : MemLp f 2 μ)
    (m m' : ℝ → Ω → ℝ)
    (hm : ∀ t, AEStronglyMeasurable (m t) μ)
    (hm' : ∀ t, AEStronglyMeasurable (m' t) μ)
    (hd : ∀ t ω, HasDerivAt (fun s => m s ω) (m' t ω) t)
    {C D : ℝ} (_hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t ω, |m t ω| ≤ C) (hb' : ∀ t ω, |m' t ω| ≤ D) :
    ∃ F F' : ℝ → Lp ℝ 2 μ,
      (∀ t, (F t : Ω → ℝ) =ᵐ[μ] fun ω => m t ω * f ω) ∧
      (∀ t, (F' t : Ω → ℝ) =ᵐ[μ] fun ω => m' t ω * f ω) ∧
      ∀ t, HasDerivAt F (F' t) t := by
  let q (r : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ := fun ω => r t ω * f ω
  have hmf t : MemLp (q m t) 2 μ := hf.of_le_mul ((hm t).mul hf.1)
    (Filter.Eventually.of_forall fun ω => by
      simpa only [q,norm_mul,Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hb t ω) (abs_nonneg (f ω)))
  have hmf' t : MemLp (q m' t) 2 μ := hf.of_le_mul ((hm' t).mul hf.1)
    (Filter.Eventually.of_forall fun ω => by
      simpa only [q,norm_mul,Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hb' t ω) (abs_nonneg (f ω)))
  let F t := (hmf t).toLp (q m t)
  let F' t := (hmf' t).toLp (q m' t)
  refine ⟨F,F',fun t => (hmf t).coeFn_toLp,fun t => (hmf' t).coeFn_toLp,?_⟩
  intro t
  let ψ : ℝ → Ω → ℝ := fun h ω => ((m (t+h) ω-m t ω)/h-m' t ω)*f ω
  have hψmeas h : AEStronglyMeasurable (ψ h) μ := by
    simpa only [ψ,div_eq_mul_inv] using
      ((((hm (t+h)).sub (hm t)).mul_const h⁻¹).sub (hm' t)).mul hf.1
  have hψbound h ω : |ψ h ω| ≤ |(2*D)*f ω| := by
    have hq : |(m (t+h) ω-m t ω)/h| ≤ D := by
      by_cases he : h = 0
      · simp [he,hD]
      · have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
          (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (hd r ω).differentiableAt)
          (fun r _ => by rw [(hd r ω).deriv]; exact hb' r ω)
          convex_univ (Set.mem_univ t) (Set.mem_univ (t+h))
        rw [Real.norm_eq_abs,Real.norm_eq_abs,add_sub_cancel_left] at hmv
        rw [abs_div]
        exact (div_le_iff₀ (abs_pos.mpr he)).mpr hmv
    have he : |(m (t+h) ω-m t ω)/h-m' t ω| ≤ 2*D :=
      (abs_sub _ _).trans (by linarith [hb' t ω])
    dsimp only [ψ]
    rw [abs_mul,abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hD)]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg _)
  have hψlim ω : Tendsto (fun h => ψ h ω) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ht := (hasDerivAt_iff_tendsto_slope_zero.mp (hd t ω))
    have ht' : Tendsto (fun h => (m (t+h) ω-m t ω)/h) (𝓝[≠] (0 : ℝ))
        (𝓝 (m' t ω)) := by
      simpa only [smul_eq_mul,div_eq_inv_mul] using ht
    simpa only [ψ,sub_self,zero_mul] using
      (ht'.sub (tendsto_const_nhds (x := m' t ω))).mul_const (f ω)
  have ht := tendsto_eLpNorm_two_of_dominated μ (𝓝[≠] (0 : ℝ))
    (hf.const_mul (2*D)) (Eventually.of_forall hψmeas)
    (Eventually.of_forall fun h => Eventually.of_forall (hψbound h))
    (Eventually.of_forall hψlim)
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun h : ℝ => h⁻¹ • (F (t+h)-F t)) (q m' t) (hmf' t)).mpr
  apply ht.congr
  intro h
  symm
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_smul h⁻¹ (F (t+h)-F t), Lp.coeFn_sub (F (t+h)) (F t),
    (hmf (t+h)).coeFn_toLp,(hmf t).coeFn_toLp] with ω h1 h2 h3 h4
  change F (t+h) ω = q m (t+h) ω at h3
  change F t ω = q m t ω at h4
  simp only [Pi.sub_apply,h1,h2,Pi.smul_apply,smul_eq_mul,h3,h4,q,ψ]
  ring

end EinsteinRelation.Correctors
