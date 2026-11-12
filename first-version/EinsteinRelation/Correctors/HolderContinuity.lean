import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.TimeChange.EuclideanTransport

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Filter Topology

/-- A positive Euclidean Hölder exponent supplies continuity for the actual Pi carrier.
Source: `paper/main.tex:735-739`. -/
theorem continuousOn_of_holderBound {d : ℕ} {U : Set (Vec d)}
    {α K : ℝ} (hα : 0 < α) {f : Vec d → ℝ} (hf : HolderBound U α f K) :
    ContinuousOn f U := by
  intro x hx
  obtain ⟨S, H, hS, hH, hK, hS_bound, hH_bound⟩ := hf
  have hc : Continuous (fun y : Vec d => H * euclideanNorm (y - x) ^ α) := by
    apply continuous_const.mul
    apply (Real.continuous_rpow_const hα.le).comp
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hlim : Tendsto (fun y : Vec d => H * euclideanNorm (y - x) ^ α)
      (𝓝[U] x) (𝓝 0) := by
    have h := hc.tendsto x
    simpa [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, Real.sqrt_zero, Real.zero_rpow hα.ne', mul_zero]
      using h.mono_left inf_le_left
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa [Real.norm_eq_abs] using hH_bound y hy x hx
end EinsteinRelation.Correctors
