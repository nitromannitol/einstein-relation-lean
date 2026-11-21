import EinsteinFull.External.DFGW.ScaledBrownianFDD
import EinsteinFull.Calculus.CLConstantEnvironmentDiffusivity

/-! # Finite-dimensional limits at arbitrary times

Brownian scaling extends finite-dimensional convergence on the unit interval to every finite
family of nonnegative times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ} {D : Mat d} {W : Measure (Path d)}

/-- Unit-interval finite-dimensional convergence implies convergence at arbitrary times. -/
theorem tendstoInDistribution_fdd_of_unit_interval
    (Y : Ω → Path d) (hW : IsBrownianLaw D W)
    (hunit : ∀ (m : ℕ) (u : Fin m → ℝ≥0), (∀ j, u j ≤ 1) →
      letI : IsProbabilityMeasure W := hW.1
      TendstoInDistribution (fun (ε : ℝ) η j => ε • Y η ((ε⁻¹ ^ 2).toNNReal * u j))
        (𝓝[>] 0) (fun γ : Path d => fun j => γ (u j)) (fun _ => P) W)
    (m : ℕ) (t : Fin m → ℝ≥0) :
    letI : IsProbabilityMeasure W := hW.1
    TendstoInDistribution (fun (ε : ℝ) η j => ε • Y η ((ε⁻¹ ^ 2).toNNReal * t j))
      (𝓝[>] 0) (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  classical
  let : IsProbabilityMeasure W := hW.1
  let R : ℝ≥0 := 1 + ∑ j, t j
  have hR : 0 < R := by simp only [R]; positivity
  let c : ℝ := Real.sqrt R
  have hc : 0 < c := Real.sqrt_pos.2 (by exact_mod_cast hR)
  have hc2 : c ^ 2 = (R : ℝ) := Real.sq_sqrt R.coe_nonneg
  let u : Fin m → ℝ≥0 := fun j => t j / R
  have hu (j : Fin m) : u j ≤ 1 := by
    apply (div_le_one hR).2
    have hsum : t j ≤ ∑ k, t k := Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ t k)) (Finset.mem_univ j)
    dsimp only [R]
    exact le_trans hsum (le_add_of_nonneg_left zero_le_one)
  have hdelta : Tendsto (fun ε : ℝ => ε / c) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h := ((continuous_id.div_const c).tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε hc
  have htScale (j : Fin m) : ((c⁻¹ ^ 2).toNNReal * t j) = u j := by
    apply NNReal.eq
    change (((c⁻¹ ^ 2).toNNReal : ℝ≥0) : ℝ) * (t j : ℝ) =
      ((t j / R : ℝ≥0) : ℝ)
    rw [Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_div, inv_pow, hc2]
    ring
  have htime (ε : ℝ) (j : Fin m) : (((ε / c)⁻¹ ^ 2).toNNReal * u j) =
      (ε⁻¹ ^ 2).toNNReal * t j := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), u, NNReal.coe_div]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, hc2]
    have hRn : (R : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hR)
    field_simp
  let E : Path d → Fin m → Vec d := fun γ j => γ (t j)
  let Z : Path d → Fin m → Vec d := fun γ j => c • γ (u j)
  have hE : Continuous E := by
    apply continuous_pi
    intro j
    exact continuous_eval_const (t j)
  have hrescale : W.map (rescalePath c) = W :=
    EinsteinFull.Blueprint.IsBrownianLaw.unique
      (EinsteinFull.Blueprint.IsBrownianLaw.map_rescalePath hW (ne_of_gt hc)) hW
  have hZeq : Z = E ∘ rescalePath c := by
    funext γ j
    change c • γ (u j) = c • γ ((c⁻¹ ^ 2).toNNReal * t j)
    rw [htScale]
  have hmap : W.map Z = W.map E := by
    rw [hZeq, ← Measure.map_map hE.measurable (TimeChangeCovariance.continuous_rescalePath c).measurable,
      hrescale]
  have h := hunit m u hu
  let V : ℝ → Ω → Fin m → Vec d := fun ε η j => (ε / c) •
    Y η (((ε / c)⁻¹ ^ 2).toNNReal * u j)
  have hV : TendstoInDistribution V (𝓝[>] 0) (fun γ : Path d => fun j => γ (u j))
      (fun _ => P) W := ⟨fun ε => h.forall_aemeasurable (ε / c), h.aemeasurable_limit,
        h.tendsto.comp hdelta⟩
  have hcV := hV.continuous_comp (g := fun x : Fin m → Vec d => c • x) (continuous_id.const_smul c)
  have hA : TendstoInDistribution (fun (ε : ℝ) η j => ε •
      Y η ((ε⁻¹ ^ 2).toNNReal * t j)) (𝓝[>] 0) Z (fun _ => P) W := by
    apply TendstoInDistribution.congr (h := hcV) _ _
    · intro ε
      apply ae_of_all P
      intro η
      funext j i
      simp only [Function.comp_apply, V, Pi.smul_apply, smul_eq_mul, htime]
      field_simp
    · exact ae_of_all W fun γ => rfl
  refine ⟨hA.forall_aemeasurable, hE.measurable.aemeasurable, ?_⟩
  simpa only [hmap] using hA.tendsto

end EinsteinFull.External.DFGW
