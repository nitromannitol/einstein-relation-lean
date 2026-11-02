import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_tube_u2D_probability
import EinsteinFull.Frozen.GantertRegenerationTail
import EinsteinRelation.Probability.FiniteHistoryMeasurability
import Mathlib.Topology.CompactOpen

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

private lemma transfer_norm_continuous {d : ℕ} :
    Continuous (fun v : Vec d => euclideanNorm v) := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    (continuous_apply i).mul (continuous_apply i))

private lemma transfer_tube_measurable {d : ℕ} (lam : ℝ)
    (m : ℕ) (γ : ℝ → Vec d) (hγ : Continuous γ) (ε : ℝ) :
    MeasurableSet[finiteHistorySigma (Renewal.regenDelta lam) m]
      {z : CoupledSample d | ∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
        euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε} := by
  classical
  let F : Path d → C(ℝ≥0, ℝ) := fun Y =>
    ⟨fun u => euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - γ u),
      transfer_norm_continuous.comp ((continuous_const.fun_smul
        (Y.continuous.comp (continuous_real_toNNReal.comp
          (NNReal.continuous_coe.div_const _)))).fun_sub (hγ.comp NNReal.continuous_coe))⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact transfer_norm_continuous.comp ((continuous_const.fun_smul
      (continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp
          ((NNReal.continuous_coe.comp continuous_snd).div_const _))))).fun_sub
            (hγ.comp (NNReal.continuous_coe.comp continuous_snd)))
  have hA : MeasurableSet {z : CoupledSample d | ∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
      euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε} := by
    have ho := (ContinuousMap.isOpen_setOf_mapsTo (isCompact_Icc :
      IsCompact (Set.Icc (0 : ℝ≥0) (m : ℝ≥0))) (isOpen_Iio : IsOpen (Set.Iio ε))).preimage hF
    have he : {z : CoupledSample d | ∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
        euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε} =
        Prod.fst ⁻¹' (F ⁻¹' {f | Set.MapsTo f (Set.Icc 0 (m : ℝ≥0)) (Set.Iio ε)}) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.MapsTo, Set.mem_Icc, Set.mem_Iio,
        F, ContinuousMap.coe_mk, zero_le, true_and]
      exact ⟨fun h u hu => h u (by exact_mod_cast hu),
        fun h u hu => h (by exact_mod_cast hu)⟩
    rw [he]
    exact ho.measurableSet.preimage measurable_fst
  have hH := Probability.measurable_of_finite_history_prefix
    (Renewal.regenDelta lam) m
    (fun z : CoupledSample d => {z' : CoupledSample d | ∀ u : ℝ≥0,
      (u : ℝ) ≤ (m : ℝ) →
      euclideanNorm (lam • z'.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε}.indicator
        (fun _ => (1 : ℝ)) z) (measurable_const.indicator hA)
    (by
      intro z z' hp _
      have he : (∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
          euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε) ↔
          (∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
          euclideanNorm (lam • z'.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε) := by
        apply forall_congr'
        intro u
        apply imp_congr_right
        intro hu
        rw [hp _ ⟨zero_le, ?_⟩]
        change ((u : ℝ) / lam ^ 2).toNNReal ≤
          (m : ℝ≥0) * (lam ^ 2)⁻¹.toNNReal
        rw [show (m : ℝ≥0) = (m : ℝ).toNNReal by simp,
          ← Real.toNNReal_mul (by positivity)]
        apply Real.toNNReal_le_toNNReal
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr (sq_nonneg lam))
      change (if (∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
        euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε)
        then (1 : ℝ) else 0) =
        (if (∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
        euclideanNorm (lam • z'.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε)
        then 1 else 0)
      rw [he])
  have he : {z : CoupledSample d | ∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
      euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε} =
      {z | {z' : CoupledSample d | ∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
        euclideanNorm (lam • z'.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε}.indicator
          (fun _ => (1 : ℝ)) z = 1} := by
    ext z
    by_cases hz : ∀ u : ℝ≥0, (u : ℝ) ≤ (m : ℝ) →
      euclideanNorm (lam • z.1 ((u : ℝ) / lam ^ 2).toNNReal - γ u) < ε <;> simp [hz]
  rw [he]
  exact measurableSet_eq_fun hH measurable_const

private lemma transfer_fresh_mass {d : ℕ} (Δ : ℝ≥0) (δ : ℝ) (hδ : 0 ≤ δ)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d)
    [IsProbabilityMeasure (K xω)] (hf : FreshBitsAt Δ δ K xω)
    (m : ℕ) (A : Set (CoupledSample d))
    (hA : MeasurableSet[finiteHistorySigma Δ m] A) :
    K xω {z | z ∈ A ∧ z.2 m = true} = ENNReal.ofReal δ * K xω A := by
  classical
  have hAg : MeasurableSet A := Probability.finiteHistorySigma_le Δ m A hA
  have hS : MeasurableSet {z : CoupledSample d | z ∈ A ∧ z.2 m = true} :=
    hAg.inter (measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_snd) measurable_const)
  have hi := hf m (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
    ⟨1, by intro z; by_cases hz : z ∈ A <;> simp [hz]⟩
  have he : (fun z : CoupledSample d => A.indicator (fun _ => (1 : ℝ)) z *
      (if z.2 m = true then 1 else 0)) =
      {z : CoupledSample d | z ∈ A ∧ z.2 m = true}.indicator (fun _ => 1) := by
    funext z
    by_cases ha : z ∈ A <;> by_cases hb : z.2 m = true <;> simp [ha, hb]
  rw [he, integral_indicator_const _ hS, integral_indicator_const _ hAg] at hi
  simp only [smul_eq_mul, mul_one, measureReal_def] at hi
  rw [← ENNReal.ofReal_toReal (measure_ne_top (K xω) _), hi, ENNReal.ofReal_mul hδ,
    ENNReal.ofReal_toReal (measure_ne_top (K xω) A)]

/-- Combine the literal tube bound with the fresh candidate coin and the admitted
GMP first-cycle tail, retaining the preceding construction parameters. -/
theorem node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer_of_deps
    (htube : node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt) :
    node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hr₀, htail⟩ := External.gantert_regeneration_tail d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hr₀, ?_⟩
  intro l hl δ hδ hδ₁
  have hlpos := hl₀.trans_le hl
  obtain ⟨c, C, hc, hC, ht⟩ := htail l hl δ hδ hδ₁
  obtain ⟨B, Ct, cs, η, N, _, _, _, hη, hη₁, hN, _, hprob⟩ :=
    htube d hd Λ₀ r₀ l hlpos
  refine ⟨1 / 2, c, C, η, N, by norm_num, hc, hC, hη, hη₁, hN, ?_⟩
  intro Q lam h₀ h₁ P K hK
  refine ⟨(ht Q lam h₀ h₁ P K hK).1, (ht Q lam h₀ h₁ P K hK).2, ?_⟩
  filter_upwards [hprob Q lam h₀ h₁ P hK.2.2.1, hK.1.1,
    hK.2.1.1, hK.2.2.2.1.1] with ω hω hμ hpath hf
  intro j hj
  let γ₂ : ℝ → Vec d := fun u => min ((25 * l / 4) * u) (25 * l / 8) •
    unitVector (Renewal.forceCoord hd)
  let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
  let γ : ℝ → Vec d := if j = 2 then γ₂ else γ₃
  have hg₂ : Continuous γ₂ := (continuous_const.mul continuous_id).min continuous_const |>.smul continuous_const
  have hg₃ : Continuous γ₃ := by
    apply Continuous.if_le continuous_const
      (hg₂.comp (continuous_id.sub continuous_const)) continuous_id continuous_const
    intro u hu
    change u = 1 at hu
    change 0 = γ₂ (u - 1)
    rw [hu, sub_self]
    simp only [γ₂, mul_zero, min_eq_left (by positivity : (0 : ℝ) ≤ 25 * l / 8), zero_smul]
  have hg : Continuous γ := by
    dsimp only [γ]
    split_ifs <;> assumption
  let E : Set (Path d) := {Y | ∀ u : ℝ≥0, (u : ℝ) ≤ (j : ℝ) - 1 →
    euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - γ u) < l / 32}
  have hp : ENNReal.ofReal (η ^ N) ≤ P (0, ω) E := (hω.2 j hj).2
  have hjcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rcases hj with rfl | rfl <;> norm_num
  have hA : MeasurableSet[finiteHistorySigma (Renewal.regenDelta lam) (j - 1)]
      {z : CoupledSample d | z.1 ∈ E} := by
    have h := transfer_tube_measurable lam (j - 1) γ hg (l / 32)
    rw [hjcast] at h
    exact h
  have hAg := Probability.finiteHistorySigma_le (Renewal.regenDelta lam) (j - 1) _ hA
  have hE : MeasurableSet E := by
    have hi : Measurable (fun Y : Path d => (Y, fun _ : ℕ => false)) :=
      measurable_id.prodMk measurable_const
    exact hAg.preimage hi
  letI := hμ
  have hm := transfer_fresh_mass (Renewal.regenDelta lam) δ hδ.le K (0, ω) hf
    (j - 1) {z | z.1 ∈ E} hA
  have hmap : K (0, ω) {z | z.1 ∈ E} = P (0, ω) E := by
    rw [← hpath, Measure.map_apply measurable_fst hE]
    rfl
  have hcoin : ENNReal.ofReal (δ * η ^ N) ≤
      K (0, ω) {z | z.1 ∈ E ∧ z.2 (j - 1) = true} := by
    simp only [Set.mem_setOf_eq] at hm
    rw [hm, hmap, ENNReal.ofReal_mul hδ.le]
    exact mul_le_mul_right hp _
  have hfin := And.intro hp hcoin
  simp only [E, γ, γ₂, γ₃, ite_apply] at hfin
  exact hfin

end EinsteinFull.Blueprint
