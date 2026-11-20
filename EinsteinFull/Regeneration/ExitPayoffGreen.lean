import EinsteinFull.Regeneration.ExitPayoffDynkin
import EinsteinFull.Calculus.SunaS1KilledResolventIdentification

/-!
# Discounted occupation before the exit time

The discounted occupation of a bounded observable before the exit from an open set is
a path functional. Its expectation is a representative of the killed resolvent of the
observable, and it converges to the undiscounted occupation as the discount vanishes.
-/

open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- The discounted occupation of an observable before the exit from a set. -/
noncomputable def discountedOccupation (U : Set (Vec d)) (g : Vec d → ℝ) (α : ℝ)
    (γ : Path d) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), {s : ℝ | (s.toNNReal : ℝ≥0∞) <
    MarkovProcess.ContinuousPath.exitTime U γ}.indicator
      (fun s => Real.exp (-α * s) * g (γ s.toNNReal)) s

/-- The survival event in time and path is measurable. -/
theorem measurableSet_survival_time (U : Set (Vec d)) (hU : IsOpen U) :
    MeasurableSet {p : Path d × ℝ | (p.2.toNNReal : ℝ≥0∞) <
      MarkovProcess.ContinuousPath.exitTime U p.1} :=
  measurableSet_lt ((measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal).comp
    measurable_snd) ((MarkovProcess.ContinuousPath.measurable_exitTime U hU).comp measurable_fst)

theorem measurable_discountedOccupation_integrand (U : Set (Vec d)) (hU : IsOpen U)
    (g : Vec d → ℝ) (hg : Measurable g) (α : ℝ) :
    Measurable (fun p : Path d × ℝ => {s : ℝ | (s.toNNReal : ℝ≥0∞) <
      MarkovProcess.ContinuousPath.exitTime U p.1}.indicator
        (fun s => Real.exp (-α * s) * g (p.1 s.toNNReal)) p.2) := by
  have heval : Measurable (fun p : Path d × ℝ => p.1 p.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hf : Measurable (fun p : Path d × ℝ => Real.exp (-α * p.2) * g (p.1 p.2.toNNReal)) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul (hg.comp heval)
  have h := hf.indicator (measurableSet_survival_time U hU)
  have he : (fun p : Path d × ℝ => {s : ℝ | (s.toNNReal : ℝ≥0∞) <
      MarkovProcess.ContinuousPath.exitTime U p.1}.indicator
        (fun s => Real.exp (-α * s) * g (p.1 s.toNNReal)) p.2) =
      {p : Path d × ℝ | (p.2.toNNReal : ℝ≥0∞) <
        MarkovProcess.ContinuousPath.exitTime U p.1}.indicator
        (fun p => Real.exp (-α * p.2) * g (p.1 p.2.toNNReal)) := by
    funext p
    rfl
  rw [he]
  exact h

theorem measurable_discountedOccupation (U : Set (Vec d)) (hU : IsOpen U)
    (g : Vec d → ℝ) (hg : Measurable g) (α : ℝ) :
    Measurable (discountedOccupation U g α) :=
  ((measurable_discountedOccupation_integrand U hU g hg α).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

/-- Before a finite exit, the undiscounted occupation is the integral up to the exit time. -/
theorem discountedOccupation_zero (U : Set (Vec d)) (g : Vec d → ℝ) (γ : Path d)
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    discountedOccupation U g 0 γ =
      ∫ s in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTime U γ).toReal, g (γ s.toNNReal) := by
  set τ := MarkovProcess.ContinuousPath.exitTime U γ with hτ
  have hA : MeasurableSet {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
      measurable_const
  have hset : Set.Ioi (0 : ℝ) ∩ {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ} = Set.Ioo 0 τ.toReal := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨hs, hsτ⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).mp hsτ⟩
    · rintro ⟨hs, hsτ⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).mpr hsτ⟩
  unfold discountedOccupation
  rw [setIntegral_indicator hA, hset, intervalIntegral.integral_of_le ENNReal.toReal_nonneg,
    integral_Ioc_eq_integral_Ioo]
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]

/-- The discounted occupation is bounded by the observable bound times the exit time. -/
theorem abs_discountedOccupation_le (U : Set (Vec d)) (g : Vec d → ℝ) (B : ℝ)
    (hB : ∀ y, |g y| ≤ B) (α : ℝ) (hα : 0 ≤ α) (γ : Path d)
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    |discountedOccupation U g α γ| ≤
      B * (MarkovProcess.ContinuousPath.exitTime U γ).toReal := by
  set τ := MarkovProcess.ContinuousPath.exitTime U γ with hτ
  have hA : MeasurableSet {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
      measurable_const
  have hset : Set.Ioi (0 : ℝ) ∩ {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ} = Set.Ioo 0 τ.toReal := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨hs, hsτ⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).mp hsτ⟩
    · rintro ⟨hs, hsτ⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).mpr hsτ⟩
  unfold discountedOccupation
  rw [setIntegral_indicator hA, hset]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioo (0 : ℝ) τ.toReal)
    (f := fun s => Real.exp (-α * s) * g (γ s.toNNReal)) (C := B)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) (fun s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-α * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.1])
      calc Real.exp (-α * s) * |g (γ s.toNNReal)| ≤ 1 * B :=
            mul_le_mul he (hB _) (abs_nonneg _) zero_le_one
        _ = B := one_mul B)
  rw [Real.norm_eq_abs, Real.volume_real_Ioo_of_le ENNReal.toReal_nonneg, sub_zero] at h
  exact h

/-- As the discount vanishes, the discounted occupation converges to the undiscounted one. -/
theorem tendsto_discountedOccupation (U : Set (Vec d)) (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : ∀ y, |g y| ≤ B) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n)
    (hα0 : Tendsto α atTop (𝓝 0)) (γ : Path d)
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    Tendsto (fun n => discountedOccupation U g (α n) γ) atTop
      (𝓝 (discountedOccupation U g 0 γ)) := by
  unfold discountedOccupation
  set τ := MarkovProcess.ContinuousPath.exitTime U γ with hτ
  have hA : MeasurableSet {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
      measurable_const
  have hset : Set.Ioi (0 : ℝ) ∩ {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ} = Set.Ioo 0 τ.toReal := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨hs, hsτ⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).mp hsτ⟩
    · rintro ⟨hs, hsτ⟩
      exact ⟨hs, (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).mpr hsτ⟩
  have hrw : ∀ a : ℝ, (∫ s in Set.Ioi (0 : ℝ), {s : ℝ | (s.toNNReal : ℝ≥0∞) < τ}.indicator
      (fun s => Real.exp (-a * s) * g (γ s.toNNReal)) s) =
      ∫ s in Set.Ioo (0 : ℝ) τ.toReal, Real.exp (-a * s) * g (γ s.toNNReal) := by
    intro a
    rw [setIntegral_indicator hA, hset]
  simp only [hrw]
  have hgm : Measurable (fun s : ℝ => g (γ s.toNNReal)) :=
    hg.comp (γ.continuous.comp continuous_real_toNNReal).measurable
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro n
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      hgm).aestronglyMeasurable
  · exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-α n * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.1, hα n])
    calc Real.exp (-α n * s) * |g (γ s.toNNReal)| ≤ 1 * B :=
          mul_le_mul he (hB _) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  · filter_upwards with s
    apply Tendsto.mul _ tendsto_const_nhds
    have h : Tendsto (fun n => -α n * s) atTop (𝓝 (-0 * s)) :=
      (hα0.neg).mul tendsto_const_nhds
    exact (Real.continuous_exp.tendsto _).comp h


variable {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}

/-- The physical L² Laplace transform of the killed semigroup applied to a bounded
observable is represented by the expected discounted occupation before the exit. -/
theorem killedLaplace_ae_eq_discountedOccupation
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ)
    (hB : ∀ y, |g y| ≤ B) (hgL : MemLp g 2 (physicalReversibleMeasure ω hd lam))
    (α : ℝ) (hα : 0 < α) :
    (fun x => (∫ t : ℝ in Set.Ioi 0, Real.exp (-α * t) •
        gmpKilledL2Operator G U hU t.toNNReal (hgL.toLp g)) x) =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ γ, discountedOccupation U g α γ ∂G.pathLaw x := by
  let m := physicalReversibleMeasure ω hd lam
  have : SigmaFinite m := physicalReversibleMeasure_sigmaFinite hd ω lam
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let gL := hgL.toLp g
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let u : ℝ → Lp ℝ 2 m := fun t => Real.exp (-α * t) • gmpKilledL2Operator G U hU t.toNNReal gL
  -- integrability of the curve, through the interior semigroup
  have hu : Integrable u ν := by
    let p : physicalZeroBoundaryL2 U hd ω lam L hω :=
      ⟨physicalZeroBoundaryProjection U hd ω lam L hω gL,
        physicalZeroBoundaryProjection_mem U hd ω lam L hω gL⟩
    let S := gmpKilledInteriorSemigroup G U hU
    let J := (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL
    have hp (t : ℝ≥0) : gmpKilledL2Operator G U hU t p.val = gmpKilledL2Operator G U hU t gL := by
      have h := congrArg (fun A => A gL) (gmpKilledL2Operator_add_time G U hU t 0)
      simpa only [add_zero, ContinuousLinearMap.comp_apply, gmpKilledL2Operator_apply,
        gmpKilledL2_zero, p] using h.symm
    have hint := J.integrable_comp (S.integrableOn_laplaceIntegrand hα p)
    refine hint.congr (Eventually.of_forall fun t => ?_)
    change J (Real.exp (-α * t) • S t.toNNReal p) = u t
    rw [map_smul]
    change Real.exp (-α * t) • gmpKilledL2Operator G U hU t.toNNReal p.val = u t
    rw [hp]
  -- the joint representative
  let H : ℝ × Path d → ℝ := fun q =>
    {γ : Path d | (q.1.toNNReal : ℝ≥0∞) < localityExitTime U γ}.indicator
      (fun γ => g (γ q.1.toNNReal)) q.2
  have hHm : Measurable H := by
    have heval : Measurable (fun q : ℝ × Path d => q.2 q.1.toNNReal) :=
      (continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp continuous_fst))).measurable
    have hset : MeasurableSet {q : ℝ × Path d |
        (q.1.toNNReal : ℝ≥0∞) < localityExitTime U q.2} :=
      measurableSet_lt ((measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal).comp
        measurable_fst) ((measurable_localityExitTime U hU).comp measurable_snd)
    have h := (hg.comp heval).indicator hset
    have he : H = {q : ℝ × Path d | (q.1.toNNReal : ℝ≥0∞) < localityExitTime U q.2}.indicator
        (fun q => g (q.2 q.1.toNNReal)) := by
      funext q
      rfl
    rw [he]
    exact h
  let κ : Kernel (ℝ × Vec d) (Path d) := Kernel.comap G.pathLaw Prod.snd measurable_snd
  let Uf : ℝ × Vec d → ℝ := fun q => Real.exp (-α * q.1) * ∫ γ, H (q.1, γ) ∂G.pathLaw q.2
  have hUf : Measurable Uf := by
    have hk := (hHm.comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable
      |>.integral_kernel_prod_right' (κ := κ)
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hk.measurable
  have hkill : ∀ (t : ℝ) (x : Vec d), (∫ y, g y ∂gmpKilledEndpointKernel G U hU t.toNNReal x) =
      ∫ γ, H (t, γ) ∂G.pathLaw x := by
    intro t x
    rw [integral_gmpKilledEndpointKernel G U hU t.toNNReal x g hg]
    rfl
  have heq : ∀ t, (fun x => Uf (t, x)) =ᵐ[m] u t := by
    intro t
    have hsmul := Lp.coeFn_smul (Real.exp (-α * t)) (gmpKilledL2Operator G U hU t.toNNReal gL)
    have hrep := gmpKilledL2_ae_eq G U hU t.toNNReal gL
    have hgg : (gL : Vec d → ℝ) =ᵐ[m] g := hgL.coeFn_toLp
    have hint : ∀ᵐ x ∂m, (∫ y, gL y ∂gmpKilledEndpointKernel G U hU t.toNNReal x) =
        ∫ y, g y ∂gmpKilledEndpointKernel G U hU t.toNNReal x := by
      by_cases ht : 0 < t.toNNReal
      · exact Eventually.of_forall fun x =>
          integral_gmpKilledEndpointKernel_congr_ae G U hU t.toNNReal ht x _ _ hgg
      · have ht0 : t.toNNReal = 0 := le_antisymm (not_lt.mp ht) zero_le
        filter_upwards [hgg] with x hx
        rw [ht0, gmpKilledEndpointKernel_zero G U hU x]
        by_cases hxU : x ∈ U
        · simp only [Set.indicator_of_mem hxU, integral_dirac, hx]
        · simp only [Set.indicator_of_notMem hxU, integral_zero_measure]
    filter_upwards [hsmul, hrep, hint] with x hs hr hi
    change Real.exp (-α * t) * ∫ γ, H (t, γ) ∂G.pathLaw x = u t x
    change Real.exp (-α * t) * ∫ γ, H (t, γ) ∂G.pathLaw x =
      (Real.exp (-α * t) • gmpKilledL2Operator G U hU t.toNNReal gL) x
    rw [hs, Pi.smul_apply, smul_eq_mul, gmpKilledL2Operator_apply, hr, hi, hkill]
  have hjoint := EinsteinFull.u2_real_coeFn_integral_joint_l2_sigmaFinite hu hUf heq
  filter_upwards [hjoint] with x hx
  rw [hx]
  -- Fubini in time and path
  have hFint : Integrable (Function.uncurry fun (t : ℝ) (γ : Path d) =>
      Real.exp (-α * t) * H (t, γ)) (ν.prod (G.pathLaw x)) := by
    have hdom : Integrable (fun z : ℝ × Path d => Real.exp (-α * z.1) * B)
        (ν.prod (G.pathLaw x)) :=
      (exp_neg_integrableOn_Ioi 0 hα).mul_prod (integrable_const B)
    refine hdom.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
        hHm).aestronglyMeasurable
    · change ‖Real.exp (-α * z.1) * H (z.1, z.2)‖ ≤ Real.exp (-α * z.1) * B
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simp only [H, Set.indicator]
      split_ifs
      · exact hB _
      · simpa using hB0
  calc ∫ t, Uf (t, x) ∂ν
      = ∫ t, ∫ γ, Real.exp (-α * t) * H (t, γ) ∂G.pathLaw x ∂ν := by
        apply integral_congr_ae
        filter_upwards with t
        exact (integral_const_mul _ _).symm
    _ = ∫ γ, ∫ t, Real.exp (-α * t) * H (t, γ) ∂ν ∂G.pathLaw x :=
        integral_integral_swap hFint
    _ = ∫ γ, discountedOccupation U g α γ ∂G.pathLaw x := by
        apply integral_congr_ae
        filter_upwards with γ
        unfold discountedOccupation
        apply integral_congr_ae
        filter_upwards with t
        simp only [H, Set.indicator, Set.mem_ofPred_eq, localityExitTime_eq_exitTime]
        split_ifs <;> simp

end EinsteinFull.Regeneration
