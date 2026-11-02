import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module

/-!
# Abstract weighted growth for a strongly continuous semigroup

For a strongly continuous semigroup on a complex Hilbert space whose generator
graph is the relation `Gen`, a bounded operator `M` with the one-sided energy
estimate `Re ⟪M f, M g⟫ ≤ κ ‖M f‖²` on the generator graph satisfies
`‖M (P t f)‖ ≤ exp (κ t) ‖M f‖` for every `f`.  The generator domain is shown
dense by time averages of orbits, so the estimate extends from the domain.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull

section S5Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The content of the physical semigroup predicates, for an abstract generator graph. -/
structure S5Semigroup (P : ℝ≥0 → E →L[ℂ] E) (Gen : E → E → Prop) : Prop where
  zero : P 0 = ContinuousLinearMap.id ℂ E
  add : ∀ s t, P (s + t) = (P s).comp (P t)
  cont : ∀ f, Continuous (fun t : ℝ≥0 => P t f)
  gen : ∀ f g, Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ Gen f g

omit [CompleteSpace E] in
theorem s5_cinv_smul (r : ℝ) (x : E) : ((r : ℂ))⁻¹ • x = r⁻¹ • x := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r⁻¹ x, RCLike.ofReal_inv]
  all_goals rfl

theorem s5_tendsto_nnreal_coe_nhdsGT :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ≥0)))
    rwa [NNReal.coe_zero] at h
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact NNReal.coe_pos.mpr ht

variable {P : ℝ≥0 → E →L[ℂ] E} {Gen : E → E → Prop}

omit [CompleteSpace E] in
theorem S5Semigroup.map_gen (hP : S5Semigroup P Gen) {f g : E} (hfg : Gen f g) (t : ℝ≥0) :
    Gen (P t f) (P t g) := by
  apply (hP.gen _ _).mp
  have h := ((P t).continuous.tendsto g).comp ((hP.gen f g).mpr hfg)
  convert h using 1
  ext s
  simp only [Function.comp_apply, map_smul, map_sub]
  have hc : P t (P s f) = P s (P t f) := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.add, add_comm, hP.add,
      ContinuousLinearMap.comp_apply]
  rw [hc]

omit [CompleteSpace E] in
theorem S5Semigroup.hasDerivWithinAt_orbit (hP : S5Semigroup P Gen) {f g : E} (hfg : Gen f g)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => P (Real.toNNReal s) f)
      (P (Real.toNNReal t) g) (Ici t) t := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mpr
  have he : Tendsto (fun s : ℝ => Real.toNNReal (s - t))
      (𝓝[>] t) (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def, id_eq, sub_self, Real.toNNReal_zero] using
        (continuous_real_toNNReal.comp
          (continuous_id.fun_sub (continuous_const (y := t)))).tendsto t
          |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  have h := (((P (Real.toNNReal t)).continuous.tendsto g).comp
    ((hP.gen f g).mpr hfg)).comp he
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change t < s at hs
  have hs0 : 0 ≤ s := ht.trans hs.le
  have ha : Real.toNNReal t + Real.toNNReal (s - t) = Real.toNNReal s := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left ht,
      max_eq_left (sub_nonneg.mpr hs.le), max_eq_left hs0]
    ring
  simp only [Function.comp_apply]
  rw [map_smul, map_sub]
  simp only [slope_def_module,
    Real.coe_toNNReal', max_eq_left (sub_nonneg.mpr hs.le),
    RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rw [← ContinuousLinearMap.comp_apply, ← hP.add, ha]
  rfl

/-- Time averages of an orbit lie in the generator domain and converge to the datum. -/
theorem S5Semigroup.exists_gen_approx (hP : S5Semigroup P Gen) (f : E) :
    ∃ F G : ℝ → E, (∀ δ : ℝ, 0 < δ → Gen (F δ) (G δ)) ∧
      Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 f) := by
  let Φ : ℝ → E := fun s => P s.toNNReal f
  have hΦ : Continuous Φ := (hP.cont f).comp continuous_real_toNNReal
  let g : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, Φ s
  have hg : ∀ x, HasDerivAt g (Φ x) x := fun x =>
    (hΦ.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hg0 : g 0 = 0 := intervalIntegral.integral_same
  have hΦ0 : Φ 0 = f := by
    simp only [Φ, Real.toNNReal_zero, hP.zero, ContinuousLinearMap.id_apply]
  have hshift : ∀ x t : ℝ, 0 ≤ x → 0 ≤ t →
      P t.toNNReal (g x) = g (x + t) - g t := by
    intro x t hx ht
    have h1 : P t.toNNReal (g x) = ∫ s in (0 : ℝ)..x, P t.toNNReal (Φ s) :=
      ((P t.toNNReal).intervalIntegral_comp_comm
        (hΦ.intervalIntegrable (μ := volume) 0 x)).symm
    have h2 : (∫ s in (0 : ℝ)..x, P t.toNNReal (Φ s)) = ∫ s in (0 : ℝ)..x, Φ (s + t) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by
        rw [uIcc_of_le hx] at hs
        exact hs.1
      have hadd : t.toNNReal + s.toNNReal = (s + t).toNNReal := by
        rw [Real.toNNReal_add hs0 ht, add_comm]
      change P t.toNNReal (P s.toNNReal f) = P (s + t).toNNReal f
      rw [← ContinuousLinearMap.comp_apply, ← hP.add, hadd]
    rw [h1, h2, intervalIntegral.integral_comp_add_right]
    have h3 := intervalIntegral.integral_interval_sub_left
      (hΦ.intervalIntegrable (μ := volume) 0 (x + t))
      (hΦ.intervalIntegrable (μ := volume) 0 t)
    rw [zero_add]
    exact h3.symm
  refine ⟨fun δ => δ⁻¹ • g δ, fun δ => δ⁻¹ • (Φ δ - f), ?_, ?_⟩
  · intro δ hδ
    rw [← hP.gen]
    have hs := ((hg δ).tendsto_slope_zero_right).sub ((hg 0).tendsto_slope_zero_right)
    have hs' := (hs.const_smul δ⁻¹).comp s5_tendsto_nnreal_coe_nhdsGT
    rw [hΦ0] at hs'
    refine Tendsto.congr' ?_ hs'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htp : (0 : ℝ) ≤ (t : ℝ) := t.property
    have e1 : P t (δ⁻¹ • g δ) = δ⁻¹ • (g (δ + (t : ℝ)) - g (t : ℝ)) := by
      have := hshift δ (t : ℝ) hδ.le htp
      rw [Real.toNNReal_coe] at this
      rw [(P t).map_smul_of_tower δ⁻¹ (g δ), this]
    simp only [Function.comp_apply]
    rw [e1, s5_cinv_smul, hg0, zero_add]
    module
  · have h := (hg 0).tendsto_slope_zero_right
    rw [hΦ0] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, hg0, sub_zero]

/-- The weighted growth bound for a strongly continuous semigroup with one-sided energy
estimate on its generator graph. -/
theorem S5Semigroup.weighted_growth (hP : S5Semigroup P Gen) (M : E →L[ℂ] E) (κ : ℝ)
    (hE : ∀ f g, Gen f g → (inner ℂ (M f) (M g)).re ≤ κ * ‖M f‖ ^ 2)
    (f : E) (t : ℝ≥0) :
    ‖M (P t f)‖ ≤ Real.exp (κ * (t : ℝ)) * ‖M f‖ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  have hdom : ∀ f g, Gen f g → ∀ t : ℝ≥0,
      ‖M (P t f)‖ ≤ Real.exp (κ * (t : ℝ)) * ‖M f‖ := by
    intro f g hfg t
    let u : ℝ → E := fun s => M (P s.toNNReal f)
    have hu : Continuous u := M.continuous.comp ((hP.cont f).comp continuous_real_toNNReal)
    have hd : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun r => ‖u r‖ ^ 2)
        (2 * inner ℝ (u s) (M (P s.toNNReal g))) (Ici s) s := by
      intro s hs
      have h1 := hP.hasDerivWithinAt_orbit hfg s hs
      let Mr : E →L[ℝ] E := M.restrictScalars ℝ
      have hl : HasFDerivAt (⇑Mr) Mr (P s.toNNReal f) := Mr.hasFDerivAt
      have h2 : HasDerivWithinAt (⇑Mr ∘ fun r : ℝ => P r.toNNReal f) (Mr (P s.toNNReal g))
          (Ici s) s := hl.comp_hasDerivWithinAt s h1
      have h3 : HasDerivWithinAt u (M (P s.toNNReal g)) (Ici s) s := h2
      exact h3.norm_sq
    have hb := le_gronwallBound_of_liminf_deriv_right_le
      (f := fun s => ‖u s‖ ^ 2)
      (f' := fun s => 2 * inner ℝ (u s) (M (P s.toNNReal g)))
      (δ := ‖u 0‖ ^ 2) (K := 2 * κ) (ε := 0) (a := 0) (b := (t : ℝ))
      (hu.norm.pow 2).continuousOn
      (fun s hs _ hr => (hd s hs.1).liminf_right_slope_le hr)
      le_rfl
      (fun s _ => by
        have hs := hE (P s.toNNReal f) (P s.toNNReal g) (hP.map_gen hfg s.toNNReal)
        have e : inner ℝ (u s) (M (P s.toNNReal g)) =
            (inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re :=
          rfl
        change 2 * inner ℝ (u s) (M (P s.toNNReal g)) ≤ 2 * κ * ‖u s‖ ^ 2 + 0
        rw [e, add_zero]
        change 2 * (inner ℂ (M (P s.toNNReal f)) (M (P s.toNNReal g))).re ≤
          2 * κ * ‖M (P s.toNNReal f)‖ ^ 2
        linarith only [hs])
      (t : ℝ) ⟨t.property, le_rfl⟩
    rw [gronwallBound_ε0, sub_zero] at hb
    have e2 : Real.exp (2 * κ * (t : ℝ)) = Real.exp (κ * (t : ℝ)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hu0 : u 0 = M f := by
      simp only [u, Real.toNNReal_zero, hP.zero, ContinuousLinearMap.id_apply]
    have hut : u (t : ℝ) = M (P t f) := by
      simp only [u, Real.toNNReal_coe]
    rw [hu0, hut] at hb
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    calc ‖M (P t f)‖ ^ 2 ≤ ‖M f‖ ^ 2 * Real.exp (2 * κ * (t : ℝ)) := by
          exact hb
      _ =(Real.exp (κ * (t : ℝ)) * ‖M f‖) ^ 2 := by rw [e2]; ring
  obtain ⟨F, G, hFG, hF⟩ := hP.exists_gen_approx f
  have hl : Tendsto (fun δ => ‖M (P t (F δ))‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖M (P t f)‖) :=
    (((M.continuous.comp (P t).continuous).tendsto f).comp hF).norm
  have hr : Tendsto (fun δ => Real.exp (κ * (t : ℝ)) * ‖M (F δ)‖) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (κ * (t : ℝ)) * ‖M f‖)) :=
    (((M.continuous.tendsto f).comp hF).norm).const_mul _
  refine le_of_tendsto_of_tendsto hl hr ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hdom (F δ) (G δ) (hFG δ hδ) t

end S5Abstract

end EinsteinFull
