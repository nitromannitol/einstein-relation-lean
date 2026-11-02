import EinsteinFull.Calculus.RadialPrimitiveSupport

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem positivePart_sq_remainder (r s K : ℝ) :
    0 ≤ (max (s - K) 0)^2 - (max (r - K) 0)^2 -
      2 * max (r - K) 0 * (s-r) ∧
    (max (s - K) 0)^2 - (max (r - K) 0)^2 -
      2 * max (r - K) 0 * (s-r) ≤ (s-r)^2 := by
  rcases le_total r K with hr | hr <;> rcases le_total s K with hs | hs
  · rw [max_eq_right (sub_nonpos.mpr hr), max_eq_right (sub_nonpos.mpr hs)]
    constructor <;> nlinarith [sq_nonneg (s-r)]
  · rw [max_eq_right (sub_nonpos.mpr hr), max_eq_left (sub_nonneg.mpr hs)]
    constructor <;> nlinarith [sq_nonneg (s-K), mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr (le_trans hr hs))]
  · rw [max_eq_left (sub_nonneg.mpr hr), max_eq_right (sub_nonpos.mpr hs)]
    constructor <;> nlinarith [sq_nonneg (r-K), mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr (le_trans hs hr)), sq_nonneg (s-K)]
  · rw [max_eq_left (sub_nonneg.mpr hr), max_eq_left (sub_nonneg.mpr hs)]
    constructor <;> nlinarith [sq_nonneg (s-r)]

private theorem threshold_ratio {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) :
    0 ≤ max (r-K) 0 / r ∧ max (r-K) 0 / r ≤ 1 ∧
      (max (r-K) 0 / r) * r = max (r-K) 0 := by
  by_cases hz : r = 0
  · simp [hz, max_eq_right (neg_nonpos.mpr hK)]
  have hp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  exact ⟨div_nonneg (le_max_right _ _) hr,
    (div_le_one hp).mpr (max_le (by linarith) hr), div_mul_cancel₀ _ hz⟩

private theorem threshold_remainder (K : ℝ) (hK : 0 ≤ K) (x y : ℂ) :
    ‖(max (‖y‖-K) 0)^2 - (max (‖x‖-K) 0)^2 -
      2 * inner ℝ ((max (‖x‖-K) 0 / ‖x‖) • x) (y-x)‖ ≤
        2 * ‖y-x‖^2 := by
  obtain ⟨ha, ha1, har⟩ := threshold_ratio hK (norm_nonneg x)
  obtain ⟨hlo, hhi⟩ := positivePart_sq_remainder ‖x‖ ‖y‖ K
  have hn : (‖y‖-‖x‖)^2 ≤ ‖y-x‖^2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg (norm_nonneg _)] using abs_norm_sub_norm_le y x)
  have hid := norm_add_sq_real x (y-x)
  rw [add_sub_cancel] at hid
  rw [real_inner_smul_left, Real.norm_eq_abs, abs_le]
  have hm := mul_nonneg ha (sub_nonneg.mpr hn)
  have hm1 := mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg ‖y-x‖)
  have hi := congrArg (fun q : ℝ => (max (‖x‖-K) 0 / ‖x‖) * q) hid
  have hr := congrArg (fun q : ℝ => 2 * q * (‖y‖-‖x‖)) har
  have hm0 := mul_nonneg ha (sq_nonneg (‖y‖-‖x‖))
  constructor <;> nlinarith only [hlo, hhi, hm, hm1, hm0, hi, hr, hn, sq_nonneg ‖y-x‖]

private theorem threshold_memLp {d : ℕ} (μ : Measure (FieldPair d))
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℂ 2 μ) :
    MemLp (fun ω => (max (‖f ω‖-K) 0 / ‖f ω‖) • f ω) 2 μ := by
  have hf := Lp.aestronglyMeasurable f
  have hm : AEStronglyMeasurable (fun ω => max (‖f ω‖-K) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable hf.norm
  apply (Lp.memLp f).mono
    ((hm.aemeasurable.div hf.norm.aemeasurable).aestronglyMeasurable.smul hf)
  exact Eventually.of_forall fun ω => by
    obtain ⟨ha, ha1, _⟩ := threshold_ratio hK (norm_nonneg (f ω))
    change ‖(max (‖f ω‖-K) 0 / ‖f ω‖) • f ω‖ ≤ ‖f ω‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    exact mul_le_of_le_one_left (norm_nonneg _) ha1

private theorem threshold_energy_integrable {d : ℕ} (μ : Measure (FieldPair d))
    (K : ℝ) (hK : 0 ≤ K) (f : Lp ℂ 2 μ) :
    Integrable (fun ω => (max (‖f ω‖-K) 0)^2) μ := by
  have hm : AEStronglyMeasurable (fun ω => max (‖f ω‖-K) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f).norm
  apply (Lp.memLp f).norm.integrable_sq.mono' (hm.pow 2)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (le_max_right _ _)
    exact max_le (by linarith) (norm_nonneg _)

/-- The squared excess above a nonnegative norm threshold is differentiable on actual L2. -/
theorem response_threshold_excess_energy_hasFDerivAt
    {d : ℕ} (μ : Measure (FieldPair d)) (K : ℝ) (hK : 0 ≤ K)
    (f : Lp ℂ 2 μ) :
    ∃ v : Lp ℂ 2 μ,
      (v =ᵐ[μ] fun ω => ((max (‖f ω‖ - K) 0 / ‖f ω‖ : ℝ) : ℂ) * f ω) ∧
      HasFDerivAt
        (fun u : Lp ℂ 2 μ => ∫ ω, (max (‖u ω‖ - K) 0) ^ 2 ∂μ)
        ((2 : ℝ) • innerSL ℝ v) f := by
  let hv := threshold_memLp μ K hK f
  let v := hv.toLp _
  have heq : v =ᵐ[μ] fun ω => (max (‖f ω‖-K) 0 / ‖f ω‖) • f ω := hv.coeFn_toLp
  refine ⟨v, ?_, ?_⟩
  · simpa only [Complex.real_smul, Complex.ofReal_mul] using heq
  have hb (g : Lp ℂ 2 μ) :
      ‖(∫ ω, (max (‖g ω‖-K) 0)^2 ∂μ) -
        (∫ ω, (max (‖f ω‖-K) 0)^2 ∂μ) - 2 * inner ℝ v (g-f)‖ ≤
          2 * ‖g-f‖^2 := by
    have hi := threshold_energy_integrable μ K hK
    have hh := L2.integrable_inner (𝕜 := ℝ) v (g-f)
    have hn : ‖g-f‖^2 = ∫ ω, ‖(g-f) ω‖^2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    have hiDiff : Integrable (fun ω => (max (‖g ω‖-K) 0)^2 -
        (max (‖f ω‖-K) 0)^2) μ := (hi g).sub (hi f)
    rw [L2.inner_def, ← integral_const_mul, ← integral_sub (hi g) (hi f)]
    rw [← integral_sub hiDiff (hh.const_mul 2), hn, ← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae (((hi g).sub (hi f)).sub (hh.const_mul 2)).norm
      ((Lp.memLp (g-f)).norm.integrable_sq.const_mul 2)
    filter_upwards [heq, Lp.coeFn_sub g f] with ω hvω hgω
    simp only [hvω, hgω, Pi.sub_apply]
    exact threshold_remainder K hK (f ω) (g ω)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound 2 ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := Lp ℂ 2 μ) (by decide : 1 < 2))
  apply Eventually.of_forall
  intro h
  simpa only [add_sub_cancel_left, smul_apply,
    innerSL_apply_apply, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖h‖)] using hb (f+h)

end EinsteinFull.Blueprint
