import EinsteinRelation.TimeChange.Pairing
import EinsteinFull.Calculus.C18TubeWeightedTimeMollification
import EinsteinFull.Calculus.C13TubeSmallPowerCoercivity
import EinsteinFull.External.Source.GMPDirichletKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

open Filter MeasureTheory EinsteinRelation EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The exponents in a geometric Moser iteration grow without bound. -/
theorem c13_moser_geometric_exponents_tendsto (p c : ℝ) (hp : 0 < p) (hc : 1 < c) :
    Tendsto (fun n : ℕ => p * c ^ n) atTop atTop := by
  simpa only [mul_comm] using
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const hp

/-- A finite-exponent bound controls each norm superlevel set. -/
theorem c13_moser_superlevel_power_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (q A b : ℝ) (hq : 0 < q)
    (hbound : eLpNorm u (ENNReal.ofReal q) μ ≤ ENNReal.ofReal A) :
    (ENNReal.ofReal b) ^ q * μ {x | ENNReal.ofReal b ≤ ‖u x‖ₑ} ≤
      (ENNReal.ofReal A) ^ q := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have h := mul_meas_ge_le_pow_eLpNorm' μ hq0 hqt (f := u) (ENNReal.ofReal b)
  rw [ENNReal.toReal_ofReal hq.le] at h
  exact h.trans (ENNReal.rpow_le_rpow hbound hq.le)

/-- Powers of a nonnegative ratio below one vanish along the Moser exponents. -/
theorem c13_moser_ratio_power_tendsto (p c r : ℝ) (hp : 0 < p) (hc : 1 < c)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (r ^ (p * c ^ n))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_atTop_of_base_lt_one r (lt_of_lt_of_le (neg_lt_zero.mpr zero_lt_one) hr0) hr1).comp
    (c13_moser_geometric_exponents_tendsto p c hp hc)
  simpa only [Function.comp_apply, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h

/-- Any superlevel strictly above the uniform bound has measure zero. -/
theorem c13_moser_superlevel_measure_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    (p c A b : ℝ) (hp : 0 < p) (hc : 1 < c) (hA : 0 ≤ A) (hb : A < b)
    (hiter : ∀ n : ℕ, eLpNorm u (ENNReal.ofReal (p * c ^ n)) μ ≤ ENNReal.ofReal A) :
    μ {x | ENNReal.ofReal b ≤ ‖u x‖ₑ} = 0 := by
  have hbpos : 0 < b := lt_of_le_of_lt hA hb
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hratio0 : 0 ≤ A / b := div_nonneg hA hbpos.le
  have hratio1 : A / b < 1 := (div_lt_one hbpos).2 hb
  have hlim := c13_moser_ratio_power_tendsto p c (A / b) hp hc hratio0 hratio1
  have hbound : ∀ n : ℕ, μ {x | ENNReal.ofReal b ≤ ‖u x‖ₑ} ≤
      ENNReal.ofReal ((A / b) ^ (p * c ^ n)) := by
    intro n
    have hq : 0 < p * c ^ n := mul_pos hp (pow_pos hcpos n)
    have hq0 : ENNReal.ofReal (p * c ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
    have hb0 : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.mpr hbpos).ne'
    have h := meas_ge_le_mul_pow_eLpNorm_enorm μ hq0 ENNReal.ofReal_ne_top
      (f := u) hb0 (by simp)
    rw [ENNReal.toReal_ofReal hq.le] at h
    calc
      μ {x | ENNReal.ofReal b ≤ ‖u x‖ₑ} ≤
          (ENNReal.ofReal b)⁻¹ ^ (p * c ^ n) *
            eLpNorm u (ENNReal.ofReal (p * c ^ n)) μ ^ (p * c ^ n) := h
      _ ≤ (ENNReal.ofReal b)⁻¹ ^ (p * c ^ n) *
            (ENNReal.ofReal A) ^ (p * c ^ n) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (hiter n) hq.le) _
      _ = ENNReal.ofReal ((A / b) ^ (p * c ^ n)) := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le, mul_comm,
          ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hbpos,
          ← ENNReal.ofReal_rpow_of_nonneg hratio0 hq.le]
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)) bot_le

/-- Uniform bounds for geometric powers imply the literal essential bound. -/
theorem c13_moser_powers_essential_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (p c A : ℝ) (hp : 0 < p) (hc : 1 < c) (hA : 0 ≤ A)
    (hiter : ∀ n : ℕ, eLpNorm u (ENNReal.ofReal (p*c^n)) μ ≤ ENNReal.ofReal A) :
    eLpNorm u ⊤ μ ≤ ENNReal.ofReal A := by
  rw [eLpNorm_exponent_top hu]
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hyt : y = ⊤
  · rw [hyt]; exact le_top
  have hyreal : A < y.toReal := by
    have := ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hyt |>.2 hy
    simpa only [ENNReal.toReal_ofReal hA] using this
  have hzero := c13_moser_superlevel_measure_zero μ u p c A y.toReal hp hc hA hyreal hiter
  rw [ENNReal.ofReal_toReal hyt] at hzero
  apply eLpNormEssSup_le_of_ae_enorm_bound
  rw [ae_iff]
  apply measure_mono_null _ hzero
  intro x hx
  exact le_of_lt (lt_of_not_ge hx)

/-- Select a future time at which an integrable energy is at most its
    average, while retaining an arbitrary almost-everywhere condition. -/
theorem c13_exists_future_energy_le_average (E : ℝ → ℝ) (P : ℝ → Prop)
    (hE : IntegrableOn E (Set.Ioo (1/4 : ℝ) (1/2)))
    (hP : ∀ᵐ s ∂volume.restrict (Set.Ioo (1/4 : ℝ) (1/2)), P s) :
    ∃ s ∈ Set.Ioo (1/4 : ℝ) (1/2), P s ∧
      E s ≤ 4 * ∫ q in Set.Ioo (1/4 : ℝ) (1/2), E q := by
  classical
  let I : Set ℝ := Set.Ioo (1/4 : ℝ) (1/2)
  let μ : Measure ℝ := volume.restrict I
  have hμ : μ ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    norm_num [μ, I, Real.volume_Ioo]
  have hgood : ∀ᵐ s ∂μ, s ∈ I ∧ P s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hP] with s hs hp
    exact ⟨hs, hp⟩
  have hnull : μ {s | ¬(s ∈ I ∧ P s)} = 0 := ae_iff.mp hgood
  obtain ⟨s, hs, hle⟩ := exists_notMem_null_le_average hμ hE hnull
  have hs' : s ∈ I ∧ P s := by simpa only [Set.mem_setOf_eq, not_not] using hs
  have havg : (⨍ q in I, E q) = 4 * ∫ q in I, E q := by
    rw [setAverage_eq]
    norm_num [I, Measure.real, Real.volume_Ioo]
  refine ⟨s, hs'.1, hs'.2, ?_⟩
  simpa only [μ, havg] using hle

/-- The continuous cutoff mass has a nonnegative representative at an early time. -/
theorem c13_positive_power_exists_early_nonnegative {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (E : ℝ → ℝ)
    (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) :
    ∃ t ∈ Set.Ioo (-1/2 : ℝ) (-1/4), 0 ≤ E t := by
  have hsub : Set.Ioo (-1/2 : ℝ) (-1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  letI : (ae (volume.restrict (Set.Ioo (-1/2 : ℝ) (-1/4)))).NeBot :=
    ae_restrict_neBot.mpr (by norm_num [Real.volume_Ioo])
  have hgood : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/2 : ℝ) (-1/4)),
      t ∈ Set.Ioo (-1/2 : ℝ) (-1/4) ∧ 0 ≤ E t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hrep,
      ae_restrict_of_ae_restrict_of_subset hsub hslices] with t ht hEt hpos
    refine ⟨ht, ?_⟩
    rw [hEt]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  exact hgood.exists



/-- Pointwise elliptic coercivity for the literal positive-power flux. -/
theorem c13_positive_power_flux_coercive {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v p : ℝ) (hv : 0 < v) (hp : 0 < p) (hp1 : p < 1)
    (g : Vec d) (chi : ℝ) (z : Vec d) :
    (κ * p * (1-p) / 2) * (chi ^ 2 * (Real.rpow v (p-2) * euclideanSq g)) ≤
      -(chi ^ 2 * (p * (p-1) * Real.rpow v (p-2)) * dot ((α x).mulVec g) g +
        2 * chi * (p * Real.rpow v (p-1)) * dot ((α x).mulVec g) z) +
      (2*p/(κ^3*(1-p))) * (Real.rpow v p * euclideanSq z) := by
  have hp1' : 0 < 1-p := by linarith
  have hpow : 0 ≤ Real.rpow v (p-2) := (Real.rpow_pos_of_pos hv _).le
  have he := ((hell.2.2 x).2.2.2 g).1
  change κ * euclideanSq g ≤ dot g ((α x).mulVec g) at he
  rw [show dot g ((α x).mulVec g) = dot ((α x).mulVec g) g by simp [dot, mul_comm]] at he
  have hm := c13_small_power_mixed_flux_bound hκ ρ α hell x v p hv hp hp1 g chi z
  have hm' := (le_abs_self _).trans hm
  have hc : 0 ≤ p * (1-p) / 2 * chi^2 * Real.rpow v (p-2) := by positivity
  have he' := mul_le_mul_of_nonneg_left he hc
  nlinarith only [he', hm']



/-- The literal positive power is integrable on the cylinder. -/
theorem c13_positive_power_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z) :
    Integrable (fun z => Real.rpow (u z) p)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  haveI : IsFiniteMeasure (volume.restrict (sourceBall (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top 0 R)
  haveI : IsFiniteMeasure μ := by
    have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict (sourceBall (0 : Vec d) R))) := inferInstance
    rwa [Measure.prod_restrict] at hf
  have hexp : ENNReal.ofReal p ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    linarith
  have hm : MemLp u (ENNReal.ofReal p) μ := hcal.1.mono_exponent hexp
  have hi := hm.integrable_norm_rpow'
  have hi' : Integrable (fun z => |u z| ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using hi
  apply hi'.congr
  filter_upwards [hu] with z hz
  rw [abs_of_pos (lt_of_lt_of_le hε hz)]
  rfl

/-- The weighted positive-power mass is integrable on the cylinder. -/
theorem c13_weighted_positive_power_integrable {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z) :
    Integrable (fun z => ρ z.2 * Real.rpow (u z) p)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hρ : MemLp (fun z : ℝ × Vec d => ρ z.2) ∞ μ := by
    apply memLp_top_of_bound (hell.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    filter_upwards with z
    change |ρ z.2| ≤ κ⁻¹
    rw [abs_of_nonneg (hκ.le.trans (hell.2.2 z.2).1)]
    exact (hell.2.2 z.2).2.1
  exact (c13_positive_power_integrable hε hp hp1 ρ α u G hcal hu).mul_of_top_right hρ


/-- The spatial cutoff error for the positive power is integrable. -/
theorem c13_positive_power_cutoff_error_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => Real.rpow (u z) p *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hpow := c13_positive_power_integrable hε hp hp1 ρ α u G hcal hu
  have hDtop (i : Fin d) : MemLp (fun z : ℝ × Vec d =>
      fderiv ℝ χ z.2 (unitVector i)) ∞ μ := by
    have hd : Continuous (fun x : Vec d => fderiv ℝ χ x (unitVector i)) :=
      (hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB, hb⟩ :=
      ((hχc.fderiv_apply ℝ (unitVector i)).isCompact_range hd).isBounded.exists_pos_norm_le
    apply memLp_top_of_bound (hd.comp continuous_snd).aestronglyMeasurable B
    exact ae_of_all μ (fun z => hb _ ⟨z.2, rfl⟩)
  have hs : Integrable (fun z : ℝ × Vec d => ∑ i : Fin d,
      Real.rpow (u z) p * (fderiv ℝ χ z.2 (unitVector i)) ^ 2) μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    have ht := hpow.mul_of_top_right ((hDtop i).mul (hDtop i))
    convert ht using 1 <;> ext z <;> simp only [Pi.mul_apply, pow_two] <;> ring
  simpa only [euclideanSq, dot, Finset.mul_sum, pow_two] using hs


/-- The literal positive-power cutoff mass is integrable. -/
theorem c13_positive_power_literal_mass_integrable {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) p)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hm := c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell u G hcal hu
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ∞ μ := by
    have ht : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using ht
  convert hm.mul_of_top_right hsq using 1 <;> ext z <;> simp only [Pi.mul_apply] <;> ring

/-- A bounded cutoff gradient is controlled by the weighted positive-power mass. -/
theorem c13_positive_power_cutoff_error_le_mass {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, Real.rpow (u z) p *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) ≤
    (L^2 * κ⁻¹) * (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  have he := c13_positive_power_cutoff_error_integrable hε hp hp1 ρ α u G hcal hu χ hχ hχc
  have hm := c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell u G hcal hu
  have hi := integral_mono_ae he (hm.const_mul (L^2 * κ⁻¹)) (by
    filter_upwards [hu] with z hz
    have hq : 0 ≤ Real.rpow (u z) p := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _
    have hρ : 1 ≤ κ⁻¹ * ρ z.2 := by
      have h := mul_le_mul_of_nonneg_left (hell.2.2 z.2).1 (inv_nonneg.mpr hκ.le)
      simpa only [inv_mul_cancel₀ (ne_of_gt hκ)] using h
    have hg : euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)) ≤ L^2 * (κ⁻¹ * ρ z.2) :=
      (hL z.2).trans (le_mul_of_one_le_right (sq_nonneg L) hρ)
    have ht := mul_le_mul_of_nonneg_left hg hq
    nlinarith)
  simpa only [integral_const_mul] using hi


theorem c13_positive_power_future_average_le_mass {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (E : ℝ → ℝ) (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) :
    IntegrableOn E (Set.Ioo (1/4 : ℝ) (1/2)) ∧
    (∫ t in Set.Ioo (1/4 : ℝ) (1/2), E t) ≤
      ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) p := by
  let I : Set ℝ := Set.Ioo (-1 : ℝ) 1
  let J : Set ℝ := Set.Ioo (1/4 : ℝ) (1/2)
  let U : Set (Vec d) := sourceBall 0 1
  let F : ℝ → ℝ := fun t => ∫ x in U, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p
  let Q : ℝ × Vec d → ℝ := fun z => ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) p
  let M : ℝ × Vec d → ℝ := fun z => ρ z.2 * Real.rpow (u z) p
  have hJI : J ⊆ I := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hQ : IntegrableOn Q (I ×ˢ U) :=
    c13_positive_power_literal_mass_integrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  have hM : IntegrableOn M (I ×ˢ U) :=
    c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell u G hcal hu
  have hQprod := hQ
  change Integrable Q ((volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U)) at hQprod
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hQprod
  have hF : IntegrableOn F I := hQprod.integral_prod_left
  have hrepJ : ∀ᵐ t ∂volume.restrict J, E t = F t :=
    ae_restrict_of_ae_restrict_of_subset hJI hrep
  refine ⟨(hF.mono_set hJI).congr (hrepJ.mono fun _ h => h.symm), ?_⟩
  have hu' := hu
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu'
  have hslices := Measure.ae_ae_of_ae_prod hu'
  have hFpos : ∀ᵐ t ∂volume.restrict I, 0 ≤ F t := by
    filter_upwards [hslices] with t ht
    apply integral_nonneg_of_ae
    filter_upwards [ht] with x hx
    exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)
  have hQle : ∀ᵐ z ∂volume.restrict (I ×ˢ U), Q z ≤ M z := by
    filter_upwards [hu] with z hz
    have hc : χ z.2 ^ 2 ≤ 1 := by nlinarith [hχ0 z.2, hχ1 z.2, sq_nonneg (χ z.2)]
    have hp' : 0 ≤ ρ z.2 * Real.rpow (u z) p :=
      mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
    have hh := mul_le_mul_of_nonneg_right hc hp'
    dsimp [Q, M]
    calc
      ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) p =
          χ z.2 ^ 2 * (ρ z.2 * Real.rpow (u z) p) := by ring
      _ ≤ 1 * (ρ z.2 * Real.rpow (u z) p) := hh
      _ = ρ z.2 * Real.rpow (u z) p := by ring
  have hprod : (volume.restrict I).prod (volume.restrict U) =
      (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U) := by
    rw [Measure.prod_restrict]
    rfl
  calc
    (∫ t in J, E t) = ∫ t in J, F t := integral_congr_ae hrepJ
    _ ≤ ∫ t in I, F t := integral_mono_measure (Measure.restrict_mono hJI le_rfl) hFpos hF
    _ = ∫ z in I ×ˢ U, Q z := by
      rw [← hprod]
      exact (integral_prod _ hQprod).symm
    _ ≤ ∫ z in I ×ˢ U, M z := integral_mono_ae hQ hM hQle




/-- Restricting the time interval cannot increase the weighted positive-power mass. -/
theorem c13_positive_power_mass_subinterval_le {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (J : Set ℝ) (hJ : J ⊆ Set.Ioo a b) :
    (∫ z in J ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) ≤
      ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p := by
  apply integral_mono_measure (Measure.restrict_mono (Set.prod_mono hJ (Set.Subset.rfl)) le_rfl)
  · filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  · exact c13_weighted_positive_power_integrable hκ hε hp hp1 ρ α hell u G hcal hu




/-- Positive-power gradient energy is integrable under the positive lower bound. -/
theorem c13_positive_power_gradient_integrable {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z) :
    Integrable (fun z => Real.rpow (u z) (p - 2) * euclideanSq (G z))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  have hc : Continuous (fun x : ℝ => Real.rpow (max ε x) (p - 2)) := by
    apply (continuous_const.max continuous_id).rpow_const
    intro x
    left
    exact ne_of_gt (lt_of_lt_of_le hε (le_max_left ε x))
  have hm : MemLp (fun z => Real.rpow (max ε (u z)) (p - 2)) ∞ μ := by
    apply memLp_top_of_bound (hc.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable)
      (Real.rpow ε (p - 2))
    filter_upwards with z
    have hn : 0 ≤ Real.rpow (max ε (u z)) (p - 2) :=
      Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε (le_max_left ε (u z)))) (p - 2)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact Real.rpow_le_rpow_of_nonpos hε (le_max_left ε (u z)) (by linarith)
  have hs : Integrable (fun z => euclideanSq (G z)) μ := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using hcal.2.2.1.integrable_sq
  have hi := hs.mul_of_top_left hm
  apply hi.congr
  filter_upwards [hu] with z hz
  simp only [Pi.mul_apply, max_eq_right hz, mul_comm]

end EinsteinFull.Calculus
