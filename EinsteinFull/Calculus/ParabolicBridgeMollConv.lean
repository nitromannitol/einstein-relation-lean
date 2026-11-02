import EinsteinFull.Calculus.ParabolicBridgeMollifier
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-!
# `L²` convergence of the time mollification
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ} {ε : ℝ} {hε : 0 < ε}

theorem Mol_measurable (F : Vec d × ℝ → ℝ) (hF : Measurable F) : Measurable (Mol ε hε F) := by
  have hf : Measurable fun p : (Vec d × ℝ) × ℝ => tmoll ε hε (p.1.2 - p.2) * F (p.1.1, p.2) :=
    (tmoll_continuous.measurable.comp (measurable_snd.comp measurable_fst |>.sub measurable_snd)).mul
      (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem eLpNorm_Mol_le (F : Vec d × ℝ → ℝ) (hF : Measurable F) :
    eLpNorm (Mol ε hε F) 2 volume ≤ eLpNorm F 2 volume := by
  have h := lintegral_enorm_Mol_sq_le (ε := ε) (hε := hε) F hF
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (Mol_measurable F hF).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- A.e. slices are `L²`. -/
theorem ae_slice_finite (F : Vec d × ℝ → ℝ) (hF : Measurable F)
    (h : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ≠ ⊤) : ∀ᵐ y : Vec d, ∫⁻ t : ℝ, ‖F (y, t)‖ₑ ^ (2 : ℝ) < ⊤ := by
  have hm : Measurable fun z : Vec d × ℝ => ‖F z‖ₑ ^ (2 : ℝ) := hF.enorm.pow_const _
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable] at h
  exact ae_lt_top (hm.lintegral_prod_right') h

theorem integrable_slice_mol (F : Vec d × ℝ → ℝ) (hF : Measurable F) (y : Vec d)
    (hy : ∫⁻ t : ℝ, ‖F (y, t)‖ₑ ^ (2 : ℝ) < ⊤) (t : ℝ) :
    Integrable (fun s => tmoll ε hε (t - s) * F (y, s)) volume := by
  have hFm : Measurable fun s => F (y, s) := hF.comp (measurable_const.prodMk measurable_id)
  have hF2 : MemLp (fun s => F (y, s)) 2 volume := by
    rw [memLp_two_iff_integrable_sq hFm.aestronglyMeasurable]
    refine ⟨(hFm.pow_const 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => ?_)) hy
    rw [enorm_pow, ENNReal.rpow_two]
  have hρ2 : MemLp (fun s => tmoll ε hε (t - s)) 2 volume :=
    Continuous.memLp_of_hasCompactSupport (μ := volume)
      (tmoll_continuous.comp (continuous_const.sub continuous_id))
      (tmoll_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft t))
  exact hρ2.integrable_mul hF2

/-- Linearity of the mollification, almost everywhere. -/
theorem Mol_sub_ae (F g : Vec d × ℝ → ℝ) (hF : Measurable F) (hg : Measurable g)
    (hFl : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ≠ ⊤) (hgl : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ≠ ⊤) :
    ∀ᵐ z : Vec d × ℝ, Mol ε hε (F - g) z = Mol ε hε F z - Mol ε hε g z := by
  have h1 := ae_slice_finite F hF hFl
  have h2 := ae_slice_finite g hg hgl
  have h3 : ∀ᵐ y : Vec d, (∫⁻ t : ℝ, ‖F (y, t)‖ₑ ^ (2 : ℝ) < ⊤) ∧
      ∫⁻ t : ℝ, ‖g (y, t)‖ₑ ^ (2 : ℝ) < ⊤ := h1.and h2
  have h4 : ∀ᵐ z : Vec d × ℝ, (∫⁻ t : ℝ, ‖F (z.1, t)‖ₑ ^ (2 : ℝ) < ⊤) ∧
      ∫⁻ t : ℝ, ‖g (z.1, t)‖ₑ ^ (2 : ℝ) < ⊤ := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_fst).ae h3
  filter_upwards [h4] with z hz
  have iF := integrable_slice_mol (ε := ε) (hε := hε) F hF z.1 hz.1 z.2
  have ig := integrable_slice_mol (ε := ε) (hε := hε) g hg z.1 hz.2 z.2
  unfold Mol
  rw [← integral_sub iF ig]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.sub_apply]
  ring

/-- Uniform convergence of the mollification of a compactly supported continuous function. -/
theorem Mol_sub_self_bound (g : Vec d × ℝ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ → ∀ z : Vec d × ℝ,
      |Mol ε hε g z - g z| ≤ η := by
  have huc := hc.uniformContinuous_of_continuous hg
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc η hη
  refine ⟨δ, hδ, fun ε hε hεδ z => ?_⟩
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hρint : Integrable (fun s => tmoll ε hε (z.2 - s)) volume :=
    tmoll_integrable.comp_sub_left z.2
  have hρ1 : ∫ s, tmoll ε hε (z.2 - s) = 1 := by
    rw [integral_sub_left_eq_self (fun s => tmoll ε hε s) volume z.2, tmoll_integral]
  have hgs : Continuous fun s => g (z.1, s) := hg.comp (continuous_const.prodMk continuous_id)
  have hint1 : Integrable (fun s => tmoll ε hε (z.2 - s) * g (z.1, s)) volume :=
    hρint.mul_bdd (c := B) hgs.aestronglyMeasurable (Filter.Eventually.of_forall fun s => hB _)
  have hint2 : Integrable (fun s => tmoll ε hε (z.2 - s) * g z) volume := hρint.mul_const _
  have hdiff : Mol ε hε g z - g z = ∫ s, tmoll ε hε (z.2 - s) * (g (z.1, s) - g z) := by
    have h : ∫ s, tmoll ε hε (z.2 - s) * (g (z.1, s) - g z) =
        (∫ s, tmoll ε hε (z.2 - s) * g (z.1, s)) - ∫ s, tmoll ε hε (z.2 - s) * g z := by
      rw [← integral_sub hint1 hint2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun s => by simp only; ring)
    rw [h, integral_mul_const, hρ1, one_mul]
    rfl
  rw [hdiff, ← Real.norm_eq_abs]
  have hbd : Integrable (fun s => tmoll ε hε (z.2 - s) * η) volume := hρint.mul_const _
  refine (norm_integral_le_of_norm_le hbd (Filter.Eventually.of_forall fun s => ?_)).trans ?_
  · rw [norm_mul, Real.norm_of_nonneg (tmoll_nonneg _)]
    by_cases h0 : tmoll ε hε (z.2 - s) = 0
    · rw [h0]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (tmoll_nonneg _)
      have hs : |z.2 - s| < ε := by
        by_contra hnot
        exact h0 (tmoll_eq_zero (not_lt.mp hnot))
      have hdist : dist (z.1, s) z < δ := by
        have e : dist (z.1, s) z = |z.2 - s| := by
          rw [Prod.dist_eq]
          simp [Real.dist_eq, abs_sub_comm]
        rw [e]
        linarith
      have h1 := hδ' hdist
      simpa [Real.dist_eq, Real.norm_eq_abs] using h1.le
  · rw [integral_mul_const, hρ1, one_mul]

/-- Outside a product set, the mollification of a function supported there vanishes. -/
theorem Mol_eq_zero_of_not_mem (g : Vec d × ℝ → ℝ) (A : Set (Vec d)) (R : ℝ)
    (hsupp : ∀ x, g x ≠ 0 → x.1 ∈ A ∧ |x.2| ≤ R) (hε1 : ε ≤ 1) (z : Vec d × ℝ)
    (hz : ¬ (z.1 ∈ A ∧ |z.2| ≤ R + 1)) : Mol ε hε g z = 0 := by
  unfold Mol
  have h : (fun t => tmoll ε hε (z.2 - t) * g (z.1, t)) = fun _ => 0 := by
    funext t
    by_cases h0 : g (z.1, t) = 0
    · rw [h0, mul_zero]
    · by_cases hρ : tmoll ε hε (z.2 - t) = 0
      · rw [hρ, zero_mul]
      · exfalso
        have hs : |z.2 - t| < ε := by
          by_contra hnot
          exact hρ (tmoll_eq_zero (not_lt.mp hnot))
        obtain ⟨h1, h2⟩ := hsupp _ h0
        refine hz ⟨h1, ?_⟩
        have : |z.2| ≤ |z.2 - t| + |t| := by
          have := abs_add_le (z.2 - t) t
          simpa using this
        simp only at h2
        linarith
  rw [h]
  simp

/-- The mollification of a compactly supported continuous function converges in `L²`. -/
theorem eLpNorm_Mol_sub_self_le (g : Vec d × ℝ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      eLpNorm (Mol ε hε g - g) 2 volume ≤ ENNReal.ofReal δ := by
  have hKc : IsCompact (tsupport g) := hc
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ tsupport g, ‖x.2‖ ≤ R :=
    hKc.exists_bound_of_continuousOn (f := fun x : Vec d × ℝ => x.2) continuous_snd.continuousOn
  have hA : IsCompact (Prod.fst '' tsupport g) := hKc.image continuous_fst
  have hK' : IsCompact ((Prod.fst '' tsupport g) ×ˢ Set.Icc (-(R + 1)) (R + 1)) :=
    hA.prod isCompact_Icc
  have hV : volume ((Prod.fst '' tsupport g) ×ˢ Set.Icc (-(R + 1)) (R + 1)) < ⊤ :=
    hK'.measure_lt_top
  have hsupp : ∀ x, g x ≠ 0 → x.1 ∈ Prod.fst '' tsupport g ∧ |x.2| ≤ R := by
    intro x hx
    have hx' : x ∈ tsupport g := subset_tsupport g hx
    exact ⟨⟨x, hx', rfl⟩, by simpa using hR x hx'⟩
  set W : ℝ≥0∞ := volume ((Prod.fst '' tsupport g) ×ˢ Set.Icc (-(R + 1)) (R + 1)) ^
    (1 / (2 : ℝ≥0∞).toReal) with hW
  have hWtop : W ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hV.ne
  set w : ℝ := W.toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hη : 0 < δ / (w + 1) := by positivity
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Mol_sub_self_bound g hg hc hη
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, fun ε hε hεε => ?_⟩
  have hεa : ε < ε₁ := lt_of_lt_of_le hεε (min_le_left _ _)
  have hεb : ε ≤ 1 := (lt_of_lt_of_le hεε (min_le_right _ _)).le
  have hmeas : AEStronglyMeasurable (Mol ε hε g - g) volume :=
    ((Mol_measurable g hg.measurable).sub hg.measurable).aestronglyMeasurable
  have hbound := eLpNorm_sub_le_of_dist_bdd (p := 2)
    (s := (Prod.fst '' tsupport g) ×ˢ Set.Icc (-(R + 1)) (R + 1)) volume (by simp)
    hK'.measurableSet.nullMeasurableSet hη.le hmeas
    (fun x => by
      rw [Real.dist_eq]
      exact hε₁' ε hε hεa x)
    (fun x hx => by
      by_contra hxK
      refine hx ?_
      refine Mol_eq_zero_of_not_mem g _ R hsupp hεb x ?_
      intro h
      refine hxK ⟨h.1, ?_⟩
      exact abs_le.mp h.2 |> fun h' => ⟨by linarith [h'.1], h'.2⟩)
    (fun x hx => by
      have := hsupp x hx
      exact ⟨this.1, abs_le.mp (this.2.trans (by linarith)) |> fun h' =>
        ⟨by linarith [h'.1], by linarith [h'.2]⟩⟩)
  refine hbound.trans ?_
  have hWeq : volume ((Prod.fst '' tsupport g) ×ˢ Set.Icc (-(R + 1)) (R + 1)) ^
      (1 / (2 : ℝ≥0∞).toReal) = ENNReal.ofReal w := by
    rw [hw, ENNReal.ofReal_toReal hWtop]
  rw [hWeq, ← ENNReal.ofReal_mul hη.le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- `L²` membership in terms of the lintegral of the squared norm. -/
theorem eLpNorm_two_lt_top_iff {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ < ⊤ ↔ ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  constructor
  · intro h htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact lt_irrefl _ h
  · intro h
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h

/-- `L²` convergence of the time mollification. -/
theorem Mol_L2_converges (F : Vec d × ℝ → ℝ) (hF : Measurable F)
    (hFl : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      eLpNorm (Mol ε hε F - F) 2 volume ≤ ENNReal.ofReal δ := by
  have hF2 : MemLp F 2 volume := (eLpNorm_two_lt_top_iff hF.aestronglyMeasurable).mpr hFl
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨g, hgc, hFg, hgcont, hgmem⟩ := hF2.exists_hasCompactSupport_eLpNorm_sub_le
    (by simp : (2 : ℝ≥0∞) ≠ ∞) (ε := ENNReal.ofReal (δ / 3))
    (ENNReal.ofReal_pos.mpr hδ3).ne'
  have hgm : Measurable g := hgcont.measurable
  have hgl : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ≠ ⊤ :=
    (eLpNorm_two_lt_top_iff hgm.aestronglyMeasurable).mp hgmem
  have hFgm : Measurable (F - g) := hF.sub hgm
  obtain ⟨ε₀, hε₀, hε₀'⟩ := eLpNorm_Mol_sub_self_le g hgcont hgc hδ3
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have hsub : eLpNorm (Mol ε hε F - F) 2 volume =
      eLpNorm (Mol ε hε (F - g) + (Mol ε hε g - g) - (F - g)) 2 volume := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Mol_sub_ae (ε := ε) (hε := hε) F g hF hgm hFl hgl] with z hz
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [hz]
    ring
  have ha : eLpNorm (Mol ε hε (F - g)) 2 volume ≤ ENNReal.ofReal (δ / 3) :=
    (eLpNorm_Mol_le (ε := ε) (hε := hε) (F - g) hFgm).trans hFg
  have hb := hε₀' ε hε hεε₀
  calc eLpNorm (Mol ε hε F - F) 2 volume
      = eLpNorm (Mol ε hε (F - g) + (Mol ε hε g - g) - (F - g)) 2 volume := hsub
    _ ≤ eLpNorm (Mol ε hε (F - g) + (Mol ε hε g - g)) 2 volume + eLpNorm (F - g) 2 volume :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ (eLpNorm (Mol ε hε (F - g)) 2 volume + eLpNorm (Mol ε hε g - g) 2 volume) +
          eLpNorm (F - g) 2 volume :=
        add_le_add_left (eLpNorm_add_le (by norm_num)) _
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) :=
        add_le_add (add_le_add ha hb) hFg
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add hδ3.le hδ3.le, ← ENNReal.ofReal_add (by positivity) hδ3.le]
        congr 1
        ring

end EinsteinFull.ParabolicBridge
