import EinsteinFull.External.Draft.DFGWInvarianceV2
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# J1 convergence towards continuous paths

J1 convergence (`SkorokhodTendsto`, Billingsley 1999, Theorem 16.1) to a continuous limit is
locally uniform convergence, and a J1 limit of continuous paths is continuous.
-/

open Filter Topology EinsteinRelation MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.Draft

variable {d : ℕ}

/-- J1 convergence to a continuous path is uniform convergence on every bounded interval. -/
theorem SkorokhodTendsto.tendstoUniformlyOn_Iic {x : ℕ → CadlagPath d} {γ : Path d}
    (h : SkorokhodTendsto x (Path.toCadlag γ)) (T : ℝ≥0) :
    TendstoUniformlyOn (fun n t => (x n).toFun t) γ atTop (Set.Iic T) := by
  obtain ⟨lam, hlam, hx⟩ := h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huc : UniformContinuousOn γ (Set.Icc 0 (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous γ.continuous.continuousOn
  obtain ⟨δ, hδ, hδγ⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  have hδ1 : 0 < min δ 1 := lt_min hδ one_pos
  filter_upwards [hlam (min δ 1 / 2) (half_pos hδ1), hx (T + 1) (ε / 2) (half_pos hε)]
    with n hn hxn t ht
  set s := (lam n).symm t with hs
  have hls : lam n s = t := by simp [hs]
  have hst : |((s : ℝ≥0) : ℝ) - t| ≤ min δ 1 / 2 := by
    have := hn s
    rw [hls] at this
    rwa [abs_sub_comm] at this
  have hsT : s ≤ T + 1 := by
    have h1 : (s : ℝ) ≤ t + min δ 1 / 2 := by linarith [(abs_le.1 hst).2]
    have h2 : (t : ℝ) ≤ T := ht
    have : (s : ℝ) ≤ T + 1 := by linarith [min_le_right δ 1]
    exact_mod_cast this
  have h1 : ‖(x n).toFun t - (Path.toCadlag γ).toFun s‖ ≤ ε / 2 := by
    rw [← hls]
    exact hxn s hsT
  have h2 : dist (γ s) (γ t) < ε / 2 := by
    refine hδγ s ⟨bot_le, hsT⟩ t ⟨bot_le, le_trans ht le_self_add⟩ ?_
    rw [NNReal.dist_eq]
    exact lt_of_le_of_lt hst (by linarith [min_le_left δ 1])
  rw [dist_comm, dist_eq_norm]
  calc ‖(x n).toFun t - γ t‖ ≤ ‖(x n).toFun t - γ s‖ + ‖γ s - γ t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt h1 (by rwa [← dist_eq_norm])
    _ = ε := add_halves ε

/-- A J1 limit of continuous paths is continuous: continuous paths form a J1-closed set. -/
theorem continuous_of_skorokhodTendsto {γ : ℕ → Path d} {y : CadlagPath d}
    (h : SkorokhodTendsto (fun n => Path.toCadlag (γ n)) y) : Continuous y.toFun := by
  obtain ⟨lam, -, hx⟩ := h
  have hcont : ∀ T : ℝ≥0, ContinuousOn y.toFun (Set.Iic T) := by
    intro T
    have hu : TendstoUniformlyOn (fun n t => γ n (lam n t)) y.toFun atTop (Set.Iic T) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hx T (ε / 2) (half_pos hε)] with n hn t ht
      rw [dist_comm, dist_eq_norm]
      exact lt_of_le_of_lt (hn t ht) (half_lt_self hε)
    refine hu.continuousOn (Frequently.of_forall fun n => ?_)
    exact ((γ n).continuous.comp (lam n).continuous).continuousOn
  refine continuous_iff_continuousAt.2 fun t => ?_
  refine (hcont (t + 1)).continuousAt (Iic_mem_nhds ?_)
  exact lt_add_of_pos_right t one_pos

/-! ### A J1 pre-distance -/

/-- The capped displacement of a time change. -/
noncomputable def tcDev (lam : ℝ≥0 ≃o ℝ≥0) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ENNReal.ofReal (min 1 |((lam t : ℝ≥0) : ℝ) - t|)

/-- The weighted capped gap between `x ∘ λ` and `y`. -/
noncomputable def tcGap (x : CadlagPath d) (lam : ℝ≥0 ≃o ℝ≥0) (y : CadlagPath d) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, ENNReal.ofReal (Real.exp (-(t : ℝ)) * min 1 ‖x.toFun (lam t) - y.toFun t‖)

/-- The J1 pre-distance: the best time change, in the sup of displacement and weighted gap. -/
noncomputable def skorPre (x y : CadlagPath d) : ℝ≥0∞ :=
  ⨅ lam : ℝ≥0 ≃o ℝ≥0, max (tcDev lam) (tcGap x lam y)

theorem skorPre_self (x : CadlagPath d) : skorPre x x = 0 := by
  refine le_antisymm ((iInf_le _ (OrderIso.refl ℝ≥0)).trans ?_) bot_le
  simp [tcDev, tcGap]

theorem tcDev_le_one (lam : ℝ≥0 ≃o ℝ≥0) : tcDev lam ≤ 1 :=
  iSup_le fun _ => ENNReal.ofReal_le_one.2 (min_le_left _ _)

theorem tcGap_le_one (x : CadlagPath d) (lam : ℝ≥0 ≃o ℝ≥0) (y : CadlagPath d) :
    tcGap x lam y ≤ 1 :=
  iSup_le fun t => ENNReal.ofReal_le_one.2 (mul_le_one₀ (Real.exp_le_one_iff.2 (by simp))
    (le_min zero_le_one (norm_nonneg _)) (min_le_left _ _))

theorem skorPre_le_one (x y : CadlagPath d) : skorPre x y ≤ 1 :=
  (iInf_le _ (OrderIso.refl ℝ≥0)).trans (max_le (tcDev_le_one _) (tcGap_le_one _ _ _))

/-- Conversely, if the pre-distance tends to zero then the paths converge in J1. -/
theorem skorokhodTendsto_of_tendsto_skorPre {x : ℕ → CadlagPath d} {y : CadlagPath d}
    (h : Tendsto (fun n => skorPre (x n) y) atTop (𝓝 0)) : SkorokhodTendsto x y := by
  have hex : ∀ n : ℕ, ∃ lam : ℝ≥0 ≃o ℝ≥0,
      max (tcDev lam) (tcGap (x n) lam y) < skorPre (x n) y + ((n : ℝ≥0∞) + 1)⁻¹ := fun n => by
    have hlt : skorPre (x n) y < skorPre (x n) y + ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.lt_add_right ((skorPre_le_one _ _).trans_lt ENNReal.one_lt_top).ne
        (ENNReal.inv_ne_zero.2 (by simp))
    exact iInf_lt_iff.1 hlt
  choose lam hlam using hex
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
  have hto : Tendsto (fun n => skorPre (x n) y + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using h.add hinv
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      tcDev (lam n) ≤ ENNReal.ofReal δ ∧ tcGap (x n) (lam n) y ≤ ENNReal.ofReal δ := by
    intro δ hδ
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hto) (ENNReal.ofReal δ)
      (ENNReal.ofReal_pos.2 hδ)] with n hn
    exact ⟨((le_max_left _ _).trans (hlam n).le).trans hn,
      ((le_max_right _ _).trans (hlam n).le).trans hn⟩
  refine ⟨lam, fun ε hε => ?_, fun T ε hε => ?_⟩
  · filter_upwards [hsmall (min ε (1 / 2)) (lt_min hε one_half_pos)] with n hn t
    have h1 : min 1 |((lam n t : ℝ≥0) : ℝ) - t| ≤ min ε (1 / 2) :=
      (ENNReal.ofReal_le_ofReal_iff (le_min hε.le one_half_pos.le)).1
        ((le_iSup (fun t : ℝ≥0 => ENNReal.ofReal (min 1 |((lam n t : ℝ≥0) : ℝ) - t|)) t).trans hn.1)
    have h2 : |((lam n t : ℝ≥0) : ℝ) - t| ≤ min ε (1 / 2) := by
      rcases min_cases (1 : ℝ) |((lam n t : ℝ≥0) : ℝ) - t| with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm] at h1
        linarith [min_le_right ε (1 / 2 : ℝ)]
      · rwa [hm] at h1
    exact h2.trans (min_le_left _ _)
  · have heT : 0 < Real.exp (-(T : ℝ)) := Real.exp_pos _
    filter_upwards [hsmall (min ε (1 / 2) * Real.exp (-(T : ℝ)))
      (mul_pos (lt_min hε one_half_pos) heT)] with n hn t ht
    have h1 : Real.exp (-(t : ℝ)) * min 1 ‖(x n).toFun (lam n t) - y.toFun t‖ ≤
        min ε (1 / 2) * Real.exp (-(T : ℝ)) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_min hε.le one_half_pos.le) heT.le)).1
        ((le_iSup (fun t : ℝ≥0 => ENNReal.ofReal (Real.exp (-(t : ℝ)) *
          min 1 ‖(x n).toFun (lam n t) - y.toFun t‖)) t).trans hn.2)
    have hexp : Real.exp (-(T : ℝ)) ≤ Real.exp (-(t : ℝ)) :=
      Real.exp_le_exp.2 (by have : (t : ℝ) ≤ T := ht; linarith)
    have h2 : min 1 ‖(x n).toFun (lam n t) - y.toFun t‖ ≤ min ε (1 / 2) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc (Real.exp_pos (-(t : ℝ)))
      nlinarith [mul_le_mul_of_nonneg_left hexp (le_min hε.le one_half_pos.le)]
    rcases min_cases (1 : ℝ) ‖(x n).toFun (lam n t) - y.toFun t‖ with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm] at h2
      linarith [min_le_right ε (1 / 2 : ℝ)]
    · rw [hm] at h2
      exact h2.trans (min_le_left _ _)

theorem min_one_abs_add_le (a b : ℝ) : min 1 |a + b| ≤ min 1 |a| + min 1 |b| := by
  rcases le_total 1 |a| with ha | ha
  · rw [min_eq_left ha]
    linarith [min_le_left (1 : ℝ) |a + b|, le_min zero_le_one (abs_nonneg b)]
  rcases le_total 1 |b| with hb | hb
  · rw [min_eq_left hb]
    linarith [min_le_left (1 : ℝ) |a + b|, le_min zero_le_one (abs_nonneg a)]
  rw [min_eq_right ha, min_eq_right hb]
  exact (min_le_right _ _).trans (abs_add_le a b)

theorem min_one_norm_add_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    min 1 ‖a + b‖ ≤ min 1 ‖a‖ + min 1 ‖b‖ := by
  rcases le_total 1 ‖a‖ with ha | ha
  · rw [min_eq_left ha]
    linarith [min_le_left (1 : ℝ) ‖a + b‖, le_min zero_le_one (norm_nonneg b)]
  rcases le_total 1 ‖b‖ with hb | hb
  · rw [min_eq_left hb]
    linarith [min_le_left (1 : ℝ) ‖a + b‖, le_min zero_le_one (norm_nonneg a)]
  rw [min_eq_right ha, min_eq_right hb]
  exact (min_le_right _ _).trans (norm_add_le a b)

/-- Displacements add under composition of time changes. -/
theorem tcDev_trans (lam₁ lam₂ : ℝ≥0 ≃o ℝ≥0) :
    tcDev (lam₂.trans lam₁) ≤ tcDev lam₁ + tcDev lam₂ := by
  refine iSup_le fun t => ?_
  have h := min_one_abs_add_le (((lam₁ (lam₂ t) : ℝ≥0) : ℝ) - (lam₂ t : ℝ≥0))
    (((lam₂ t : ℝ≥0) : ℝ) - t)
  rw [sub_add_sub_cancel] at h
  calc ENNReal.ofReal (min 1 |((lam₂.trans lam₁ t : ℝ≥0) : ℝ) - t|)
      ≤ ENNReal.ofReal (min 1 |((lam₁ (lam₂ t) : ℝ≥0) : ℝ) - (lam₂ t : ℝ≥0)|) +
        ENNReal.ofReal (min 1 |((lam₂ t : ℝ≥0) : ℝ) - t|) := by
        rw [← ENNReal.ofReal_add (le_min zero_le_one (abs_nonneg _))
          (le_min zero_le_one (abs_nonneg _))]
        exact ENNReal.ofReal_le_ofReal h
    _ ≤ tcDev lam₁ + tcDev lam₂ := add_le_add
        (le_iSup (fun s : ℝ≥0 => ENNReal.ofReal (min 1 |((lam₁ s : ℝ≥0) : ℝ) - s|)) (lam₂ t))
        (le_iSup (fun s : ℝ≥0 => ENNReal.ofReal (min 1 |((lam₂ s : ℝ≥0) : ℝ) - s|)) t)

theorem abs_sub_lt_one_of_tcDev_lt_one {lam : ℝ≥0 ≃o ℝ≥0} (h : tcDev lam < 1) (t : ℝ≥0) :
    |((lam t : ℝ≥0) : ℝ) - t| < 1 := by
  have h1 : ENNReal.ofReal (min 1 |((lam t : ℝ≥0) : ℝ) - t|) < 1 :=
    (le_iSup (fun s : ℝ≥0 => ENNReal.ofReal (min 1 |((lam s : ℝ≥0) : ℝ) - s|)) t).trans_lt h
  rw [ENNReal.ofReal_lt_one] at h1
  rcases min_cases (1 : ℝ) |((lam t : ℝ≥0) : ℝ) - t| with ⟨hm, -⟩ | ⟨hm, hlt⟩
  · rw [hm] at h1
    exact absurd h1 (lt_irrefl 1)
  · rwa [hm] at h1

/-- Gaps compose, with the weight changing by at most `e` under a time change moving points by
less than one. -/
theorem tcGap_trans (x y z : CadlagPath d) (lam₁ lam₂ : ℝ≥0 ≃o ℝ≥0) (h₂ : tcDev lam₂ < 1) :
    tcGap x (lam₂.trans lam₁) z ≤
      ENNReal.ofReal (Real.exp 1) * tcGap x lam₁ y + tcGap y lam₂ z := by
  refine iSup_le fun t => ?_
  have hw : Real.exp (-(t : ℝ)) ≤ Real.exp 1 * Real.exp (-((lam₂ t : ℝ≥0) : ℝ)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    linarith [(abs_lt.1 (abs_sub_lt_one_of_tcDev_lt_one h₂ t)).2]
  have hm := min_one_norm_add_le (x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t))
    (y.toFun (lam₂ t) - z.toFun t)
  rw [sub_add_sub_cancel] at hm
  have hpt : Real.exp (-(t : ℝ)) * min 1 ‖x.toFun (lam₁ (lam₂ t)) - z.toFun t‖ ≤
      Real.exp 1 * (Real.exp (-((lam₂ t : ℝ≥0) : ℝ)) *
        min 1 ‖x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t)‖) +
      Real.exp (-(t : ℝ)) * min 1 ‖y.toFun (lam₂ t) - z.toFun t‖ := by
    have h0 : 0 ≤ min 1 ‖x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t)‖ :=
      le_min zero_le_one (norm_nonneg _)
    calc Real.exp (-(t : ℝ)) * min 1 ‖x.toFun (lam₁ (lam₂ t)) - z.toFun t‖
        ≤ Real.exp (-(t : ℝ)) * (min 1 ‖x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t)‖ +
            min 1 ‖y.toFun (lam₂ t) - z.toFun t‖) :=
          mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ ≤ _ := by
          rw [mul_add]
          refine add_le_add ?_ le_rfl
          calc Real.exp (-(t : ℝ)) * min 1 ‖x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t)‖
              ≤ (Real.exp 1 * Real.exp (-((lam₂ t : ℝ≥0) : ℝ))) *
                  min 1 ‖x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t)‖ :=
                mul_le_mul_of_nonneg_right hw h0
            _ = _ := by ring
  calc ENNReal.ofReal (Real.exp (-(t : ℝ)) *
        min 1 ‖x.toFun ((lam₂.trans lam₁) t) - z.toFun t‖)
      ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-((lam₂ t : ℝ≥0) : ℝ)) *
          min 1 ‖x.toFun (lam₁ (lam₂ t)) - y.toFun (lam₂ t)‖) +
        ENNReal.ofReal (Real.exp (-(t : ℝ)) * min 1 ‖y.toFun (lam₂ t) - z.toFun t‖) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_add
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le
            (le_min zero_le_one (norm_nonneg _))))
          (mul_nonneg (Real.exp_pos _).le (le_min zero_le_one (norm_nonneg _)))]
        exact ENNReal.ofReal_le_ofReal hpt
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (le_iSup (fun s : ℝ≥0 => ENNReal.ofReal
          (Real.exp (-(s : ℝ)) * min 1 ‖x.toFun (lam₁ s) - y.toFun s‖)) (lam₂ t)))
        (le_iSup (fun s : ℝ≥0 => ENNReal.ofReal
          (Real.exp (-(s : ℝ)) * min 1 ‖y.toFun (lam₂ s) - z.toFun s‖)) t)

/-- The quasi-triangle inequality, with constant `e + 1`. -/
theorem skorPre_triangle (x y z : CadlagPath d) :
    skorPre x z ≤ ENNReal.ofReal (Real.exp 1 + 1) * max (skorPre x y) (skorPre y z) := by
  set C := ENNReal.ofReal (Real.exp 1 + 1) with hCdef
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.2 zero_le_one
  have hC1 : 1 ≤ C := by
    rw [hCdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hC2 : 2 ≤ C := by
    rw [hCdef, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have key : ∀ lam₁ lam₂ : ℝ≥0 ≃o ℝ≥0, skorPre x z ≤
      C * max (max (tcDev lam₁) (tcGap x lam₁ y)) (max (tcDev lam₂) (tcGap y lam₂ z)) := by
    intro lam₁ lam₂
    set M := max (max (tcDev lam₁) (tcGap x lam₁ y)) (max (tcDev lam₂) (tcGap y lam₂ z))
    have h1 : tcDev lam₁ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
    have h2 : tcGap x lam₁ y ≤ M := (le_max_right _ _).trans (le_max_left _ _)
    have h3 : tcDev lam₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have h4 : tcGap y lam₂ z ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    by_cases hd : tcDev lam₂ < 1
    · refine (iInf_le _ (lam₂.trans lam₁)).trans (max_le ?_ ?_)
      · calc tcDev (lam₂.trans lam₁) ≤ tcDev lam₁ + tcDev lam₂ := tcDev_trans _ _
          _ ≤ M + M := add_le_add h1 h3
          _ = 2 * M := (two_mul M).symm
          _ ≤ C * M := mul_le_mul' hC2 le_rfl
      · calc tcGap x (lam₂.trans lam₁) z
            ≤ ENNReal.ofReal (Real.exp 1) * tcGap x lam₁ y + tcGap y lam₂ z :=
              tcGap_trans x y z lam₁ lam₂ hd
          _ ≤ ENNReal.ofReal (Real.exp 1) * M + 1 * M := add_le_add (mul_le_mul' le_rfl h2)
              (by rw [one_mul]; exact h4)
          _ = C * M := by
              rw [← add_mul, hCdef, ENNReal.ofReal_add (Real.exp_pos 1).le zero_le_one,
                ENNReal.ofReal_one]
    · push_neg at hd
      calc skorPre x z ≤ 1 := skorPre_le_one x z
        _ ≤ M := hd.trans h3
        _ ≤ C * M := le_mul_of_one_le_left bot_le hC1
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := (ε : ℝ) / (Real.exp 1 + 1)
  have hδ : 0 < δ := div_pos (by exact_mod_cast hε) (by linarith)
  have hCδ : C * ENNReal.ofReal δ = ε := by
    rw [hCdef, ← ENNReal.ofReal_mul (by linarith), mul_div_cancel₀ _ (by linarith),
      ENNReal.ofReal_coe_nnreal]
  have hA : skorPre x y < skorPre x y + ENNReal.ofReal δ :=
    ENNReal.lt_add_right ((skorPre_le_one _ _).trans_lt ENNReal.one_lt_top).ne
      (ENNReal.ofReal_pos.2 hδ).ne'
  have hB : skorPre y z < skorPre y z + ENNReal.ofReal δ :=
    ENNReal.lt_add_right ((skorPre_le_one _ _).trans_lt ENNReal.one_lt_top).ne
      (ENNReal.ofReal_pos.2 hδ).ne'
  obtain ⟨lam₁, hl₁⟩ := iInf_lt_iff.1 hA
  obtain ⟨lam₂, hl₂⟩ := iInf_lt_iff.1 hB
  calc skorPre x z ≤ C * max (max (tcDev lam₁) (tcGap x lam₁ y))
        (max (tcDev lam₂) (tcGap y lam₂ z)) := key lam₁ lam₂
    _ ≤ C * (max (skorPre x y) (skorPre y z) + ENNReal.ofReal δ) := by
        refine mul_le_mul' le_rfl (max_le (hl₁.le.trans ?_) (hl₂.le.trans ?_))
        · exact add_le_add (le_max_left _ _) le_rfl
        · exact add_le_add (le_max_right _ _) le_rfl
    _ = C * max (skorPre x y) (skorPre y z) + ε := by rw [mul_add, hCδ]

theorem tcDev_symm (lam : ℝ≥0 ≃o ℝ≥0) : tcDev lam.symm ≤ tcDev lam := by
  refine iSup_le fun t => ?_
  have h := le_iSup (fun s : ℝ≥0 => ENNReal.ofReal (min 1 |((lam s : ℝ≥0) : ℝ) - s|))
    (lam.symm t)
  simp only [OrderIso.apply_symm_apply] at h
  rwa [abs_sub_comm] at h

theorem tcGap_symm (x y : CadlagPath d) {lam : ℝ≥0 ≃o ℝ≥0} (hd : tcDev lam < 1) :
    tcGap y lam.symm x ≤ ENNReal.ofReal (Real.exp 1) * tcGap x lam y := by
  refine iSup_le fun t => ?_
  set s := lam.symm t
  have hs : lam s = t := lam.apply_symm_apply t
  have hw : Real.exp (-((lam s : ℝ≥0) : ℝ)) ≤ Real.exp 1 * Real.exp (-(s : ℝ)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    linarith [(abs_lt.1 (abs_sub_lt_one_of_tcDev_lt_one hd s)).1]
  have h0 : 0 ≤ min 1 ‖x.toFun (lam s) - y.toFun s‖ := le_min zero_le_one (norm_nonneg _)
  calc ENNReal.ofReal (Real.exp (-(t : ℝ)) * min 1 ‖y.toFun (lam.symm t) - x.toFun t‖)
      = ENNReal.ofReal (Real.exp (-((lam s : ℝ≥0) : ℝ)) * min 1 ‖x.toFun (lam s) - y.toFun s‖) := by
        rw [hs, norm_sub_rev]
    _ ≤ ENNReal.ofReal (Real.exp 1 * (Real.exp (-(s : ℝ)) *
          min 1 ‖x.toFun (lam s) - y.toFun s‖)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc Real.exp (-((lam s : ℝ≥0) : ℝ)) * min 1 ‖x.toFun (lam s) - y.toFun s‖
            ≤ (Real.exp 1 * Real.exp (-(s : ℝ))) * min 1 ‖x.toFun (lam s) - y.toFun s‖ :=
              mul_le_mul_of_nonneg_right hw h0
          _ = _ := by ring
    _ ≤ _ := by
        rw [ENNReal.ofReal_mul (Real.exp_pos 1).le]
        exact mul_le_mul' le_rfl (le_iSup (fun s : ℝ≥0 => ENNReal.ofReal
          (Real.exp (-(s : ℝ)) * min 1 ‖x.toFun (lam s) - y.toFun s‖)) s)

/-- The pre-distance is symmetric up to the factor `e`. -/
theorem skorPre_symm_le (x y : CadlagPath d) :
    skorPre y x ≤ ENNReal.ofReal (Real.exp 1) * skorPre x y := by
  set c := ENNReal.ofReal (Real.exp 1)
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.2 zero_le_one
  have hc1 : 1 ≤ c := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal he1
  have key : ∀ lam : ℝ≥0 ≃o ℝ≥0, skorPre y x ≤ c * max (tcDev lam) (tcGap x lam y) := by
    intro lam
    by_cases hd : tcDev lam < 1
    · refine (iInf_le _ lam.symm).trans (max_le ?_ ?_)
      · exact (tcDev_symm lam).trans ((le_max_left _ _).trans (le_mul_of_one_le_left bot_le hc1))
      · exact (tcGap_symm x y hd).trans (mul_le_mul' le_rfl (le_max_right _ _))
    · push_neg at hd
      exact (skorPre_le_one y x).trans ((hd.trans (le_max_left _ _)).trans
        (le_mul_of_one_le_left bot_le hc1))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set δ : ℝ := (ε : ℝ) / Real.exp 1
  have hδ : 0 < δ := div_pos (by exact_mod_cast hε) (Real.exp_pos 1)
  have hcδ : c * ENNReal.ofReal δ = ε := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos 1).le, mul_div_cancel₀ _ (Real.exp_pos 1).ne',
      ENNReal.ofReal_coe_nnreal]
  have hA : skorPre x y < skorPre x y + ENNReal.ofReal δ :=
    ENNReal.lt_add_right ((skorPre_le_one _ _).trans_lt ENNReal.one_lt_top).ne
      (ENNReal.ofReal_pos.2 hδ).ne'
  obtain ⟨lam, hl⟩ := iInf_lt_iff.1 hA
  calc skorPre y x ≤ c * max (tcDev lam) (tcGap x lam y) := key lam
    _ ≤ c * (skorPre x y + ENNReal.ofReal δ) := mul_le_mul' le_rfl hl.le
    _ = c * skorPre x y + ε := by rw [mul_add, hcδ]

/-- J1 convergence drives the pre-distance to zero. -/
theorem SkorokhodTendsto.tendsto_skorPre {x : ℕ → CadlagPath d} {y : CadlagPath d}
    (h : SkorokhodTendsto x y) : Tendsto (fun n => skorPre (x n) y) atTop (𝓝 0) := by
  obtain ⟨lam, hlam, hx⟩ := h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hε'
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hε', ?_⟩
      rw [ENNReal.ofReal_toReal hε']
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, Real.exp (-(T : ℝ)) ≤ η := by
    refine ⟨⟨max 0 (-Real.log η), le_max_left _ _⟩, ?_⟩
    calc Real.exp (-(max 0 (-Real.log η))) ≤ Real.exp (Real.log η) :=
          Real.exp_le_exp.2 (by linarith [le_max_right 0 (-Real.log η)])
      _ = η := Real.exp_log hη
  filter_upwards [hlam η hη, hx T η hη] with n hn hxn
  refine (iInf_le _ (lam n)).trans (le_trans ?_ hηε)
  refine max_le (iSup_le fun t => ENNReal.ofReal_le_ofReal ?_)
    (iSup_le fun t => ENNReal.ofReal_le_ofReal ?_)
  · exact (min_le_right _ _).trans (hn t)
  · rcases le_or_gt t T with htT | htT
    · calc Real.exp (-(t : ℝ)) * min 1 ‖(x n).toFun (lam n t) - y.toFun t‖
          ≤ 1 * η := mul_le_mul (Real.exp_le_one_iff.2 (by simp)) ((min_le_right _ _).trans
            (hxn t htT)) (by positivity) zero_le_one
        _ = η := one_mul η
    · calc Real.exp (-(t : ℝ)) * min 1 ‖(x n).toFun (lam n t) - y.toFun t‖
          ≤ Real.exp (-(T : ℝ)) * 1 := mul_le_mul (Real.exp_le_exp.2 (by
            have : (T : ℝ) < t := htT
            linarith)) (min_le_left _ _) (by positivity) (Real.exp_pos _).le
        _ ≤ η := by rw [mul_one]; exact hT

/-! ### The J1 pseudometric -/

/-- The symmetrized pre-distance. -/
noncomputable def skorSym (x y : CadlagPath d) : ℝ≥0∞ := max (skorPre x y) (skorPre y x)

theorem skorSym_comm (x y : CadlagPath d) : skorSym x y = skorSym y x := max_comm _ _

theorem skorSym_self (x : CadlagPath d) : skorSym x x = 0 := by simp [skorSym, skorPre_self]

theorem skorSym_le_one (x y : CadlagPath d) : skorSym x y ≤ 1 :=
  max_le (skorPre_le_one _ _) (skorPre_le_one _ _)

theorem skorSym_triangle (x y z : CadlagPath d) :
    skorSym x z ≤ ENNReal.ofReal (Real.exp 1 + 1) * max (skorSym x y) (skorSym y z) := by
  refine max_le ((skorPre_triangle x y z).trans (mul_le_mul' le_rfl (max_le_max
    (le_max_left _ _) (le_max_left _ _)))) ((skorPre_triangle z y x).trans (mul_le_mul' le_rfl ?_))
  rw [max_comm]
  exact max_le_max (le_max_right _ _) (le_max_right _ _)

/-- The fourth root of the symmetrized pre-distance, as a nonnegative real. -/
noncomputable def skorNN (x y : CadlagPath d) : ℝ≥0 :=
  NNReal.sqrt (NNReal.sqrt (skorSym x y).toNNReal)

theorem skorNN_self (x : CadlagPath d) : skorNN x x = 0 := by simp [skorNN, skorSym_self]

theorem skorNN_comm (x y : CadlagPath d) : skorNN x y = skorNN y x := by
  simp only [skorNN, skorSym_comm]

theorem skorNN_four (x₁ x₂ x₃ x₄ : CadlagPath d) :
    skorNN x₁ x₄ ≤ 2 * max (skorNN x₁ x₂) (max (skorNN x₂ x₃) (skorNN x₃ x₄)) := by
  set C := ENNReal.ofReal (Real.exp 1 + 1) with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.one_le_exp_iff.2 (zero_le_one : (0:ℝ) ≤ 1)])
  have fin : ∀ u v : CadlagPath d, skorSym u v ≠ ⊤ := fun u v =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (skorSym_le_one u v)
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, skorSym x₁ x₂ = a := ⟨_, (ENNReal.coe_toNNReal (fin _ _)).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, skorSym x₂ x₃ = b := ⟨_, (ENNReal.coe_toNNReal (fin _ _)).symm⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, skorSym x₃ x₄ = c := ⟨_, (ENNReal.coe_toNNReal (fin _ _)).symm⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ≥0, skorSym x₁ x₄ = e := ⟨_, (ENNReal.coe_toNNReal (fin _ _)).symm⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, C = k := ⟨_, (ENNReal.coe_toNNReal ENNReal.ofReal_ne_top).symm⟩
  have hk2 : NNReal.sqrt k ≤ 2 := by
    have hkr : (k : ℝ) = Real.exp 1 + 1 := by
      have := congrArg ENNReal.toReal hk
      rw [hCdef, ENNReal.toReal_ofReal (by positivity)] at this
      simpa using this.symm
    rw [NNReal.sqrt_le_iff_le_sq, ← NNReal.coe_le_coe, hkr]
    push_cast
    nlinarith [Real.exp_one_lt_d9]
  have hA : skorSym x₂ x₄ ≤ C * max (skorSym x₁ x₂) (max (skorSym x₂ x₃) (skorSym x₃ x₄)) :=
    (skorSym_triangle x₂ x₃ x₄).trans (mul_le_mul' le_rfl
      (max_le ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _))))
  have hB : skorSym x₁ x₂ ≤ C * max (skorSym x₁ x₂) (max (skorSym x₂ x₃) (skorSym x₃ x₄)) :=
    (le_max_left _ _).trans (le_mul_of_one_le_left bot_le hC1)
  have h4 : skorSym x₁ x₄ ≤
      C * (C * max (skorSym x₁ x₂) (max (skorSym x₂ x₃) (skorSym x₃ x₄))) :=
    (skorSym_triangle x₁ x₂ x₄).trans (mul_le_mul' le_rfl (max_le hB hA))
  rw [ha, hb, hc, he, hk] at h4
  have h4' : e ≤ k * (k * max a (max b c)) := by
    have : ((e : ℝ≥0) : ℝ≥0∞) ≤ ((k * (k * max a (max b c)) : ℝ≥0) : ℝ≥0∞) := by
      push_cast
      simpa [ENNReal.coe_max] using h4
    exact_mod_cast this
  have hsq : NNReal.sqrt (NNReal.sqrt (k * (k * max a (max b c)))) =
      NNReal.sqrt k * NNReal.sqrt (NNReal.sqrt (max a (max b c))) := by
    rw [← mul_assoc, NNReal.sqrt_mul, NNReal.sqrt_mul, NNReal.sqrt_mul_self]
  have hmono : NNReal.sqrt (NNReal.sqrt (max a (max b c))) =
      max (NNReal.sqrt (NNReal.sqrt a))
        (max (NNReal.sqrt (NNReal.sqrt b)) (NNReal.sqrt (NNReal.sqrt c))) := by
    have hm : Monotone (fun u : ℝ≥0 => NNReal.sqrt (NNReal.sqrt u)) :=
      NNReal.sqrt.monotone.comp NNReal.sqrt.monotone
    rw [hm.map_max, hm.map_max]
  have hval : skorNN x₁ x₄ = NNReal.sqrt (NNReal.sqrt e) := by simp [skorNN, he]
  have hval₁ : skorNN x₁ x₂ = NNReal.sqrt (NNReal.sqrt a) := by simp [skorNN, ha]
  have hval₂ : skorNN x₂ x₃ = NNReal.sqrt (NNReal.sqrt b) := by simp [skorNN, hb]
  have hval₃ : skorNN x₃ x₄ = NNReal.sqrt (NNReal.sqrt c) := by simp [skorNN, hc]
  rw [hval, hval₁, hval₂, hval₃, ← hmono]
  calc NNReal.sqrt (NNReal.sqrt e) ≤ NNReal.sqrt (NNReal.sqrt (k * (k * max a (max b c)))) :=
        NNReal.sqrt_le_sqrt.2 (NNReal.sqrt_le_sqrt.2 h4')
    _ = NNReal.sqrt k * NNReal.sqrt (NNReal.sqrt (max a (max b c))) := hsq
    _ ≤ 2 * NNReal.sqrt (NNReal.sqrt (max a (max b c))) := mul_le_mul_of_nonneg_right hk2 bot_le

/-- The J1 pseudometric on cadlag paths. -/
noncomputable instance : PseudoMetricSpace (CadlagPath d) :=
  PseudoMetricSpace.ofPreNNDist skorNN skorNN_self skorNN_comm

theorem dist_le_skorNN (x y : CadlagPath d) : dist x y ≤ skorNN x y :=
  PseudoMetricSpace.dist_ofPreNNDist_le skorNN skorNN_self skorNN_comm x y

theorem skorNN_le_two_mul_dist (x y : CadlagPath d) : (skorNN x y : ℝ) ≤ 2 * dist x y :=
  PseudoMetricSpace.le_two_mul_dist_ofPreNNDist skorNN skorNN_self skorNN_comm skorNN_four x y

theorem tendsto_skorNN_iff {x : ℕ → CadlagPath d} {y : CadlagPath d} :
    Tendsto (fun n => (skorNN (x n) y : ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun n => skorSym (x n) y) atTop (𝓝 0) := by
  have fin : ∀ u v : CadlagPath d, skorSym u v ≠ ⊤ := fun u v =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (skorSym_le_one u v)
  have hc : Continuous fun u : ℝ≥0 => ((NNReal.sqrt (NNReal.sqrt u) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (NNReal.continuous_sqrt.comp NNReal.continuous_sqrt)
  constructor
  · intro h
    have h4 : Tendsto (fun n => ((skorNN (x n) y : ℝ) ^ 4)) atTop (𝓝 0) := by
      simpa using h.pow 4
    have heq : ∀ n, ((skorNN (x n) y : ℝ) ^ 4) = ((skorSym (x n) y).toNNReal : ℝ) := by
      intro n
      rw [← NNReal.coe_pow]
      congr 1
      simp only [skorNN]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, NNReal.sq_sqrt, NNReal.sq_sqrt]
    simp_rw [heq] at h4
    have h4' : Tendsto (fun n => (skorSym (x n) y).toNNReal) atTop (𝓝 0) := by
      rw [← NNReal.tendsto_coe]
      simpa using h4
    have := (ENNReal.continuous_coe.tendsto 0).comp h4'
    simpa [Function.comp_def, ENNReal.coe_toNNReal (fin _ _)] using this
  · intro h
    have h1 : Tendsto (fun n => (skorSym (x n) y).toNNReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toNNReal ENNReal.zero_ne_top).comp h
      simpa [Function.comp_def] using this
    have := (hc.tendsto 0).comp h1
    simpa [skorNN, Function.comp_def] using this

/-- J1 convergence is convergence in the J1 pseudometric. -/
theorem SkorokhodTendsto.tendsto_dist {x : ℕ → CadlagPath d} {y : CadlagPath d}
    (h : SkorokhodTendsto x y) : Tendsto (fun n => dist (x n) y) atTop (𝓝 0) := by
  have hpre := h.tendsto_skorPre
  have hsym : Tendsto (fun n => skorSym (x n) y) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => ENNReal.ofReal (Real.exp 1) * skorPre (x n) y) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hpre (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hpre.max h2)
      (fun n => bot_le) (fun n => max_le_max le_rfl (skorPre_symm_le _ _))
  refine squeeze_zero (fun n => dist_nonneg) (fun n => dist_le_skorNN _ _)
    (tendsto_skorNN_iff.2 hsym)

/-- Convergence in the J1 pseudometric is J1 convergence. -/
theorem skorokhodTendsto_of_tendsto_dist {x : ℕ → CadlagPath d} {y : CadlagPath d}
    (h : Tendsto (fun n => dist (x n) y) atTop (𝓝 0)) : SkorokhodTendsto x y := by
  have hnn : Tendsto (fun n => (skorNN (x n) y : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => NNReal.coe_nonneg _) (fun n => skorNN_le_two_mul_dist _ _) ?_
    simpa using h.const_mul 2
  have hsym := tendsto_skorNN_iff.1 hnn
  refine skorokhodTendsto_of_tendsto_skorPre (tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsym (fun n => bot_le) (fun n => le_max_left _ _))

/-! ### Continuous paths in the J1 pseudometric -/

theorem skorokhodTendsto_toCadlag_of_tendsto {γ : ℕ → Path d} {γ₀ : Path d}
    (h : Tendsto γ atTop (𝓝 γ₀)) :
    SkorokhodTendsto (fun n => Path.toCadlag (γ n)) (Path.toCadlag γ₀) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at h
  refine ⟨fun _ => OrderIso.refl ℝ≥0, fun ε hε => Eventually.of_forall fun n t => by simpa using hε.le,
    fun T ε hε => ?_⟩
  have hu := h (Set.Iic T) (by rw [← Set.Icc_bot]; exact isCompact_Icc)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu ε hε] with n hn t ht
  have := hn t ht
  rw [dist_comm, dist_eq_norm] at this
  exact this.le

theorem tendsto_of_skorokhodTendsto_toCadlag {γ : ℕ → Path d} {γ₀ : Path d}
    (h : SkorokhodTendsto (fun n => Path.toCadlag (γ n)) (Path.toCadlag γ₀)) :
    Tendsto γ atTop (𝓝 γ₀) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨T, hT⟩ := hK.bddAbove
  exact (h.tendstoUniformlyOn_Iic T).mono fun t ht => hT ht

/-- `Path.toCadlag` is an embedding of the continuous paths (compact-open topology) into the
cadlag paths with the J1 pseudometric. -/
theorem isInducing_toCadlag : Topology.IsInducing (Path.toCadlag (d := d)) := by
  have hcont : Continuous (Path.toCadlag (d := d)) := by
    refine continuous_iff_seqContinuous.2 fun γ γ₀ h => ?_
    exact tendsto_iff_dist_tendsto_zero.2 (skorokhodTendsto_toCadlag_of_tendsto h).tendsto_dist
  refine Topology.isInducing_iff_nhds.2 fun γ₀ => le_antisymm (hcont.tendsto γ₀).le_comap ?_
  intro U hU
  by_contra hne
  have hball : ∀ n : ℕ, ∃ γ, dist (Path.toCadlag γ) (Path.toCadlag γ₀) < 1 / ((n : ℝ) + 1) ∧
      γ ∉ U := by
    intro n
    by_contra hall
    push_neg at hall
    exact hne (Filter.mem_comap.2 ⟨Metric.ball (Path.toCadlag γ₀) (1 / ((n : ℝ) + 1)),
      Metric.ball_mem_nhds _ (by positivity), fun γ hγ => hall γ hγ⟩)
  choose γ hγ hγU using hball
  have hd : Tendsto (fun n => dist (Path.toCadlag (γ n)) (Path.toCadlag γ₀)) atTop (𝓝 0) :=
    squeeze_zero (fun n => dist_nonneg) (fun n => (hγ n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hγlim := tendsto_of_skorokhodTendsto_toCadlag (skorokhodTendsto_of_tendsto_dist hd)
  obtain ⟨n, hn⟩ := (hγlim.eventually_mem hU).exists
  exact hγU n hn

/-! ### From Skorokhod tests to bounded continuous tests on continuous paths -/

/-- A bounded Lipschitz function on continuous paths (for the J1 pseudometric read through
`Path.toCadlag`) is the restriction of a Skorokhod test. -/
theorem exists_skorokhodTest_of_lipschitz (f : Path d → ℝ) {L : ℝ≥0} {B : ℝ}
    (hL : ∀ γ γ', |f γ - f γ'| ≤ L * dist (Path.toCadlag γ) (Path.toCadlag γ'))
    (hB : ∀ γ, |f γ| ≤ B) :
    ∃ G : CadlagPath d → ℝ, IsSkorokhodTest G ∧ ∀ γ, G (Path.toCadlag γ) = f γ := by
  classical
  let fc : CadlagPath d → ℝ := fun x => if h : Continuous x.toFun then f ⟨x.toFun, h⟩ else 0
  have hfc : ∀ γ : Path d, fc (Path.toCadlag γ) = f γ := fun γ => by
    simp only [fc, Path.toCadlag, dif_pos γ.continuous]
    rfl
  have hLs : LipschitzOnWith L fc (Set.range (Path.toCadlag (d := d))) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨γ, rfl⟩ _ ⟨γ', rfl⟩
    rw [hfc, hfc, Real.dist_eq]
    exact hL γ γ'
  obtain ⟨g, hg, hgs⟩ := hLs.extend_real
  let G : CadlagPath d → ℝ := fun x => max (-B) (min (g x) B)
  have hG : LipschitzWith L G := (hg.min_const B).const_max (-B)
  refine ⟨G, ⟨⟨B, fun x => ?_⟩, fun x y h => ?_⟩, fun γ => ?_⟩
  · have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · exact (hG.continuous.tendsto y).comp (tendsto_iff_dist_tendsto_zero.2 h.tendsto_dist)
  · have h1 : g (Path.toCadlag γ) = f γ := by rw [← hgs ⟨γ, rfl⟩, hfc]
    simp only [G, h1]
    have := abs_le.1 (hB γ)
    rw [min_eq_left this.2, max_eq_right this.1]

/-- Convergence for all Skorokhod tests of laws carried by continuous paths, towards a law on
continuous paths, gives convergence for every bounded continuous test on continuous paths. -/
theorem tendsto_boundedContinuous_of_skorokhod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → Path d} (hY : Measurable Y) {W : Measure (Path d)}
    [IsProbabilityMeasure W]
    (h : ∀ F : CadlagPath d → ℝ, IsSkorokhodTest F →
      Tendsto (fun ε : ℝ => ∫ η, F (Path.toCadlag (rescalePath ε (Y η))) ∂P) (𝓝[>] 0)
        (𝓝 (∫ γ, F (Path.toCadlag γ) ∂W)))
    (F : BoundedContinuousFunction (Path d) ℝ) :
    Tendsto (fun ε : ℝ => ∫ η, F (rescalePath ε (Y η)) ∂P) (𝓝[>] 0) (𝓝 (∫ γ, F γ ∂W)) := by
  letI m : PseudoMetricSpace (Path d) :=
    (PseudoMetricSpace.induced (Path.toCadlag (d := d)) inferInstance).replaceTopology
      isInducing_toCadlag.eq_induced
  have hresc : ∀ ε : ℝ, Measurable fun η => rescalePath ε (Y η) := fun ε =>
    ContinuousMap.measurable_iff_eval.2 fun t =>
      ((continuous_eval_const _).measurable.comp hY).const_smul ε
  let μs : ℝ → ProbabilityMeasure (Path d) := fun ε =>
    ⟨P.map fun η => rescalePath ε (Y η),
      (Measure.isProbabilityMeasure_map_iff (hresc ε).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure (Path d) := ⟨W, inferInstance⟩
  have hconv : Tendsto μs (𝓝[>] 0) (𝓝 μ) := by
    rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro f ⟨C, hC⟩ ⟨L, hL⟩
    have hB : ∀ γ, |f γ| ≤ |f 0| + C := fun γ => by
      have := hC γ 0
      rw [Real.dist_eq] at this
      calc |f γ| = |(f γ - f 0) + f 0| := by ring_nf
        _ ≤ |f γ - f 0| + |f 0| := abs_add_le _ _
        _ ≤ C + |f 0| := add_le_add this le_rfl
        _ = |f 0| + C := add_comm _ _
    have hLd : ∀ γ γ', |f γ - f γ'| ≤ L * dist (Path.toCadlag γ) (Path.toCadlag γ') :=
      fun γ γ' => by
        rw [← Real.dist_eq]
        exact hL.dist_le_mul γ γ'
    obtain ⟨G, hGt, hGf⟩ := exists_skorokhodTest_of_lipschitz f hLd hB
    have hfm : Measurable f := hL.continuous.measurable
    have key := h G hGt
    simp only [hGf] at key
    refine key.congr' (Eventually.of_forall fun ε => ?_) |>.trans ?_
    · change ∫ η, f (rescalePath ε (Y η)) ∂P = ∫ γ, f γ ∂(P.map fun η => rescalePath ε (Y η))
      rw [integral_map (hresc ε).aemeasurable hfm.aestronglyMeasurable]
    · rfl
  have hF := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv) F
  refine hF.congr (fun ε => ?_)
  change ∫ γ, F γ ∂(P.map fun η => rescalePath ε (Y η)) = ∫ η, F (rescalePath ε (Y η)) ∂P
  rw [integral_map (hresc ε).aemeasurable F.continuous.measurable.aestronglyMeasurable]

end EinsteinFull.External.Draft
