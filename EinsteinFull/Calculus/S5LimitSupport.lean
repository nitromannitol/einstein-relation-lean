import EinsteinFull.Calculus.S5DaviesSupport
import EinsteinFull.Calculus.S5ExpWeightSupport
import EinsteinFull.Calculus.S5MollifySupport
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Removing the truncations: Davies bound for Euclidean-Lipschitz exponents

First the truncation parameter is removed for a smooth profile by Fatou's lemma for
`eLpNorm`, then the smooth profile is replaced by a general Euclidean-`1`-Lipschitz one by
mollification, and finally negative exponents are reduced to positive ones by `ψ ↦ -ψ`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5Limit

variable {d : ℕ}

theorem s5_enorm_of_toReal {a b : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : a.toReal ≤ c * b.toReal) : a ≤ ENNReal.ofReal c * b := by
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h

theorem s5_smooth_limit {q K : ℝ} (hq : 0 ≤ q) (hK : 0 ≤ K) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hg : ∀ x, s5Nrm (fun j => coordinateDerivative j ψ x) ≤ 1)
    (f U : Lp ℂ 2 (volume : Measure (Vec d)))
    (hgr : ∀ (φ : Vec d → ℝ) (B : ℝ), S5Weight φ B q →
      (eLpNorm (fun x => (φ x : ℂ) * U x) 2 volume).toReal ≤
        K * (eLpNorm (fun x => (φ x : ℂ) * f x) 2 volume).toReal)
    (hf : MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume) :
    MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ∧
      eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ≤
        ENNReal.ofReal K *
          eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume := by
  have hw : ∀ n : ℕ, S5Weight (fun x => s5G q (n : ℝ) (ψ x)) (Real.exp (q * n)) q :=
    fun n => s5Weight_G hq (n : ℝ) hψ hg
  have hcont : ∀ n : ℕ, Continuous (fun x => s5G q (n : ℝ) (ψ x)) :=
    fun n => (hw n).smooth.continuous
  let fn : ℕ → Vec d → ℂ := fun n x => ((s5G q (n : ℝ) (ψ x) : ℝ) : ℂ) * U x
  let flim : Vec d → ℂ := fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x
  have hfn : ∀ n, AEStronglyMeasurable (fn n) volume := fun n =>
    (Complex.continuous_ofReal.comp (hcont n)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable U)
  have hflim : AEStronglyMeasurable flim volume :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul hψ.continuous))).aestronglyMeasurable.mul (Lp.aestronglyMeasurable U)
  have hlim : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (flim x)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h1 := (tendsto_s5G q (ψ x)).comp tendsto_natCast_atTop_atTop
    exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const (U x)
  have hbound : ∀ n : ℕ, eLpNorm (fn n) 2 volume ≤ ENNReal.ofReal K *
      eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume := by
    intro n
    have hwn := hw n
    have h1 := hgr _ _ hwn
    have hfin1 : eLpNorm (fn n) 2 volume ≠ ⊤ :=
      (s5_memLp_mul hwn.measurable hwn.bound U).eLpNorm_lt_top.ne
    have hfin2 : eLpNorm (fun x => ((s5G q (n : ℝ) (ψ x) : ℝ) : ℂ) * f x) 2 volume ≠ ⊤ :=
      (s5_memLp_mul hwn.measurable hwn.bound f).eLpNorm_lt_top.ne
    have h2 := s5_enorm_of_toReal hK hfin1 hfin2 h1
    refine h2.trans (mul_le_mul' le_rfl ?_)
    refine eLpNorm_mono ((Complex.continuous_ofReal.comp (hcont n)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)) fun x => ?_
    show ‖((s5G q (n : ℝ) (ψ x) : ℝ) : ℂ) * f x‖ ≤
      ‖((Real.exp (q * ψ x) : ℝ) : ℂ) * f x‖
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (s5G_pos _ _ _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (s5G_le_exp hq _ _) (norm_nonneg _)
  have hle := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (2 : ℝ≥0∞)) (μ := volume) hfn flim hflim hlim
  have hcl : atTop.liminf (fun n => eLpNorm (fn n) 2 volume) ≤ ENNReal.ofReal K *
      eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbound).frequently
  have hfinal := hle.trans hcl
  refine ⟨?_, hfinal⟩
  exact hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

theorem s5_lip_limit {q K : ℝ} (hq : 0 ≤ q) (hK : 0 ≤ K) {ψ : Vec d → ℝ}
    (hψ : ∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y))
    (f U : Lp ℂ 2 (volume : Measure (Vec d)))
    (hgr : ∀ (φ : Vec d → ℝ) (B : ℝ), S5Weight φ B q →
      (eLpNorm (fun x => (φ x : ℂ) * U x) 2 volume).toReal ≤
        K * (eLpNorm (fun x => (φ x : ℂ) * f x) 2 volume).toReal)
    (hf : MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume) :
    MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ∧
      eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ≤
        ENNReal.ofReal K *
          eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume := by
  set C := eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume with hC
  have hCtop : C ≠ ⊤ := hf.eLpNorm_lt_top.ne
  have hψc : Continuous ψ := by
    have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hl : LipschitzWith ⟨Real.sqrt d, hsd⟩ ψ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm]
      exact (hψ x y).trans (s5_euclid_le_sqrt _)
    exact hl.continuous
  have hUm : ∀ φ : Vec d → ℝ, Continuous φ →
      AEStronglyMeasurable (fun x => (φ x : ℂ) * U x) volume := fun φ hφ =>
    (Complex.continuous_ofReal.comp hφ).aestronglyMeasurable.mul (Lp.aestronglyMeasurable U)
  have hfm : ∀ φ : Vec d → ℝ, Continuous φ →
      AEStronglyMeasurable (fun x => (φ x : ℂ) * f x) volume := fun φ hφ =>
    (Complex.continuous_ofReal.comp hφ).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hexp : Continuous (fun x => Real.exp (q * ψ x)) :=
    Real.continuous_exp.comp (continuous_const.mul hψc)
  have key : ∀ ε : ℝ, 0 < ε → eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ≤
      ENNReal.ofReal (Real.exp (q * ε) * Real.exp (q * ε)) * (ENNReal.ofReal K * C) := by
    intro ε hε
    obtain ⟨ψ', hs, hg, hclose⟩ := s5_exists_smooth_lipschitz ψ hψ hε
    have hup : ∀ x, Real.exp (q * ψ' x) ≤ Real.exp (q * ε) * Real.exp (q * ψ x) := by
      intro x
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := (abs_le.mp (hclose x)).2
      nlinarith
    have hdown : ∀ x, Real.exp (q * ψ x) ≤ Real.exp (q * ε) * Real.exp (q * ψ' x) := by
      intro x
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := (abs_le.mp (hclose x)).1
      nlinarith
    have hc' : Continuous (fun x => Real.exp (q * ψ' x)) :=
      Real.continuous_exp.comp (continuous_const.mul hs.continuous)
    have hf' : eLpNorm (fun x => ((Real.exp (q * ψ' x) : ℝ) : ℂ) * f x) 2 volume ≤
        ENNReal.ofReal (Real.exp (q * ε)) * C := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hfm _ hc') ?_ 2
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hup x) (norm_nonneg _)
    have hf'm : MemLp (fun x => ((Real.exp (q * ψ' x) : ℝ) : ℂ) * f x) 2 volume :=
      hf'.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)
    obtain ⟨-, hU'⟩ := s5_smooth_limit hq hK hs hg f U hgr hf'm
    have hU : eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ≤
        ENNReal.ofReal (Real.exp (q * ε)) *
          eLpNorm (fun x => ((Real.exp (q * ψ' x) : ℝ) : ℂ) * U x) 2 volume := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hUm _ hexp) ?_ 2
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hdown x) (norm_nonneg _)
    calc eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume
        ≤ ENNReal.ofReal (Real.exp (q * ε)) *
          eLpNorm (fun x => ((Real.exp (q * ψ' x) : ℝ) : ℂ) * U x) 2 volume := hU
      _ ≤ ENNReal.ofReal (Real.exp (q * ε)) *
          (ENNReal.ofReal K * (ENNReal.ofReal (Real.exp (q * ε)) * C)) :=
        mul_le_mul' le_rfl (hU'.trans (mul_le_mul' le_rfl hf'))
      _ = ENNReal.ofReal (Real.exp (q * ε) * Real.exp (q * ε)) * (ENNReal.ofReal K * C) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (q * ε) * Real.exp (q * ε)) *
      (ENNReal.ofReal K * C)) (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal K * C)) := by
    have hc : Continuous (fun ε : ℝ => Real.exp (q * ε) * Real.exp (q * ε)) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have h1 : Tendsto (fun ε : ℝ => Real.exp (q * ε) * Real.exp (q * ε)) (𝓝 0) (𝓝 1) :=
      hc.tendsto' 0 1 (by simp)
    have h2 := ENNReal.tendsto_ofReal (h1.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
    have hb : ENNReal.ofReal K * C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop
    have h3 := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal K * C) h2 (Or.inr hb)
    rw [ENNReal.ofReal_one, one_mul] at h3
    exact h3
  have hfinal : eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ≤
      ENNReal.ofReal K * C :=
    ge_of_tendsto hlim (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact key ε hε)
  refine ⟨?_, hfinal⟩
  exact hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

theorem s5_signed_limit {q K : ℝ} (hK : 0 ≤ K) {ψ : Vec d → ℝ}
    (hψ : ∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y))
    (f U : Lp ℂ 2 (volume : Measure (Vec d)))
    (hgr : ∀ (φ : Vec d → ℝ) (B : ℝ), S5Weight φ B |q| →
      (eLpNorm (fun x => (φ x : ℂ) * U x) 2 volume).toReal ≤
        K * (eLpNorm (fun x => (φ x : ℂ) * f x) 2 volume).toReal)
    (hf : MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume) :
    MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ∧
      eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * U x) 2 volume ≤
        ENNReal.ofReal K *
          eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume := by
  by_cases hq : 0 ≤ q
  · rw [abs_of_nonneg hq] at hgr
    exact s5_lip_limit hq hK hψ f U hgr hf
  · push Not at hq
    have hq' : 0 ≤ -q := by linarith
    rw [abs_of_neg hq] at hgr
    have e : ∀ x, Real.exp ((-q) * (-ψ x)) = Real.exp (q * ψ x) := fun x => by
      rw [neg_mul_neg]
    have hψ' : ∀ x y, |(-ψ) x - (-ψ) y| ≤ euclideanNorm (x - y) := fun x y => by
      simp only [Pi.neg_apply]
      rw [neg_sub_neg, abs_sub_comm]
      exact hψ x y
    have hf' : MemLp (fun x => ((Real.exp ((-q) * (-ψ) x) : ℝ) : ℂ) * f x) 2 volume := by
      simpa only [Pi.neg_apply, e] using hf
    have := s5_lip_limit hq' hK hψ' f U hgr hf'
    simpa only [Pi.neg_apply, e] using this

end S5Limit

end EinsteinFull
