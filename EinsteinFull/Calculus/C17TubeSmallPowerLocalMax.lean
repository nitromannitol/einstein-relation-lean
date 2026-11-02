import EinsteinFull.Calculus.C17TubeLocalMaxAbsorption
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace EinsteinFull.Calculus

/-- Interpolation between a small positive exponent and the essential supremum. -/
theorem c17_eLpNorm_two_interpolation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ) (hu : AEStronglyMeasurable u μ)
    (p : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    eLpNorm u 2 μ ≤ eLpNorm u ⊤ μ ^ (1 - p / 2) *
      eLpNorm u (ENNReal.ofReal p) μ ^ (p / 2) := by
  have ha : 0 < 1 - p / 2 := by linarith
  have hb : 0 < p / 2 := by positivity
  have h := eLpNorm_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μ) (p := 2)
    (f := fun x => ‖u x‖ ^ (1 - p / 2))
    (g := fun x => ‖u x‖ ^ (p / 2))
    (fun x y : ℝ => x * y) (1 : NNReal) continuous_mul
    (ae_of_all μ fun x => by simp) (by norm_num)
  have he : (fun x => ‖u x‖ ^ (1 - p / 2) * ‖u x‖ ^ (p / 2)) =
      fun x => ‖u x‖ := by
    funext x
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) ha.le hb.le]
    have : 1 - p / 2 + p / 2 = 1 := by ring
    rw [this, Real.rpow_one]
  rw [he, eLpNorm_norm u hu, eLpNorm_norm_rpow u hu ha,
    eLpNorm_norm_rpow u hu hb] at h
  have ht : (⊤ : ℝ≥0∞) * ENNReal.ofReal (1 - p / 2) = ⊤ := by
    simp [(ENNReal.ofReal_pos.mpr ha).ne']
  have hp' : (2 : ℝ≥0∞) * ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  simpa only [ht, hp', ENNReal.coe_one, one_mul] using h

/-- A local L² gain yields a local maximum estimate at any smaller positive exponent. -/
theorem c17_small_power_local_max_of_L2_gain
    (p A m : ℝ) (hp : 0 < p) (hp2 : p < 2) (hA : 0 < A) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X] (μ : Measure X)
      (Q : ℝ → Set X) (u : X → ℝ),
      (∀ r, MeasurableSet (Q r)) → Monotone Q →
      MemLp u 2 (μ.restrict (Q 1)) →
      (∀ r s : ℝ, 1/2 ≤ r → r < s → s ≤ 1 →
        eLpNorm u ⊤ (μ.restrict (Q r)) ≤
          ENNReal.ofReal (A * Real.rpow (s-r) (-m)) *
            eLpNorm u 2 (μ.restrict (Q s))) →
      eLpNorm u ⊤ (μ.restrict (Q (1/2))) ≤
        ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal p) (μ.restrict (Q 1)) := by
  let θ : ℝ := p / 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  obtain ⟨C₀, hC₀, habs⟩ := c17_local_max_interpolation_absorption θ m hθ hθ1
  let K : ℝ := A * Real.rpow 2 m
  have hm0 : 0 ≤ m := hm.le
  have hK : 0 < K := by
    have hpow : 1 ≤ Real.rpow 2 m := Real.one_le_rpow (by norm_num) hm0
    dsimp [K]
    exact mul_pos hA (lt_of_lt_of_le zero_lt_one hpow)
  have hC : 0 < C₀ * Real.rpow K (1 / θ) :=
    mul_pos hC₀ (Real.rpow_pos_of_pos hK _)
  refine ⟨C₀ * Real.rpow K (1 / θ), hC, ?_⟩
  intro X _ μ Q u hQ hmono hu hgain
  let M := eLpNorm u (ENNReal.ofReal p) (μ.restrict (Q 1))
  by_cases hM : M = ⊤
  · change eLpNorm u ⊤ (μ.restrict (Q (1/2))) ≤ ENNReal.ofReal (C₀ * Real.rpow K (1/θ)) * M
    rw [hM, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
    exact le_top
  let q : ℝ → ℝ := fun r => 1/4 + r/2
  let F : ℝ → ℝ := fun r => (eLpNorm u ⊤ (μ.restrict (Q (q r)))).toReal
  let T : ℝ≥0∞ := eLpNorm u ⊤ (μ.restrict (Q (3/4)))
  have hT : T ≠ ⊤ := by
    have hg := hgain (3/4) 1 (by norm_num) (by norm_num) (by norm_num)
    have hfin : ENNReal.ofReal (A * Real.rpow (1 - 3/4) (-m)) *
        eLpNorm u 2 (μ.restrict (Q 1)) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.eLpNorm_lt_top
    exact ne_of_lt (lt_of_le_of_lt hg hfin)
  have hq : ∀ r ∈ Set.Icc (1/2 : ℝ) 1, 1/2 ≤ q r ∧ q r ≤ 3/4 := by
    intro r hr
    dsimp [q]
    constructor <;> linarith [hr.1, hr.2]
  have hle : ∀ r ∈ Set.Icc (1/2 : ℝ) 1,
      eLpNorm u ⊤ (μ.restrict (Q (q r))) ≤ T := by
    intro r hr
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set μ (hmono (hq r hr).2))
  have hfinite : ∀ r ∈ Set.Icc (1/2 : ℝ) 1,
      eLpNorm u ⊤ (μ.restrict (Q (q r))) ≠ ⊤ := by
    intro r hr
    exact ne_of_lt (lt_of_le_of_lt (hle r hr) (lt_top_iff_ne_top.mpr hT))
  have hF : ∀ r ∈ Set.Icc (1/2 : ℝ) 1, 0 ≤ F r ∧ F r ≤ T.toReal := by
    intro r hr
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hT (hle r hr)⟩
  have hstep : ∀ s ∈ Set.Icc (1/2 : ℝ) 1, ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      s < t → F s ≤ K * Real.rpow (t-s) (-m) *
        Real.rpow (F t) (1-θ) * Real.rpow M.toReal θ := by
    intro s hs t ht hst
    have hqt : q t ≤ 1 := by have := (hq t ht).2; linarith
    have hqsqt : q s < q t := by dsimp [q]; linarith
    have hμ : μ.restrict (Q (q t)) ≤ μ.restrict (Q 1) := by
      have heq : (μ.restrict (Q 1)).restrict (Q (q t)) = μ.restrict (Q (q t)) := by
        rw [Measure.restrict_restrict (hQ (q t)), Set.inter_eq_left.mpr (hmono hqt)]
      rw [← heq]
      exact Measure.restrict_le_self
    have hu' := hu.mono_measure hμ
    have hinterp := c17_eLpNorm_two_interpolation (μ.restrict (Q (q t))) u
      hu'.aestronglyMeasurable p hp hp2
    have hsmall := eLpNorm_mono_measure u hμ (p := ENNReal.ofReal p)
    have hbound : eLpNorm u ⊤ (μ.restrict (Q (q s))) ≤
        ENNReal.ofReal (A * Real.rpow (q t - q s) (-m)) *
          (eLpNorm u ⊤ (μ.restrict (Q (q t))) ^ (1-θ) * M ^ θ) := by
      calc
        _ ≤ _ := hgain (q s) (q t) (hq s hs).1 hqsqt hqt
        _ ≤ _ := by
          gcongr
          exact hinterp.trans (by gcongr)

    have hreal := ENNReal.toReal_mono ?_ hbound
    · dsimp [F, M, θ, K] at *
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ← ENNReal.toReal_rpow,
        ← ENNReal.toReal_rpow] at hreal
      have hgap : q t - q s = (1/2 : ℝ) * (t-s) := by dsimp [q]; ring
      rw [hgap, Real.mul_rpow (by norm_num) (sub_nonneg.mpr hst.le)] at hreal
      have hpow : (1/2 : ℝ) ^ (-m) = (2 : ℝ) ^ m := by
        rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          Real.inv_rpow (by norm_num) _, Real.rpow_neg (by norm_num), inv_inv]
      rw [hpow] at hreal
      nlinarith
    · apply ne_of_lt
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      apply ENNReal.mul_lt_top
      · exact ENNReal.rpow_lt_top_of_nonneg (by linarith) (hfinite t ht)
      · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hM
  have hres := habs F K M.toReal T.toReal hK ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hF hstep
  have hqhalf : q (1/2) = 1/2 := by norm_num [q]
  dsimp [F] at hres
  rw [hqhalf] at hres
  have hfin := hfinite (1/2) ⟨le_rfl, by norm_num⟩
  rw [hqhalf] at hfin
  apply (ENNReal.toReal_le_toReal hfin ?_).mp
  · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
    simpa only [M, Real.rpow_eq_pow] using hres
  · exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hM))

end EinsteinFull.Calculus
