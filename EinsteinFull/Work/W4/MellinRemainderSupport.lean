import EinsteinFull.Work.W4.MellinCutoffSupport
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Uniform control of the literal Mellin cutoff remainder. -/

open MeasureTheory Set
open scoped BigOperators

namespace EinsteinFull

private abbrev ProfileParameters := (ℝ × ℝ) × ℝ

private noncomputable def jointProfileDeriv : ℕ → (ProfileParameters × ℝ) → ℝ
  | 0 => fun p => gaussianProfile p.1.1.1 p.1.1.2 p.1.2 p.2
  | n + 1 => fun p => fderiv ℝ (jointProfileDeriv n) p (0, 1)

private theorem contDiff_jointProfileDeriv (n k : ℕ) :
    ContDiff ℝ k (jointProfileDeriv n) := by
  induction n generalizing k with
  | zero =>
      unfold jointProfileDeriv gaussianProfile
      fun_prop
  | succ n ih =>
      exact ((ih (k + 1)).fderiv_right (by simp)).clm_apply contDiff_const

private theorem jointProfileDeriv_eq (n : ℕ) (p : ProfileParameters) :
    (fun u => jointProfileDeriv n (p, u)) =
      iteratedDeriv n (gaussianProfile p.1.1 p.1.2 p.2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ← ih]
      funext u
      have hd : DifferentiableAt ℝ (jointProfileDeriv n) (p, u) :=
        ((contDiff_jointProfileDeriv n 1).differentiable (by norm_num)).differentiableAt
      have hp : HasDerivAt (fun x : ℝ => (p, x)) (0, 1) u :=
        (hasDerivAt_const u p).prodMk (hasDerivAt_id u)
      exact (hd.hasFDerivAt.comp_hasDerivAt u hp).deriv.symm

/-- Every profile derivative is jointly continuous in the signed amplitudes, rate,
and evaluation point. -/
theorem continuous_iteratedDeriv_gaussianProfile (n : ℕ) :
    Continuous (fun p : (((ℝ × ℝ) × ℝ) × ℝ) =>
      iteratedDeriv n (gaussianProfile p.1.1.1 p.1.1.2 p.1.2) p.2) := by
  have heq : (fun p : ProfileParameters × ℝ =>
      iteratedDeriv n (gaussianProfile p.1.1.1 p.1.1.2 p.1.2) p.2) =
      jointProfileDeriv n := by
    funext p
    exact (congrFun (jointProfileDeriv_eq n p.1) p.2).symm
  rw [heq]
  exact (contDiff_jointProfileDeriv n 0).continuous

/-- A derivative bound chosen before all profile parameters and the point.
No positivity of the rate is required on the compact interval. -/
theorem exists_uniform_iteratedDeriv_gaussianProfile_bound (n : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → |γ| ≤ B → ∀ u ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv n (gaussianProfile u₀ u₂ γ) u‖ ≤ C := by
  let K : Set (ProfileParameters × ℝ) :=
    ((Icc (-B) B ×ˢ Icc (-B) B) ×ˢ Icc (-B) B) ×ˢ Icc 0 1
  have hK : IsCompact K := ((isCompact_Icc.prod isCompact_Icc).prod
    isCompact_Icc).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_iteratedDeriv_gaussianProfile n).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun u₀ u₂ γ ha hγ u hu => ?_⟩
  have h₀ : |u₀| ≤ B := (le_add_of_nonneg_right (abs_nonneg u₂)).trans ha
  have h₂ : |u₂| ≤ B := (le_add_of_nonneg_left (abs_nonneg u₀)).trans ha
  exact (hC (((u₀, u₂), γ), u)
    ⟨⟨⟨abs_le.mp h₀, abs_le.mp h₂⟩, abs_le.mp hγ⟩, hu⟩).trans (le_max_left _ _)

/-- Uniform Taylor subtraction on `(0,1]`, with the original derivative-defined
coefficients and a constant depending only on the degree and parameter bound. -/
theorem exists_uniform_gaussianProfile_sub_taylor_div_pow_bound (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → |γ| ≤ B → ∀ u ∈ Ioc (0 : ℝ) 1,
      ‖(gaussianProfile u₀ u₂ γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
          u ^ (d + 1)‖ ≤ C := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_iteratedDeriv_gaussianProfile_bound (d + 1) B
  refine ⟨M / (d.factorial : ℝ), by positivity, fun u₀ u₂ γ ha hγ u hu => ?_⟩
  have hr := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1) (n := d)
    zero_le_one (contDiff_gaussianProfile u₀ u₂ γ (d + 1)).contDiffOn
    (show u ∈ Icc (0 : ℝ) 1 from ⟨hu.1.le, hu.2⟩) (C := M) (by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
        (contDiff_gaussianProfile u₀ u₂ γ (d + 1)).contDiffAt hy]
      exact hbound u₀ u₂ γ ha hγ y hy)
  rw [taylorWithinEval_gaussianProfile, sub_zero] at hr
  rw [norm_div, Real.norm_eq_abs (u ^ (d + 1)), abs_of_pos (pow_pos hu.1 _)]
  apply (div_le_iff₀ (pow_pos hu.1 _)).2
  calc
    _ ≤ M * u ^ (d + 1) / (d.factorial : ℝ) := hr
    _ = M / (d.factorial : ℝ) * u ^ (d + 1) := by ring

/-- The literal small-interval remainder integral is uniformly bounded by `C*s`. -/
theorem exists_uniform_integral_gaussianProfile_remainder_bound (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → |γ| ≤ B → ∀ s : ℝ, 0 < s → s ≤ 1 →
      |∫ u in Ioo (0 : ℝ) s,
        (gaussianProfile u₀ u₂ γ u -
          ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
            u ^ (d + 1)| ≤ C * s := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_gaussianProfile_sub_taylor_div_pow_bound d B
  refine ⟨C, hC, fun u₀ u₂ γ ha hγ s hs hs₁ => ?_⟩
  have hi := norm_setIntegral_le_of_norm_le_const_ae
    (μ := volume) (s := Ioo (0 : ℝ) s) (C := C) measure_Ioo_lt_top (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hbound u₀ u₂ γ ha hγ u ⟨hu.1, hu.2.le.trans hs₁⟩)
  simpa only [Real.norm_eq_abs, Real.volume_real_Ioo_of_le hs.le, sub_zero] using hi

/-- The explicit last term in the Mellin identity is `O(C*s^(d+1))` uniformly
in all amplitudes and rates in the prescribed bounded parameter set. -/
theorem exists_uniform_gaussianProfile_mellin_remainder_bound (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → |γ| ≤ B → ∀ s : ℝ, 0 < s → s ≤ 1 →
      |2 * s ^ d * (∫ u in Ioo (0 : ℝ) s,
        (gaussianProfile u₀ u₂ γ u -
          ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
            u ^ (d + 1))| ≤ C * s ^ (d + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_integral_gaussianProfile_remainder_bound d B
  refine ⟨2 * C, by positivity, fun u₀ u₂ γ ha hγ s hs hs₁ => ?_⟩
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * s ^ d)]
  calc
    _ ≤ (2 * s ^ d) * (C * s) :=
      mul_le_mul_of_nonneg_left (hbound u₀ u₂ γ ha hγ s hs hs₁) (by positivity)
    _ = (2 * C) * s ^ (d + 1) := by rw [pow_succ]; ring

/-- The exact Mellin cutoff formula with its last integral absorbed into a
uniform error bound. The positive rate is needed only for the half-line tail
and finite part; no positive lower rate bound enters the remainder constant. -/
theorem exists_uniform_gaussianProfile_mellin_expansion_bound (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → ∀ hγ : 0 < γ, γ ≤ B →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
      |2 * s ^ d * (∫ u in Ioi s, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) -
        ((∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
          ((d - j.val : ℕ) : ℝ)) * s ^ j.val) +
        2 * profileTaylorCoefficient u₀ u₂ γ d * s ^ d * Real.log (1 / s) +
        2 * profileFinitePart d u₀ u₂ γ hγ * s ^ d)| ≤ C * s ^ (d + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_gaussianProfile_mellin_remainder_bound d B
  refine ⟨C, hC, fun u₀ u₂ γ ha hγ hγB s hs hs₁ => ?_⟩
  rw [gaussianProfile_mellin_cutoff hs hs₁ d u₀ u₂ hγ,
    sub_sub_cancel_left, abs_neg]
  exact hbound u₀ u₂ γ ha (by rwa [abs_of_pos hγ]) s hs hs₁

end EinsteinFull
