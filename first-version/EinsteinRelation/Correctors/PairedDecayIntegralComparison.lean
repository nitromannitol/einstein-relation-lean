import EinsteinRelation.Correctors.PairedTimeDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Deterministic comparison of the time integral of a nonnegative, measurable decay
profile `a` with the explicit power `M (1+t)^{-(1+d/2)/n}`, and the scale conversion
`√(4R²) R^{-n} (∫₀^{4R²} a)^{n/2} ≤ C R^{-d/2}`, from `paper/main.tex:844–857`.

The integrand `a` is the abstract time-decay profile. The hypothesis
`a t ≤ M (1+t)^{-(1+d/2)/n}` is an explicit premise of the statement; this file does
not derive it from the PDE or the corrector estimate. The constant depends only on
`d`, `n`, and `M`, and it uses the deterministic bound `paired_time_decay_bound`. -/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The weight `t ↦ (1 + t)^r` is continuous on `[0, T]` for `T ≥ 0`, because `1 + t > 0`
there. No sign condition on `r` is needed. -/
private theorem comparison_weight_continuousOn (r : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => (1 + t) ^ r) (Set.uIcc 0 T) := by
  have hbase : ContinuousOn (fun t : ℝ => 1 + t) (Set.uIcc 0 T) := by fun_prop
  refine hbase.rpow_const ?_
  intro t ht
  rw [Set.uIcc_of_le hT] at ht
  have hpos : (0 : ℝ) < 1 + t := by linarith [ht.1]
  exact Or.inl hpos.ne'

/-- A constant multiple of the weight `(1 + t)^r` is interval integrable on `[0, T]`. -/
private theorem comparison_weight_intervalIntegrable (M r : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => M * (1 + t) ^ r) MeasureTheory.volume 0 T := by
  have hcont : ContinuousOn (fun t : ℝ => M * (1 + t) ^ r) (Set.uIcc 0 T) :=
    continuousOn_const.mul (comparison_weight_continuousOn r hT)
  exact hcont.intervalIntegrable

/-- Domination: a measurable `a` with `0 ≤ a t ≤ M (1 + t)^r` for `t ≥ 0` is interval
integrable on `[0, T]` whenever `T ≥ 0`. -/
private theorem comparison_intervalIntegrable {a : ℝ → ℝ} {M r T : ℝ} (ha : Measurable a)
    (ha0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ a t) (haM : ∀ t : ℝ, 0 ≤ t → a t ≤ M * (1 + t) ^ r)
    (hT : 0 ≤ T) : IntervalIntegrable a MeasureTheory.volume 0 T := by
  have hsub : ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖a x‖ ≤ M * (1 + x) ^ r := by
    intro x hx
    rw [Set.uIoc_of_le hT] at hx
    rw [Real.norm_of_nonneg (ha0 x hx.1.le)]
    exact haM x hx.1.le
  have hle : (fun x => ‖a x‖) ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) T)]
      (fun x => M * (1 + x) ^ r) :=
    ae_restrict_of_forall_mem measurableSet_uIoc hsub
  exact IntervalIntegrable.mono_fun' (comparison_weight_intervalIntegrable M r hT)
    ha.aestronglyMeasurable hle

/-- `paper/main.tex:844–857`, the deterministic consumption of the time-decay bound in the
paired-corrector comparison. For `d ≥ 2`, `n > 1 + d/2`, and a bound `M ≥ 0` on the
decay profile, the constant `C` depends only on `d`, `n`, and `M`, not on the profile `a`
or the scale `R`. The `+ 1` keeps `C` strictly positive when `M = 0`. -/
theorem paired_decay_integral_comparison (d n : ℕ) (hd : 2 ≤ d)
 (hn : 1+(d : ℝ)/2 < (n : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
 ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ → ℝ), Measurable a →
 (∀ t : ℝ, 0 ≤ t → 0 ≤ a t) →
 (∀ t : ℝ, 0 ≤ t → a t ≤ M*(1+t)^(-(1+(d : ℝ)/2)/(n : ℝ))) →
 ∀ R : ℝ, 1 ≤ R →
 Real.sqrt (4*R^2)*R^(-(n : ℝ))*(∫ t in (0 : ℝ)..(4*R^2), a t)^((n : ℝ)/2)
 ≤ C*R^(-(d : ℝ)/2) := by
  obtain ⟨C0, hC0, hbound⟩ := paired_time_decay_bound d n hd hn
  refine ⟨M ^ ((n : ℝ) / 2) * C0 + 1, ?_, ?_⟩
  · have hKC : 0 ≤ M ^ ((n : ℝ) / 2) * C0 := mul_nonneg (Real.rpow_nonneg hM _) hC0.le
    linarith
  intro a ha ha0 haM R hR
  have hR0 : 0 < R := by linarith
  have hT : (0 : ℝ) ≤ 4 * R ^ 2 := by positivity
  have hIntA := comparison_intervalIntegrable ha ha0 haM hT
  have hIntW := comparison_weight_intervalIntegrable M (-(1 + (d : ℝ) / 2) / (n : ℝ)) hT
  have hI_le : (∫ t in (0 : ℝ)..(4 * R ^ 2), a t) ≤
      ∫ t in (0 : ℝ)..(4 * R ^ 2), M * (1 + t) ^ (-(1 + (d : ℝ) / 2) / (n : ℝ)) :=
    intervalIntegral.integral_mono_on hT hIntA hIntW (fun x hx => haM x hx.1)
  rw [intervalIntegral.integral_const_mul] at hI_le
  have hI0 : 0 ≤ ∫ t in (0 : ℝ)..(4 * R ^ 2), a t :=
    intervalIntegral.integral_nonneg hT (fun u hu => ha0 u hu.1)
  have hIr0 : 0 ≤ ∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ (-(1 + (d : ℝ) / 2) / (n : ℝ)) :=
    intervalIntegral.integral_nonneg hT
      (fun u hu => Real.rpow_nonneg (by linarith [hu.1] : (0 : ℝ) ≤ 1 + u) _)
  have hhalf : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have hpow : (∫ t in (0 : ℝ)..(4 * R ^ 2), a t) ^ ((n : ℝ) / 2) ≤
      (M * ∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ (-(1 + (d : ℝ) / 2) / (n : ℝ))) ^
        ((n : ℝ) / 2) :=
    Real.rpow_le_rpow hI0 hI_le hhalf
  have hS : 0 ≤ Real.sqrt (4 * R ^ 2) * R ^ (-(n : ℝ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hR0.le _)
  have hK : 0 ≤ M ^ ((n : ℝ) / 2) := Real.rpow_nonneg hM _
  have hRd : 0 ≤ R ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hR0.le _
  calc Real.sqrt (4 * R ^ 2) * R ^ (-(n : ℝ)) * (∫ t in (0 : ℝ)..(4 * R ^ 2), a t) ^ ((n : ℝ) / 2)
      ≤ Real.sqrt (4 * R ^ 2) * R ^ (-(n : ℝ)) *
          (M * ∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ (-(1 + (d : ℝ) / 2) / (n : ℝ))) ^
            ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hpow hS
    _ = M ^ ((n : ℝ) / 2) * (Real.sqrt (4 * R ^ 2) * R ^ (-(n : ℝ)) *
          (∫ t in (0 : ℝ)..(4 * R ^ 2), (1 + t) ^ (-(1 + (d : ℝ) / 2) / (n : ℝ))) ^
            ((n : ℝ) / 2)) := by
        rw [Real.mul_rpow hM hIr0]
        ring
    _ ≤ M ^ ((n : ℝ) / 2) * (C0 * R ^ (-(d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hbound R hR) hK
    _ ≤ (M ^ ((n : ℝ) / 2) * C0 + 1) * R ^ (-(d : ℝ) / 2) := by
        have hexp : (M ^ ((n : ℝ) / 2) * C0 + 1) * R ^ (-(d : ℝ) / 2) =
            M ^ ((n : ℝ) / 2) * (C0 * R ^ (-(d : ℝ) / 2)) + R ^ (-(d : ℝ) / 2) := by
          ring
        rw [hexp]
        linarith [hRd]

end EinsteinRelation.Correctors
