import EinsteinFull.Work.W4.KernelCauchyCoefficientSupport
import EinsteinFull.Work.W4.GaussianFinitePartEvaluationSupport
import EinsteinFull.Work.W4.MellinRemainderSupport
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient

/-! Uniform bounds for the literal ordinary and critical coefficients of
Proposition 6.7. The coefficient integrability witnesses are constructed. -/

open MeasureTheory Set

namespace EinsteinFull

/-- The derivative-defined Taylor coefficient is continuous in all three
real profile parameters. -/
theorem continuous_profileTaylorCoefficient (j : ℕ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ =>
      profileTaylorCoefficient p.1.1 p.1.2 p.2 j) := by
  exact ((continuous_iteratedDeriv_gaussianProfile j).comp
    (continuous_id.prodMk continuous_const)).div_const _

/-- One bound covers the actual Taylor coefficients of all degrees through d,
before any amplitudes or rate are chosen. -/
theorem exists_uniform_profileTaylorCoefficient_bound (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → |γ| ≤ B → ∀ j : Fin (d + 1),
        |profileTaylorCoefficient u₀ u₂ γ j.val| ≤ C := by
  let S : Set ((ℝ × ℝ) × ℝ) := (Icc (-B) B ×ˢ Icc (-B) B) ×ˢ Icc (-B) B
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hb : ∀ j : Fin (d + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
      |profileTaylorCoefficient p.1.1 p.1.2 p.2 j.val| ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
      (continuous_profileTaylorCoefficient j.val).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩
  choose M hM hbound using hb
  refine ⟨∑ j, M j, Finset.sum_nonneg (fun j _ => hM j), ?_⟩
  intro u₀ u₂ γ ha hγ j
  have h₀ : |u₀| ≤ B := (le_add_of_nonneg_right (abs_nonneg u₂)).trans ha
  have h₂ : |u₂| ≤ B := (le_add_of_nonneg_left (abs_nonneg u₀)).trans ha
  exact (hbound j ((u₀, u₂), γ) ⟨⟨abs_le.mp h₀, abs_le.mp h₂⟩, abs_le.mp hγ⟩).trans
    (Finset.single_le_sum (fun k _ => hM k) (Finset.mem_univ j))

/-- The fixed positive lower rate bound makes the literal Gaussian finite part
uniformly bounded. Rate scaling uses the exact Taylor logarithm, including at
even dimensions; no unspecified finite-part constant is introduced. -/
theorem exists_uniform_profileFinitePart_bound (d : ℕ) (B c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → ∀ hγ : 0 < γ, c ≤ γ → γ ≤ B →
        |profileFinitePart d u₀ u₂ γ hγ| ≤ C := by
  let S : Set ((ℝ × ℝ) × ℝ) := (Icc (-B) B ×ˢ Icc (-B) B) ×ˢ Icc c B
  let F : ((ℝ × ℝ) × ℝ) → ℝ := fun p =>
    (Real.sqrt p.2) ^ d *
      (p.1.1 * profileFinitePart d 1 0 1 zero_lt_one +
        (p.1.2 / p.2) * profileFinitePart d 0 1 1 zero_lt_one) -
      profileTaylorCoefficient p.1.1 p.1.2 p.2 d * (Real.log p.2 / 2)
  have hpos : ∀ p ∈ S, 0 < p.2 := fun p hp => hc.trans_le hp.2.1
  have hcont : ContinuousOn F S := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul
      · exact (Real.continuous_sqrt.comp continuous_snd).pow d |>.continuousOn
      · apply ContinuousOn.add
        · exact (continuous_fst.fst.mul continuous_const).continuousOn
        · exact (continuous_fst.snd.continuousOn.div continuous_snd.continuousOn
            (fun p hp => (hpos p hp).ne')).mul continuousOn_const
    · exact (continuous_profileTaylorCoefficient d).continuousOn.mul
        ((continuous_snd.continuousOn.log (fun p hp => (hpos p hp).ne')).div_const _)
  obtain ⟨C, hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc :
    IsCompact S).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun u₀ u₂ γ ha hγ hγc hγB => ?_⟩
  have h₀ : |u₀| ≤ B := (le_add_of_nonneg_right (abs_nonneg u₂)).trans ha
  have h₂ : |u₂| ≤ B := (le_add_of_nonneg_left (abs_nonneg u₀)).trans ha
  have he : profileFinitePart d u₀ u₂ γ hγ = F ((u₀, u₂), γ) := by
    rw [profileFinitePart_rate, profileFinitePart_eq_amplitudes]
  rw [he]
  exact (hC ((u₀, u₂), γ) ⟨⟨abs_le.mp h₀, abs_le.mp h₂⟩, hγc, hγB⟩).trans
    (le_max_left _ _)

/-- Constructs hI and bounds every prescribed ordinary coefficient and the
critical coefficient with a single structural constant. All parameters and
the actual kernel occur after that constant. The source restriction `2 ≤ d`
is retained in this interface; the coefficient bounds also hold below it. -/
@[nolint unusedArguments]
theorem exists_uniform_integratedKernelCoefficient_bound (d : ℕ) (_hd : 2 ≤ d)
    (α C c : ℝ) (hα : 0 < α) (hC : 0 < C) (hc : 0 < c) :
    ∃ C_out : ℝ, 0 < C_out ∧
    ∀ (u₀ u₂ γ : ℝ) (hγ : 0 < γ) (K : ℝ → ℂ → ℂ),
      |u₀| + |u₂| ≤ C → c ≤ γ → γ ≤ C →
      ∀ hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t),
      (∀ z : ℂ, Measurable (fun t : ℝ => K t z)) →
      ∀ hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0,
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C) →
      (∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      ∃ hI : ∀ j : Fin (d + 1),
        IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) (Ici 0),
      (∀ j : Fin (d + 1),
        |integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j| ≤ C_out) ∧
      |integratedKernelCriticalCoefficient d u₀ u₂ γ hγ| ≤ C_out := by
  obtain ⟨R, hRpos, hr⟩ :=
    exists_uniform_integratedRemainderCoefficient_bound d α C hα hC
  obtain ⟨H, hH, hh⟩ := exists_uniform_profileTaylorCoefficient_bound d C
  obtain ⟨M, hM, hm⟩ := exists_uniform_profileFinitePart_bound d C c hc
  refine ⟨R + 2 * H + 2 * M, by positivity, ?_⟩
  intro u₀ u₂ γ hγ K ha hγc hγC hK hmeas hR hs hl
  obtain ⟨hI, hr⟩ := hr u₀ u₂ γ K hK hmeas hR hs hl
  have hh' := hh u₀ u₂ γ ha (by rwa [abs_of_pos hγ])
  have hm' := hm u₀ u₂ γ ha hγ hγc hγC
  refine ⟨hI, fun j => ?_, ?_⟩
  · have hb : |(if j.val < d then
          2 * profileTaylorCoefficient u₀ u₂ γ j.val / ((d - j.val : ℕ) : ℝ)
          else if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0)| ≤
          2 * H + 2 * M := by
      split_ifs with hj he
      · rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_nonneg (show (0 : ℝ) ≤ ((d - j.val : ℕ) : ℝ) from Nat.cast_nonneg _)]
        have hden : (1 : ℝ) ≤ ((d - j.val : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ d - j.val by omega)
        have hdiv := (div_le_self (by positivity) hden).trans
          (mul_le_mul_of_nonneg_left (hh' j) (by norm_num : (0 : ℝ) ≤ 2))
        linarith
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      · rw [abs_zero]
        positivity
    exact (abs_add_le _ _).trans ((add_le_add (hr j) hb).trans_eq (by ring))
  · unfold integratedKernelCriticalCoefficient
    split_ifs
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h := hh' ⟨d, Nat.lt_succ_self d⟩
      dsimp only at h
      linarith
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith

end EinsteinFull
