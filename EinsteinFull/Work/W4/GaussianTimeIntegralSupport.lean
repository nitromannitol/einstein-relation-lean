import EinsteinFull.Work.W4.MellinRemainderSupport
import EinsteinFull.Work.W3.GaussianTaylorSupport
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The actual Gaussian time integral and its signed-force Mellin expansion. -/

open MeasureTheory Set
open scoped BigOperators

namespace EinsteinFull

/-- Evenness retains signed amplitudes and an arbitrary real rate. -/
theorem gaussianProfile_abs_force (u₀ u₂ γ lam x : ℝ) :
    gaussianProfile u₀ u₂ γ (|lam| * x) = gaussianProfile u₀ u₂ γ (lam * x) := by
  simp only [gaussianProfile, mul_pow, sq_abs]

/-- The literal Mellin integrand is integrable above every positive cutoff. -/
theorem integrableOn_gaussianProfile_div_pow_Ioi {s : ℝ} (hs : 0 < s)
    (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    IntegrableOn (fun u : ℝ => gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) (Ioi s) := by
  by_cases hs₁ : s ≤ 1
  · have hl : IntegrableOn (fun u : ℝ => gaussianProfile u₀ u₂ γ u / u ^ (d + 1))
        (Icc s 1) := by
      apply ContinuousOn.integrableOn_Icc
      exact (contDiff_gaussianProfile u₀ u₂ γ 0).continuous.continuousOn.div
        (continuous_id.pow _).continuousOn
        (fun u hu => pow_ne_zero _ (ne_of_gt (hs.trans_le hu.1)))
    exact (hl.union (integrableOn_gaussianProfile_div_pow_Ioi_one d u₀ u₂ hγ)).mono_set
      (by intro u hu; by_cases hu₁ : u ≤ 1
          · exact Or.inl ⟨hu.le, hu₁⟩
          · exact Or.inr (lt_of_not_ge hu₁))
  · exact (integrableOn_gaussianProfile_div_pow_Ioi_one d u₀ u₂ hγ).mono_set
      (Ioi_subset_Ioi (le_of_not_ge hs₁))

private theorem timeChange_image {s : ℝ} (hs : 0 < s) :
    (fun u : ℝ => (u / s) ^ 2) '' Ioi s = Ioi 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    change s < u at hu
    change 1 < (u / s) ^ 2
    have hq : 1 < u / s := (lt_div_iff₀ hs).2 (by simpa using hu)
    nlinarith
  · intro ht
    change 1 < t at ht
    have hsq : 1 < Real.sqrt t := (Real.lt_sqrt (by norm_num)).2 (by simpa using ht)
    refine ⟨s * Real.sqrt t, ?_, ?_⟩
    · change s < s * Real.sqrt t
      nlinarith
    · dsimp only
      rw [mul_div_cancel_left₀ _ hs.ne', Real.sq_sqrt (by linarith)]

private theorem timeChange_injOn {s : ℝ} (hs : 0 < s) :
    InjOn (fun u : ℝ => (u / s) ^ 2) (Ioi s) := by
  intro u hu v hv huv
  have hu' : 0 < u / s := div_pos (hs.trans hu) hs
  have hv' : 0 < v / s := div_pos (hs.trans hv) hs
  have hq : u / s = v / s := by nlinarith
  exact (div_left_inj' hs.ne').mp hq

private theorem timeChange_hasDeriv (s u : ℝ) :
    HasDerivWithinAt (fun u : ℝ => (u / s) ^ 2) (2 * u / s ^ 2) (Ioi s) u := by
  convert ((hasDerivAt_id' u).div_const s).fun_pow 2 |>.hasDerivWithinAt using 1
  try dsimp
  ring

private theorem timeChange_integrand {s u : ℝ} (hs : 0 < s) (hu : s < u)
    (d : ℕ) (u₀ u₂ γ : ℝ) :
    |2 * u / s ^ 2| *
        (((u / s) ^ 2) ^ (-1 - (d : ℝ) / 2) *
          gaussianProfile u₀ u₂ γ (s * Real.sqrt ((u / s) ^ 2))) =
      (2 * s ^ d) * (gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) := by
  have hu₀ : 0 < u := hs.trans hu
  have hq : 0 < u / s := div_pos hu₀ hs
  have hp : ((u / s) ^ 2) ^ (-1 - (d : ℝ) / 2) = ((u / s) ^ (d + 2))⁻¹ := by
    rw [← Real.rpow_natCast (u / s) 2, ← Real.rpow_mul hq.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-1 - (d : ℝ) / 2) = -((d + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg hq.le, Real.rpow_natCast]
  rw [abs_of_pos (by positivity), hp, Real.sqrt_sq hq.le, mul_div_cancel₀ _ hs.ne',
    div_pow, inv_div]
  rw [show d + 2 = (d + 1) + 1 by omega, pow_succ, pow_succ]
  field_simp
  ring

/-- The genuine substitution `u = |lam|*sqrt(t)`, including integrability on
both actual open half-lines, for either sign of the nonzero force. -/
theorem gaussianProfile_time_integral (d : ℕ) (u₀ u₂ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    {lam : ℝ} (hlam : lam ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - (d : ℝ) / 2) *
      gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) (Ioi 1) ∧
    (∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
      gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) =
      2 * |lam| ^ d *
        (∫ u in Ioi |lam|, gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) := by
  have hs : 0 < |lam| := abs_pos.mpr hlam
  let f : ℝ → ℝ := fun t => t ^ (-1 - (d : ℝ) / 2) *
    gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)
  have heq (u : ℝ) (hu : u ∈ Ioi |lam|) :
      |2 * u / |lam| ^ 2| • f ((u / |lam|) ^ 2) =
        (2 * |lam| ^ d) * (gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) := by
    dsimp only [f, smul_eq_mul]
    rw [← gaussianProfile_abs_force u₀ u₂ γ lam]
    exact timeChange_integrand hs hu d u₀ u₂ γ
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun u _ => timeChange_hasDeriv |lam| u) (timeChange_injOn hs) f
  rw [timeChange_image hs] at hi
  have hright := (integrableOn_gaussianProfile_div_pow_Ioi hs d u₀ u₂ hγ).const_mul
    (2 * |lam| ^ d)
  refine ⟨hi.mpr (IntegrableOn.congr_fun hright
    (fun u hu => (heq u hu).symm) measurableSet_Ioi), ?_⟩
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => timeChange_hasDeriv |lam| u) (timeChange_injOn hs) f
  rw [timeChange_image hs] at h
  rw [h, setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul]

/-- Multiplication by a Gaussian Taylor coefficient converts absolute-force
powers to signed-force powers, also at odd degrees where the coefficient is zero. -/
theorem profileTaylorCoefficient_mul_abs_pow (u₀ u₂ γ lam : ℝ) (j : ℕ) :
    profileTaylorCoefficient u₀ u₂ γ j * |lam| ^ j =
      profileTaylorCoefficient u₀ u₂ γ j * lam ^ j := by
  rcases Nat.even_or_odd j with hj | hj
  · rw [hj.pow_abs]
  · obtain ⟨n, hn⟩ := hj
    have he : j = 2 * n + 1 := by omega
    rw [he, profileTaylorCoefficient_odd, zero_mul, zero_mul]

/-- The subcritical Mellin polynomial has the manuscript's signed powers. -/
theorem gaussianProfile_mellin_polynomial_signed (d : ℕ) (u₀ u₂ γ lam : ℝ) :
    (∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
      ((d - j.val : ℕ) : ℝ)) * |lam| ^ j.val) =
    (∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
      ((d - j.val : ℕ) : ℝ)) * lam ^ j.val) := by
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (2 / ((d - j.val : ℕ) : ℝ)) *
        (profileTaylorCoefficient u₀ u₂ γ j.val * |lam| ^ j.val) := by ring
    _ = (2 / ((d - j.val : ℕ) : ℝ)) *
        (profileTaylorCoefficient u₀ u₂ γ j.val * lam ^ j.val) := by
      rw [profileTaylorCoefficient_mul_abs_pow]
    _ = _ := by ring

/-- The logarithmic and finite-part terms split exactly into the prescribed
ordinary degree-`d` coefficient and the frozen critical kernel term. -/
theorem gaussianProfile_mellin_critical_signed (d : ℕ) (u₀ u₂ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) {lam : ℝ} (hlam : lam ≠ 0) :
    2 * profileTaylorCoefficient u₀ u₂ γ d * |lam| ^ d * Real.log (1 / |lam|) +
      2 * profileFinitePart d u₀ u₂ γ hγ * |lam| ^ d =
    (if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ d +
      integratedKernelCriticalCoefficient d u₀ u₂ γ hγ * criticalKernelTerm d lam hlam := by
  by_cases hd : Even d
  · simp only [integratedKernelCriticalCoefficient, criticalKernelTerm, if_pos hd,
      hd.pow_abs]
    ring
  · have ho := Nat.not_even_iff_odd.mp hd
    obtain ⟨n, hn⟩ := ho
    have he : d = 2 * n + 1 := by omega
    simp only [integratedKernelCriticalCoefficient, criticalKernelTerm, if_neg hd]
    rw [he, profileTaylorCoefficient_odd]
    ring

/-- Exact signed-force model formula, with its literal small-cutoff remainder. -/
theorem gaussianProfile_time_integral_mellin (d : ℕ) (u₀ u₂ : ℝ)
    {γ : ℝ} (hγ : 0 < γ) {lam : ℝ} (hlam : lam ≠ 0) (hlam₁ : |lam| ≤ 1) :
    (∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
      gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) =
    (∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
      ((d - j.val : ℕ) : ℝ)) * lam ^ j.val) +
    (if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ d +
    integratedKernelCriticalCoefficient d u₀ u₂ γ hγ * criticalKernelTerm d lam hlam -
    2 * |lam| ^ d * (∫ u in Ioo (0 : ℝ) |lam|,
      (gaussianProfile u₀ u₂ γ u -
        ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
          u ^ (d + 1)) := by
  rw [(gaussianProfile_time_integral d u₀ u₂ hγ hlam).2,
    gaussianProfile_mellin_cutoff (abs_pos.mpr hlam) hlam₁ d u₀ u₂ hγ,
    gaussianProfile_mellin_polynomial_signed]
  have hc := gaussianProfile_mellin_critical_signed d u₀ u₂ hγ hlam
  linarith only [hc]

/-- A structural model remainder constant is chosen before amplitudes, the
positive rate, and the nonzero signed force. The rate bounds are exactly
`c ≤ γ ≤ B`; the proof of this deterministic error needs only the upper bound. -/
theorem exists_uniform_gaussianProfile_time_expansion_bound (d : ℕ) (B c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → ∀ hγ : 0 < γ, c ≤ γ → γ ≤ B →
      ∀ lam : ℝ, ∀ hlam : lam ≠ 0, |lam| ≤ 1 →
      |(∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
          gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) -
        ((∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
          ((d - j.val : ℕ) : ℝ)) * lam ^ j.val) +
        (if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ d +
        integratedKernelCriticalCoefficient d u₀ u₂ γ hγ * criticalKernelTerm d lam hlam)| ≤
          C * |lam| ^ (d + 1) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_gaussianProfile_mellin_remainder_bound d B
  refine ⟨C, hC, fun u₀ u₂ γ ha hγ _hγc hγB lam hlam hlam₁ => ?_⟩
  rw [gaussianProfile_time_integral_mellin d u₀ u₂ hγ hlam hlam₁,
    sub_sub_cancel_left, abs_neg]
  exact hb u₀ u₂ γ ha (by rwa [abs_of_pos hγ]) |lam| (abs_pos.mpr hlam) hlam₁

/-- The ordinary polynomial correction in the deterministic model is exactly
the correction in the frozen integrated coefficients. The remainder coefficients
are retained literally; this identity asserts no correlation-error estimate. -/
theorem integratedKernelCoefficient_polynomial_model (d : ℕ) (u₀ u₂ γ : ℝ)
    (hγ : 0 < γ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t))
    (hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0)
    (hI : ∀ j : Fin (d + 1), IntegrableOn (fun t : ℝ =>
      iteratedDeriv j.val (fun lam : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
          (j.val.factorial : ℝ)) (Ici 0)) (lam : ℝ) :
    (∑ j : Fin (d + 1), integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j * lam ^ j.val) =
    (∑ j : Fin (d + 1), integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j) *
      lam ^ j.val) +
    (∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
      ((d - j.val : ℕ) : ℝ)) * lam ^ j.val) +
    (if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ d := by
  simp only [integratedKernelCoefficient, add_mul, Finset.sum_add_distrib]
  rw [Fin.sum_univ_castSucc (fun j : Fin (d + 1) =>
    (if j.val < d then 2 * profileTaylorCoefficient u₀ u₂ γ j.val / ((d - j.val : ℕ) : ℝ)
      else if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ j.val)]
  simp only [Fin.val_castSucc, Fin.val_last, lt_self_iff_false, if_false]
  have hs : (∑ j : Fin d,
      (if j.val < d then 2 * profileTaylorCoefficient u₀ u₂ γ j.val / ((d - j.val : ℕ) : ℝ)
        else if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ j.val) =
      ∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val / ((d - j.val : ℕ) : ℝ)) *
        lam ^ j.val := by
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos j.isLt]
  rw [hs]
  ring

/-- Adding the literal remainder polynomial gives exactly the frozen ordinary
and critical coefficients, with a structural `|lam|^(d+1)` model error. This is
a deterministic identity/estimate and does not integrate the correlation error. -/
theorem exists_uniform_gaussianProfile_integrated_coefficient_bound
    (d : ℕ) (B c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u₀ u₂ γ : ℝ,
      |u₀| + |u₂| ≤ B → ∀ hγ : 0 < γ, c ≤ γ → γ ≤ B →
      ∀ (K : ℝ → ℂ → ℂ)
        (hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t))
        (hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0)
        (hI : ∀ j : Fin (d + 1), IntegrableOn (fun t : ℝ =>
          iteratedDeriv j.val (fun lam : ℝ =>
            (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
              (j.val.factorial : ℝ)) (Ici 0)),
      ∀ lam : ℝ, ∀ hlam : lam ≠ 0, |lam| ≤ 1 →
      |((∑ j : Fin (d + 1), integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j) *
          lam ^ j.val) +
        (∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
          gaussianProfile u₀ u₂ γ (lam * Real.sqrt t))) -
        ((∑ j : Fin (d + 1), integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j *
          lam ^ j.val) +
        integratedKernelCriticalCoefficient d u₀ u₂ γ hγ * criticalKernelTerm d lam hlam)| ≤
          C * |lam| ^ (d + 1) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_gaussianProfile_time_expansion_bound d B c
  refine ⟨C, hC, fun u₀ u₂ γ ha hγ hγc hγB K hK hR hI lam hlam hlam₁ => ?_⟩
  have he :
      ((∑ j : Fin (d + 1), integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j) *
        lam ^ j.val) +
        (∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
          gaussianProfile u₀ u₂ γ (lam * Real.sqrt t))) -
        ((∑ j : Fin (d + 1), integratedKernelCoefficient d u₀ u₂ γ hγ K hK hR hI j *
          lam ^ j.val) +
        integratedKernelCriticalCoefficient d u₀ u₂ γ hγ * criticalKernelTerm d lam hlam) =
      (∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
        gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) -
        ((∑ j : Fin d, (2 * profileTaylorCoefficient u₀ u₂ γ j.val /
          ((d - j.val : ℕ) : ℝ)) * lam ^ j.val) +
        (if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0) * lam ^ d +
        integratedKernelCriticalCoefficient d u₀ u₂ γ hγ * criticalKernelTerm d lam hlam) := by
    rw [integratedKernelCoefficient_polynomial_model]
    ring
  rw [he]
  exact hb u₀ u₂ γ ha hγ hγc hγB lam hlam hlam₁

end EinsteinFull
