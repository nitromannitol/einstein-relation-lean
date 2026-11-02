import EinsteinFull.Calculus.KernelDerivativeSupport
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Cauchy estimates and absolute time integrability of the actual profile
remainder coefficients in Proposition 6.7, equation (e:cauchy). -/

open MeasureTheory Set Filter
open scoped Topology

namespace EinsteinFull

/-- Pointwise time measurability is preserved by the literal profile subtraction. -/
theorem measurable_kernelProfileRemainder (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (hK : ∀ z, Measurable (fun t => K t z)) (z : ℂ) :
    Measurable (fun t => kernelProfileRemainder d u₀ u₂ γ K t z) := by
  unfold kernelProfileRemainder complexGaussianProfile
  apply (hK z).sub
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · fun_prop
  · exact measurable_const

/-- Real force derivatives are the real parts of the genuine complex derivatives. -/
theorem iteratedDeriv_re_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => (f (y : ℂ)).re) x =
      (iteratedDeriv j f (x : ℂ)).re := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have he : (iteratedDeriv j (fun y : ℝ => (f (y : ℂ)).re)) =
        fun y : ℝ => (iteratedDeriv j f (y : ℂ)).re := funext ih
    rw [he]
    have hd := (hf.contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv j
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
    exact (hd.differentiableAt.hasDerivAt.real_of_complex).deriv

private theorem measurable_deriv_parameter {T : Type*} [MeasurableSpace T]
    (f : T → ℝ → ℝ) (hm : ∀ x, Measurable (fun t => f t x))
    (hf : ∀ t, Differentiable ℝ (f t)) (x : ℝ) :
    Measurable (fun t => deriv (f t) x) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n : ℕ => fun t => ((1 / ((n : ℝ) + 1))⁻¹ *
      (f t (x + 1 / ((n : ℝ) + 1)) - f t x)))
  · intro n
    exact measurable_const.mul ((hm _).sub (hm _))
  · rw [tendsto_pi_nhds]
    intro t
    have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall (fun n => show 0 < 1 / ((n : ℝ) + 1) by positivity)⟩
    exact ((hf t x).hasDerivAt.tendsto_slope_zero_right).comp hseq

/-- Difference quotients derive time measurability; no derivative measurability
is assumed. The parameter space can in particular be the nonnegative times. -/
theorem measurable_iteratedDeriv_parameter {T : Type*} [MeasurableSpace T]
    (f : T → ℝ → ℝ) (hm : ∀ x, Measurable (fun t => f t x))
    (hf : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (f t)) (j : ℕ) (x : ℝ) :
    Measurable (fun t => iteratedDeriv j (f t) x) := by
  induction j generalizing x with
  | zero => exact hm x
  | succ j ih =>
    simp only [iteratedDeriv_succ]
    exact measurable_deriv_parameter _ ih
      (fun t => (hf t).differentiable_iteratedDeriv j
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)) x

/-- Measurability of the actual coefficient on nonnegative times, extended by
zero only outside its integration domain. -/
theorem measurable_kernel_remainder_coefficient (d j : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ) (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hm : ∀ z, Measurable (fun t => K t z)) :
    Measurable (fun t : ℝ => if 0 ≤ t then
      iteratedDeriv j (fun x : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
          (j.factorial : ℝ) else 0) := by
  have H := measurable_iteratedDeriv_parameter
    (fun t x => if 0 ≤ t then
      (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re else 0)
    (fun x => (Complex.continuous_re.measurable.comp
      (measurable_kernelProfileRemainder d u₀ u₂ γ K hm _)).ite
      (measurableSet_le measurable_const measurable_id) measurable_const)
    (fun t => by
      by_cases ht : 0 ≤ t
      · simpa only [if_pos ht] using
          ((differentiable_kernelProfileRemainder d u₀ u₂ γ K t (hK t ht)).contDiff
            (n := (⊤ : ℕ∞))).real_of_complex
      · simp only [if_neg ht]
        exact contDiff_const) j 0
  have He := H.div_const (j.factorial : ℝ)
  convert He using 1
  funext t
  by_cases ht : 0 ≤ t
  · simp only [if_pos ht]
  · simp [ht, iteratedDeriv_const]

private theorem real_coefficient_le_cauchy {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) {R M : ℝ} (hR : 0 < R)
    (hb : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    |iteratedDeriv j (fun x : ℝ => (f (x : ℂ)).re) 0 / (j.factorial : ℝ)| ≤
      M / R ^ j := by
  rw [iteratedDeriv_re_of_entire hf, Complex.ofReal_zero, abs_div,
    abs_of_pos (a := (j.factorial : ℝ)) (Nat.cast_pos.mpr j.factorial_pos)]
  apply (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)).trans
  have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
    (hf.differentiableOn.diffContOnCl) hb
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < j.factorial)).mpr
    (by convert H using 1; ring)

/-- The initial interval has no model subtraction. Cauchy's estimate uses
radius one, inside the exact source disc of radius two. -/
theorem kernel_remainder_coefficient_initial_bound (d j : ℕ) (u₀ u₂ γ C : ℝ)
    (K : ℝ → ℂ → ℂ) (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    |iteratedDeriv j (fun x : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
        (j.factorial : ℝ)| ≤ C := by
  have he : kernelProfileRemainder d u₀ u₂ γ K t = K t := by
    funext z
    simp only [kernelProfileRemainder, if_neg (not_le.mpr ht1), sub_zero]
  rw [he]
  simpa only [one_pow, div_one] using real_coefficient_le_cauchy (hK t ht) j zero_lt_one
    (fun z hz => hb t ht ht1.le z (by
      have hz' : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      rw [hz']; norm_num))

/-- The precise Cauchy decay at large times. The common constant is chosen
before amplitudes, Gaussian rate, kernel, force, and derivative order. -/
theorem kernel_remainder_coefficient_large_bound (d : ℕ) (α C : ℝ)
    (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hb : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    |iteratedDeriv j (fun x : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
        (j.factorial : ℝ)| ≤
      (C * Real.exp (4 * C)) * t ^ (-1 - ((d : ℝ) - j) / 2 - α) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have H := real_coefficient_le_cauchy
    (differentiable_kernelProfileRemainder d u₀ u₂ γ K t (hK t ht0.le)) j
    (one_div_pos.mpr hs) (M := C * t ^ (-1 - (d : ℝ) / 2 - α) * Real.exp (4 * C))
    (by
      intro z hz
      have hz' : ‖z‖ = 1 / Real.sqrt t := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      have hz1 : ‖z‖ * Real.sqrt t = 1 := by rw [hz']; exact one_div_mul_cancel hs.ne'
      have Hz := hb t ht z (by rw [hz1]; norm_num)
      simpa only [hz1, one_add_one_eq_two, sq, show (2 : ℝ) * 2 = 4 by norm_num,
        mul_comm C 4] using Hz)
  apply H.trans_eq
  rw [one_div_pow, div_div_eq_mul_div, div_one]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht0.le]
  calc
    _ = (C * Real.exp (4 * C)) *
        (t ^ (-1 - (d : ℝ) / 2 - α) * t ^ ((1 / 2 : ℝ) * j)) := by ring
    _ = _ := by
      rw [← Real.rpow_add ht0]
      congr 2
      ring

private noncomputable def coefficientMajorant (α C t : ℝ) : ℝ :=
  if t < 1 then C else (C * Real.exp (4 * C)) * t ^ (-1 - α)

private theorem integrableOn_coefficientMajorant {α : ℝ} (hα : 0 < α) (C : ℝ) :
    IntegrableOn (coefficientMajorant α C) (Ici 0) := by
  have hi : IntegrableOn (coefficientMajorant α C) (Ico 0 1) :=
    (integrableOn_const (s := Ico (0 : ℝ) 1) (C := C) (by simp)).congr_fun
      (fun t ht => by simp only [coefficientMajorant, if_pos ht.2]) measurableSet_Ico
  have hr : IntegrableOn (fun t : ℝ => (C * Real.exp (4 * C)) * t ^ (-1 - α))
      (Ici 1) := by
    apply Integrable.const_mul
    apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hl : IntegrableOn (coefficientMajorant α C) (Ici 1) :=
    hr.congr_fun
      (fun t ht => by simp only [coefficientMajorant, if_neg (not_lt.mpr (show (1 : ℝ) ≤ t from ht))])
      measurableSet_Ici
  have hu : Ico (0 : ℝ) 1 ∪ Ici 1 = Ici 0 := by
    ext t
    simp only [mem_union, mem_Ico, mem_Ici]
    constructor
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact le_trans zero_le_one ht
    · intro ht
      by_cases ht1 : t < 1
      · exact Or.inl ⟨ht, ht1⟩
      · exact Or.inr (not_lt.mp ht1)
  simpa only [hu] using hi.union hl

private theorem coefficient_le_majorant (d j : ℕ) (hj : j ≤ d)
    (α C : ℝ) (hC : 0 < C) (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
    (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t))
    (hsmall : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C)
    (hlarge : ∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
      ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
        C * t ^ (-1 - (d : ℝ) / 2 - α) *
          Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv j (fun x : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
        (j.factorial : ℝ)| ≤ coefficientMajorant α C t := by
  by_cases ht1 : t < 1
  · rw [coefficientMajorant, if_pos ht1]
    exact kernel_remainder_coefficient_initial_bound d j u₀ u₂ γ C K hK hsmall ht ht1
  · rw [coefficientMajorant, if_neg ht1]
    have ht1' := not_lt.mp ht1
    apply (kernel_remainder_coefficient_large_bound d α C u₀ u₂ γ K hK hlarge j ht1').trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le ht1'
    have hj' : (j : ℝ) ≤ d := by exact_mod_cast hj
    linarith

/-- Absolute convergence and uniform boundedness of every literal remainder
coefficient integral in the source range. Only the standing hypotheses consumed
by this Cauchy argument occur: entire force dependence, pointwise measurable
time dependence, the initial disc bound, and the fixed-disc profile error.
The output constant precedes every amplitude, rate, and kernel. -/
theorem exists_uniform_kernel_remainder_coefficient_integral_bound (d : ℕ)
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C) :
    ∃ C_out : ℝ, 0 < C_out ∧
    ∀ (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ),
      (∀ t, 0 ≤ t → Differentiable ℂ (K t)) →
      (∀ z, Measurable (fun t => K t z)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C) →
      (∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      ∀ j : Fin (d + 1),
        IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun x : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) (Ici 0) ∧
        |∫ t in Ici (0 : ℝ), iteratedDeriv j.val (fun x : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
            (j.val.factorial : ℝ)| ≤ C_out := by
  refine ⟨|∫ t in Ici (0 : ℝ), coefficientMajorant α C t| + 1,
    by positivity, ?_⟩
  intro u₀ u₂ γ K hK hm hs hl j
  have hb' : ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)),
      ‖iteratedDeriv j.val (fun x : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
          (j.val.factorial : ℝ)‖ ≤ coefficientMajorant α C t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact coefficient_le_majorant d j.val (Nat.le_of_lt_succ j.isLt)
      α C hC u₀ u₂ γ K hK hs hl ht
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      iteratedDeriv j.val (fun x : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
          (j.val.factorial : ℝ)) (volume.restrict (Ici 0)) := by
    have hg := measurable_kernel_remainder_coefficient d j.val u₀ u₂ γ K hK hm
    apply (hg.aestronglyMeasurable (μ := volume.restrict (Ici 0))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact if_pos ht
  have hmajor := integrableOn_coefficientMajorant hα C
  refine ⟨hmajor.mono' hmeas hb', ?_⟩
  exact (norm_integral_le_of_norm_le hmajor hb').trans
    ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))

/-- The same uniform bound for the frozen, literal integral definition of r_j.
Its integrability witness is constructed here, rather than assumed. -/
theorem exists_uniform_integratedRemainderCoefficient_bound (d : ℕ)
    (α C : ℝ) (hα : 0 < α) (hC : 0 < C) :
    ∃ C_out : ℝ, 0 < C_out ∧
    ∀ (u₀ u₂ γ : ℝ) (K : ℝ → ℂ → ℂ)
      (hK : ∀ t, 0 ≤ t → Differentiable ℂ (K t)),
      (∀ z, Measurable (fun t => K t z)) →
      ∀ hR : ∀ t, 0 ≤ t → ∀ x : ℝ, (K t (x : ℂ)).im = 0,
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ 2 → ‖K t z‖ ≤ C) →
      (∀ t : ℝ, 1 ≤ t → ∀ z : ℂ, ‖z‖ * Real.sqrt t ≤ 2 →
        ‖kernelProfileRemainder d u₀ u₂ γ K t z‖ ≤
          C * t ^ (-1 - (d : ℝ) / 2 - α) *
            Real.exp (C * (1 + ‖z‖ * Real.sqrt t) ^ 2)) →
      ∃ hI : ∀ j : Fin (d + 1),
        IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun x : ℝ =>
          (kernelProfileRemainder d u₀ u₂ γ K t (x : ℂ)).re) 0 /
            (j.val.factorial : ℝ)) (Ici 0),
        ∀ j : Fin (d + 1),
          |integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j)| ≤ C_out := by
  obtain ⟨B, hB, H⟩ :=
    exists_uniform_kernel_remainder_coefficient_integral_bound d α C hα hC
  refine ⟨B, hB, ?_⟩
  intro u₀ u₂ γ K hK hm hR hs hl
  have Hr := H u₀ u₂ γ K hK hm hs hl
  exact ⟨fun j => (Hr j).1, fun j => (Hr j).2⟩

end EinsteinFull
