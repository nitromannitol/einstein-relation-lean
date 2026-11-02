import EinsteinFull.Calculus.U4PhysicalWeightedNash
import EinsteinFull.Calculus.U7PhysicalNashDecay
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import EinsteinRelation.Diffusion.CanonicalKernelStrongContinuitySupport

open MeasureTheory
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal

noncomputable section
namespace EinsteinFull

/-- Finite-measure set tests detect an essential bound for an L² function. -/
theorem u8_ae_abs_le_of_setIntegral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (f : Lp ℝ 2 μ) (B : ℝ)
    (h : ∀ s : Set α, MeasurableSet s → μ s < ∞ →
      |∫ x in s, f x ∂μ| ≤ B * μ.real s) :
    ∀ᵐ x ∂μ, |f x| ≤ B := by
  have hloc (s : Set α) (_ : MeasurableSet s) (hs : μ s < ∞) :
      IntegrableOn (fun x => B - f x) s μ ∧ IntegrableOn (fun x => B + f x) s μ := by
    have hf := integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hs.ne
    exact ⟨(integrableOn_const hs.ne).sub hf, (integrableOn_const hs.ne).add hf⟩
  have hp : 0 ≤ᵐ[μ] fun x => B - f x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hm => (hloc s hs hm).1)
    intro s hs hm
    have hc : Integrable (fun _ : α => B) (μ.restrict s) := integrableOn_const hm.ne
    have hf : Integrable (fun x => f x) (μ.restrict s) :=
      integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hm.ne
    rw [integral_sub hc hf, setIntegral_const, smul_eq_mul, mul_comm]
    have := (abs_le.mp (h s hs hm)).2
    linarith
  have hn : 0 ≤ᵐ[μ] fun x => B + f x := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hm => (hloc s hs hm).2)
    intro s hs hm
    have hc : Integrable (fun _ : α => B) (μ.restrict s) := integrableOn_const hm.ne
    have hf : Integrable (fun x => f x) (μ.restrict s) :=
      integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hm.ne
    rw [integral_add hc hf, setIntegral_const, smul_eq_mul, mul_comm]
    have := (abs_le.mp (h s hs hm)).1
    linarith
  filter_upwards [hp, hn] with x hx hy
  change (0 : ℝ) ≤ B - f x at hx
  change (0 : ℝ) ≤ B + f x at hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Transposition of an indicator L¹-to-L² bound for a symmetric L² operator. -/
theorem u8_symmetric_indicator_transpose {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (T : Lp ℝ 2 μ → Lp ℝ 2 μ) (C : ℝ)
    (hsymm : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g))
    (hbound : ∀ (s : Set α) (hs : MeasurableSet s) (hm : μ s ≠ ∞),
      ‖T (indicatorConstLp 2 hs hm (1 : ℝ))‖ ≤ C * μ.real s)
    (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ, |T f x| ≤ C * ‖f‖ := by
  apply u8_ae_abs_le_of_setIntegral_bound μ (T f) (C * ‖f‖)
  intro s hs hm
  let I : Lp ℝ 2 μ := indicatorConstLp 2 hs hm.ne (1 : ℝ)
  have he : (∫ x in s, T f x ∂μ) = inner ℝ (T I) f := by
    rw [← L2.inner_indicatorConstLp_one hs hm.ne, ← hsymm, real_inner_comm]
  rw [he]
  calc
    |inner ℝ (T I) f| ≤ ‖T I‖ * ‖f‖ := abs_real_inner_le_norm _ _
    _ ≤ (C * μ.real s) * ‖f‖ := mul_le_mul_of_nonneg_right (hbound s hs hm.ne) (norm_nonneg _)
    _ = (C * ‖f‖) * μ.real s := by ring

/-- The indicator estimate transposes for the actual unforced physical evolution. -/
theorem u8_physical_indicator_transpose {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (C : ℝ)
    (hbound : ∀ (s : Set (Vec d)) (hs : MeasurableSet s)
      (hm : physicalReversibleMeasure ω hd 0 s ≠ ∞),
      ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
        (indicatorConstLp 2 hs hm (1 : ℝ))‖ ≤
          C * (physicalReversibleMeasure ω hd 0).real s)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd 0,
      |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f x| ≤ C * ‖f‖ := by
  let : SigmaFinite (physicalReversibleMeasure ω hd 0) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  exact u8_symmetric_indicator_transpose _ _ C
    (Blueprint.gmpPhysicalSemigroup_inner_comm hd ω 0 Λ hΛ hω t) hbound f

/-- Finite-measure indicators belong to L¹, with their exact L¹ mass. -/
theorem u8_indicator_integrable_and_abs_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (hm : μ s ≠ ∞) :
    Integrable (indicatorConstLp 2 hs hm (1 : ℝ)) μ ∧
      (∫ x, |indicatorConstLp 2 hs hm (1 : ℝ) x| ∂μ) = μ.real s := by
  have hi : Integrable (s.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrableOn_const hm).integrable_indicator hs
  have he := indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hm) (c := (1 : ℝ))
  refine ⟨hi.congr he.symm, ?_⟩
  calc
    (∫ x, |indicatorConstLp 2 hs hm (1 : ℝ) x| ∂μ) =
        ∫ x, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ := by
          apply integral_congr_ae
          filter_upwards [he] with x hx
          rw [hx]
          by_cases hxs : x ∈ s <;> simp [hxs]
    _ = μ.real s := integral_indicator_one hs


/-- An L¹-to-L² estimate on functions transposes to an L²-to-L∞ estimate. -/
theorem u8_symmetric_L1_L2_transpose {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (T : Lp ℝ 2 μ → Lp ℝ 2 μ) (C : ℝ)
    (hsymm : ∀ f g, inner ℝ (T f) g = inner ℝ f (T g))
    (hbound : ∀ (g : α → ℝ) (hg1 : Integrable g μ) (hg2 : MemLp g 2 μ),
      ‖T (hg2.toLp g)‖ ≤ C * ∫ x, |g x| ∂μ)
    (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ, |T f x| ≤ C * ‖f‖ := by
  apply u8_symmetric_indicator_transpose μ T C hsymm ?_ f
  intro s hs hm
  let I : Lp ℝ 2 μ := indicatorConstLp 2 hs hm (1 : ℝ)
  have hi := u8_indicator_integrable_and_abs_integral μ s hs hm
  have hb := hbound I hi.1 (Lp.memLp I)
  rw [Lp.toLp_coeFn, hi.2] at hb
  exact hb

/-- Separate the L¹ mass from the quantitative Nash decay expression. -/
theorem u8_decay_rpow_factor (A F d t : ℝ) (hA : 0 < A) (hF : 0 < F)
    (hd : 0 < d) (ht : 0 < t) :
    ((A / F ^ (4 / d)) * t) ^ (-d / 2) =
      (A * t) ^ (-d / 2) * F ^ (2 : ℕ) := by
  have hp : -(4 / d) * (-d / 2) = (2 : ℝ) := by
    field_simp
    ring
  have hf : (A / F ^ (4 / d)) * t = (A * t) * F ^ (-(4 / d)) := by
    rw [Real.rpow_neg hF.le]
    ring
  rw [hf, Real.mul_rpow (mul_nonneg hA.le ht.le) (Real.rpow_nonneg hF.le _),
    ← Real.rpow_mul hF.le, hp, Real.rpow_two]

/-- An integrable L² function with zero L¹ mass is the zero L² element. -/
theorem u8_Lp_eq_zero_of_integral_abs_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ 2 μ) (hf : Integrable f μ)
    (hzero : (∫ x, |f x| ∂μ) = 0) : f = 0 := by
  have hz : ∀ᵐ x ∂μ, |f x| = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (by simpa only [Real.norm_eq_abs] using hf.norm)).mp hzero
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℝ 2 μ] with x hx hx0
  have hx0' : (0 : Lp ℝ 2 μ) x = 0 := by simpa only [Pi.zero_apply] using hx0
  rw [hx0']
  exact abs_eq_zero.mp hx

/-- Positive-time L²-to-L∞ smoothing for the actual unforced physical semigroup. -/
theorem u8_unforced_physical_L2_to_Linfty
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0),
      ∀ᵐ x ∂physicalReversibleMeasure ω hd 0,
        |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f x| ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hdec⟩ := u7_unforced_physical_L1_L2_decay hd ω Λ hΛ hω
  let μ := physicalReversibleMeasure ω hd 0
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  let A : ℝ := 4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))
  have hA : 0 < A := by dsimp [A]; positivity
  let K : ℝ := (A * (t : ℝ)) ^ (-(d : ℝ) / 2)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Real.sqrt K, Real.sqrt_pos.2 hK, ?_⟩
  intro f
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  apply u8_symmetric_L1_L2_transpose μ (S t) (Real.sqrt K)
    (Blueprint.gmpPhysicalSemigroup_inner_comm hd ω 0 Λ hΛ hω t) ?_ f
  intro g hg1 hg2
  let p : Lp ℝ 2 μ := hg2.toLp g
  have hp : Integrable p μ := hg1.congr hg2.coeFn_toLp.symm
  have hm : (∫ x, |p x| ∂μ) = ∫ x, |g x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    simp only [p, hx]
  let F : ℝ := ∫ x, |p x| ∂μ
  have hF : 0 ≤ F := integral_nonneg fun _ => abs_nonneg _
  by_cases hz : F = 0
  · have hp0 : p = 0 := u8_Lp_eq_zero_of_integral_abs_eq_zero μ p hp hz
    have hg0 : (∫ x, |g x| ∂μ) = 0 := by simpa [F, hz] using hm.symm
    change ‖S t p‖ ≤ _
    rw [hp0, map_zero, norm_zero, hg0, mul_zero]
  · have hFp : 0 < F := lt_of_le_of_ne hF (Ne.symm hz)
    have hb := hdec p hp F hFp le_rfl t ht
    have he : (4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ))) * (t : ℝ)) =
        (A / F ^ (4 / (d : ℝ))) * (t : ℝ) := by
      dsimp [A]
      rw [div_mul_eq_div_div]
    rw [he, u8_decay_rpow_factor A F d t hA hFp hdR htR] at hb
    have hsq : ‖S t p‖ ^ 2 ≤ (Real.sqrt K * F) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
      exact hb
    have hn := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hF)).mp hsq
    simpa [p, F, hm] using hn





end EinsteinFull
