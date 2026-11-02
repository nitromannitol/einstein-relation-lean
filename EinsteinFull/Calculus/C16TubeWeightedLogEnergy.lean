import EinsteinFull.Calculus.C11TubeWeightedLocalMax
import EinsteinFull.Calculus.C11TubeWeightedZeroPastRepresentative
import EinsteinFull.Calculus.C13TubeWeakGradientChain
import EinsteinFull.Calculus.C13TubeEnergyEndpoints
import EinsteinFull.Calculus.C5TubeWeightedSquareBalance
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.TimeChange.Pairing
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped ENNReal Topology

namespace EinsteinFull.Calculus

noncomputable section

/-- A positive smooth argument which agrees with the identity above the
positive cutoff. -/
def c16LogArgument (ε x : ℝ) : ℝ :=
  ε / 2 + Real.smoothTransition (4 * x / ε - 2) * (x - ε / 2)

theorem c16_log_argument_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < c16LogArgument ε x := by
  by_cases hx : x ≤ ε / 2
  · have ht : 4 * x / ε - 2 ≤ 0 := by
      have hh : 4 * x / ε ≤ 2 := (div_le_iff₀ hε).2 (by nlinarith)
      linarith
    simp only [c16LogArgument, Real.smoothTransition.zero_of_nonpos ht, zero_mul, add_zero]
    linarith
  · have hx' : 0 ≤ x - ε / 2 := by linarith
    have hs := Real.smoothTransition.nonneg (4 * x / ε - 2)
    dsimp [c16LogArgument]
    positivity

theorem c16_log_argument_eq {ε x : ℝ} (hε : 0 < ε) (hx : 3 * ε / 4 ≤ x) :
    c16LogArgument ε x = x := by
  have ht : 1 ≤ 4 * x / ε - 2 := by
    have : 3 * ε ≤ 4 * x := by linarith
    have : 3 ≤ 4 * x / ε := (le_div_iff₀ hε).2 (by nlinarith)
    linarith
  simp only [c16LogArgument, Real.smoothTransition.one_of_one_le ht, one_mul]
  ring

theorem c16_log_argument_contDiff {ε : ℝ} :
    ContDiff ℝ (⊤ : ℕ∞) (c16LogArgument ε) := by
  unfold c16LogArgument
  fun_prop

/-- A globally smooth logarithm matching `log` above the positive cutoff. -/
def c16LogExtension (ε x : ℝ) : ℝ := Real.log (c16LogArgument ε x)

theorem c16_log_extension_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (c16LogExtension ε) := by
  exact c16_log_argument_contDiff.log (fun x => (c16_log_argument_pos hε x).ne')

theorem c16_log_extension_eq {ε x : ℝ} (hε : 0 < ε) (hx : 3 * ε / 4 ≤ x) :
    c16LogExtension ε x = Real.log x := by
  simp only [c16LogExtension, c16_log_argument_eq hε hx]


/-- The extension has the literal logarithmic derivative on the solution range. -/
theorem c16_log_extension_deriv {ε x : ℝ} (hε : 0 < ε) (hx : 3 * ε / 4 < x) :
    deriv (c16LogExtension ε) x = x⁻¹ := by
  have hloc : c16LogExtension ε =ᶠ[𝓝 x] Real.log := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact c16_log_extension_eq hε (le_of_lt hy)
  rw [hloc.deriv_eq]
  exact Real.deriv_log x

/-- The extension is constant strictly below its transition region. -/
theorem c16_log_extension_deriv_zero {ε x : ℝ} (hε : 0 < ε) (hx : x < ε / 2) :
    deriv (c16LogExtension ε) x = 0 := by
  have hloc : c16LogExtension ε =ᶠ[𝓝 x] (fun _ => Real.log (ε / 2)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hy' : y < ε / 2 := hy
    have ht : 4 * y / ε - 2 ≤ 0 := by
      have hh : 4 * y / ε ≤ 2 := (div_le_iff₀ hε).2 (by nlinarith)
      linarith
    simp only [c16LogExtension, c16LogArgument, Real.smoothTransition.zero_of_nonpos ht,
      zero_mul, add_zero]
  rw [hloc.deriv_eq]
  exact deriv_const x _

/-- The smooth extension has a globally bounded derivative. -/
theorem c16_log_extension_deriv_bounded {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv (c16LogExtension ε) x| ≤ M := by
  have hc : Continuous (fun x => |deriv (c16LogExtension ε) x|) :=
    ((c16_log_extension_contDiff hε).continuous_deriv (by simp)).abs
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨max (max B (ε⁻¹)) 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hlo : x < ε / 2
  · rw [c16_log_extension_deriv_zero hε hlo, abs_zero]
    exact le_max_right _ _
  by_cases hhi : ε ≤ x
  · rw [c16_log_extension_deriv hε (by linarith : 3 * ε / 4 < x), abs_of_pos (inv_pos.mpr (lt_of_lt_of_le hε hhi))]
    exact le_trans (inv_le_inv₀ (lt_of_lt_of_le hε hhi) hε |>.2 hhi)
      (le_trans (le_max_right B (ε⁻¹)) (le_max_left _ _))
  · exact le_trans (hB ⟨x, ⟨le_of_not_gt hlo, le_of_not_ge hhi⟩, rfl⟩)
      (le_trans (le_max_left B (ε⁻¹)) (le_max_left _ _))


/-- The second derivative is the logarithmic curvature above the cutoff. -/
theorem c16_log_extension_second_deriv {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ x) :
    deriv (deriv (c16LogExtension ε)) x = -(x ^ 2)⁻¹ := by
  have hloc : deriv (c16LogExtension ε) =ᶠ[𝓝 x] (fun y : ℝ => y⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show 3 * ε / 4 < x by linarith)] with y hy
    exact c16_log_extension_deriv hε hy
  rw [hloc.deriv_eq]
  exact deriv_inv

theorem c16_log_extension_second_deriv_zero {ε x : ℝ} (hε : 0 < ε)
    (hx : x < ε / 2) : deriv (deriv (c16LogExtension ε)) x = 0 := by
  have hloc : deriv (c16LogExtension ε) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact c16_log_extension_deriv_zero hε hy
  rw [hloc.deriv_eq]
  exact deriv_const x _

/-- Both derivatives have bounds suitable for the nonlinear chain rule. -/
theorem c16_log_extension_second_deriv_bounded {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv (deriv (c16LogExtension ε)) x| ≤ M := by
  have h2 : ContDiff ℝ 2 (c16LogExtension ε) :=
    (c16_log_extension_contDiff hε).of_le (by simp)
  have hd : ContDiff ℝ 1 (deriv (c16LogExtension ε)) := h2.deriv'
  have hc : Continuous (fun x => |deriv (deriv (c16LogExtension ε)) x|) :=
    hd.continuous_deriv_one.abs
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨max (max B ((ε⁻¹) ^ 2)) 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hlo : x < ε / 2
  · rw [c16_log_extension_second_deriv_zero hε hlo, abs_zero]
    exact le_max_right _ _
  by_cases hhi : ε ≤ x
  · have hx : 0 < x := lt_of_lt_of_le hε hhi
    have hi : x⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hx hε).2 hhi
    have hp : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
    have hsq : (x ^ 2)⁻¹ ≤ (ε⁻¹) ^ 2 := by
      rw [← inv_pow]
      nlinarith [sq_nonneg (ε⁻¹ - x⁻¹)]
    rw [c16_log_extension_second_deriv hε hhi, abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x))]
    exact le_trans hsq
      (le_trans (le_max_right B ((ε⁻¹) ^ 2)) (le_max_left _ _))
  · exact le_trans (hB ⟨x, ⟨le_of_not_gt hlo, le_of_not_ge hhi⟩, rfl⟩)
      (le_trans (le_max_left B ((ε⁻¹) ^ 2)) (le_max_left _ _))


/-- The logarithm splice normalized for the bounded-derivative chain rule. -/
def c16NormalizedLog (ε x : ℝ) : ℝ :=
  c16LogExtension ε x - c16LogExtension ε 0

theorem c16_normalized_log_properties {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (c16NormalizedLog ε) ∧ c16NormalizedLog ε 0 = 0 ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ r, |deriv (c16NormalizedLog ε) r| ≤ M ∧
      |deriv (deriv (c16NormalizedLog ε)) r| ≤ M) ∧
    (∀ r, ε ≤ r → c16NormalizedLog ε r = Real.log r - c16LogExtension ε 0) ∧
    (∀ r, ε ≤ r → deriv (c16NormalizedLog ε) r = r⁻¹) ∧
    (∀ r, ε ≤ r → deriv (deriv (c16NormalizedLog ε)) r = -(r ^ 2)⁻¹) := by
  have hd : deriv (c16NormalizedLog ε) = deriv (c16LogExtension ε) := by
    unfold c16NormalizedLog
    exact deriv_sub_const_fun _
  obtain ⟨M₁, hM₁, h1⟩ := c16_log_extension_deriv_bounded hε
  obtain ⟨M₂, hM₂, h2⟩ := c16_log_extension_second_deriv_bounded hε
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((c16_log_extension_contDiff hε).of_le (by simp)).sub contDiff_const
  · simp [c16NormalizedLog]
  · refine ⟨max M₁ M₂, le_trans hM₁ (le_max_left _ _), fun r => ⟨?_, ?_⟩⟩
    · rw [hd]; exact le_trans (h1 r) (le_max_left _ _)
    · rw [hd]; exact le_trans (h2 r) (le_max_right _ _)
  · intro r hr
    simp only [c16NormalizedLog, c16_log_extension_eq hε (by linarith : 3 * ε / 4 ≤ r)]
  · intro r hr
    rw [hd]
    exact c16_log_extension_deriv hε (by linarith)
  · intro r hr
    rw [hd]
    exact c16_log_extension_second_deriv hε hr

/-- The logarithm of a positive weak Sobolev function has its literal
quotient weak gradient, with a harmless constant normalization. -/
theorem c16_native_weak_gradient_log {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G)
    (hpositive : ∀ᵐ x ∂volume.restrict U, ε ≤ u x) :
    MemLp (fun x => Real.log (u x) - c16LogExtension ε 0) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm ((u x)⁻¹ • G x)) 2 (volume.restrict U) ∧
    HasWeakGradient U (fun x => Real.log (u x) - c16LogExtension ε 0)
      (fun x => (u x)⁻¹ • G x) := by
  obtain ⟨hF, hF0, ⟨M, hM, hd⟩, hval, hder, _⟩ := c16_normalized_log_properties hε
  have hc := c13_native_weak_gradient_bounded_C1_chain hU u G hu hG hw
    (c16NormalizedLog ε) (hF.of_le (by norm_num)) hF0 M hM (fun r => (hd r).1)
  have hv : (fun x => c16NormalizedLog ε (u x)) =ᵐ[volume.restrict U]
      (fun x => Real.log (u x) - c16LogExtension ε 0) := by
    filter_upwards [hpositive] with x hx
    exact hval (u x) hx
  have hg : (fun x => deriv (c16NormalizedLog ε) (u x) • G x) =ᵐ[volume.restrict U]
      (fun x => (u x)⁻¹ • G x) := by
    filter_upwards [hpositive] with x hx
    rw [hder (u x) hx]
  exact ⟨(memLp_congr_ae hv).mp hc.1,
    (memLp_congr_ae (hg.mono fun _ h => congrArg euclideanNorm h)).mp hc.2.1,
    Correctors.hasWeakGradient_congr_ae hU hc.2.2 hv hg⟩


/-- The unnormalized logarithm has the same quotient weak gradient. -/
theorem c16_native_weak_gradient_log_literal {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G)
    (hpositive : ∀ᵐ x ∂volume.restrict U, ε ≤ u x) :
    HasWeakGradient U (fun x => Real.log (u x)) (fun x => (u x)⁻¹ • G x) := by
  have h := (c16_native_weak_gradient_log hU hε u G hu hG hw hpositive).2.2
  have hc := Correctors.hasWeakGradient_sub_const U h (-c16LogExtension ε 0)
  simpa only [sub_neg_eq_add, sub_add_cancel] using hc


/-- Almost every spatial slice of a positive weighted caloric function has
its actual logarithmic weak gradient. -/
theorem c16_weighted_caloric_log_gradient_slices {d : ℕ} {I : Set ℝ}
    {U : Set (Vec d)}
    (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => Real.log (u (t, x)))
        (fun x => (u (t, x))⁻¹ • G (t, x)) := by
  have hu : MemLp u 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hcal.1
  have hG : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hcal.2.2.1
  have hp : ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict U), ε ≤ u z := by
    rw [Measure.prod_restrict]
    exact hpositive
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hu,
    c9_memLp_prod_right_ae _ _ _ hG, hcal.2.2.2.1,
    Measure.ae_ae_of_ae_prod hp] with t hut hGt hwt hpt
  exact c16_native_weak_gradient_log_literal hU hε _ _ hut hGt hwt hpt



/-- On the full space-time cylinder, the positive solution's normalized
 logarithm and its actual quotient gradient are square integrable. -/
theorem c16_weighted_caloric_log_memLp {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    {ε : ℝ} (hε : 0 < ε) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    MemLp (fun z => Real.log (u z) - c16LogExtension ε 0) 2
      (volume.restrict (I ×ˢ U)) ∧
    MemLp (fun z => euclideanNorm ((u z)⁻¹ • G z)) 2
      (volume.restrict (I ×ˢ U)) := by
  obtain ⟨hF, hF0, ⟨M, hM, hd⟩, hval, hder, _⟩ := c16_normalized_log_properties hε
  have hlip := PDE.lipschitzWith_of_abs_deriv_le hM
    (hF.differentiable (by norm_num)) (fun r => (hd r).1)
  have hf : MemLp (fun z => c16NormalizedLog ε (u z)) 2
      (volume.restrict (I ×ˢ U)) := hlip.comp_memLp hF0 hcal.1
  have hv : (fun z => c16NormalizedLog ε (u z)) =ᵐ[volume.restrict (I ×ˢ U)]
      (fun z => Real.log (u z) - c16LogExtension ε 0) := by
    filter_upwards [hpositive] with z hz
    exact hval (u z) hz
  refine ⟨(memLp_congr_ae hv).mp hf, ?_⟩
  have hc : Continuous (deriv (c16NormalizedLog ε)) :=
    hF.continuous_deriv (by norm_num)
  have hcoef := hc.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable
  have hnorm := hcoef.norm.mul hcal.2.2.1.aestronglyMeasurable
  have hg : MemLp (fun z => euclideanNorm (deriv (c16NormalizedLog ε) (u z) • G z))
      2 (volume.restrict (I ×ˢ U)) := by
    apply (hcal.2.2.1.const_mul M).mono' ?_
    · filter_upwards with z
      simp only [Real.norm_eq_abs, TimeChange.euclideanNorm_smul]
      have hG : 0 ≤ euclideanNorm (G z) := by
        rw [TimeChange.euclideanNorm_eq_norm_toLp]; positivity
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) hG)]
      exact mul_le_mul_of_nonneg_right (hd (u z)).1 hG
    · convert hnorm using 1 <;> ext z <;> simp [TimeChange.euclideanNorm_smul, Real.norm_eq_abs]
  have heq : (fun z => euclideanNorm (deriv (c16NormalizedLog ε) (u z) • G z))
      =ᵐ[volume.restrict (I ×ˢ U)] (fun z => euclideanNorm ((u z)⁻¹ • G z)) := by
    filter_upwards [hpositive] with z hz
    rw [hder (u z) hz]
  exact (memLp_congr_ae heq).mp hg



/-- The cutoff logarithmic dissipation is integrable on the cylinder and,
 after spatial integration, in time. -/
theorem c16_weighted_caloric_log_dissipation_integrable {d : ℕ}
    {I : Set ℝ} {U : Set (Vec d)} {ε : ℝ} (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 * euclideanSq ((u z)⁻¹ • G z))
      (volume.restrict (I ×ˢ U)) ∧
    Integrable (fun t => ∫ x in U, χ x ^ 2 *
      euclideanSq ((u (t, x))⁻¹ • G (t, x))) (volume.restrict I) := by
  let μ := volume.restrict (I ×ˢ U)
  have hg := (c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive).2
  have henergy : Integrable (fun z => euclideanSq ((u z)⁻¹ • G z)) μ := by
    simpa only [TimeChange.euclideanSq_eq_sq_euclideanNorm] using hg.integrable_sq
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ⊤ μ := by
    have hp : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ⊤ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have he : Integrable (fun z => χ z.2 ^ 2 * euclideanSq ((u z)⁻¹ • G z)) μ :=
    henergy.mul_of_top_right hsq
  refine ⟨he, ?_⟩
  have hp : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 *
      euclideanSq ((u z)⁻¹ • G z)) ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact he
  exact hp.integral_prod_left


/-- The actual weighted logarithmic mass is integrable on the finite
cylinder and after spatial integration in time. -/
theorem c16_weighted_caloric_log_mass_integrable {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    Integrable (fun z => ρ z.2 * χ z.2 ^ 2 * Real.log (u z))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) ∧
    Integrable (fun t => ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t, x)))
      (volume.restrict (Set.Ioo a b)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  letI : IsFiniteMeasure (volume.restrict (sourceBall (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (c9_sourceBall_measure_ne_top 0 R)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))) := inferInstance
  haveI : IsFiniteMeasure μ := by
    rw [Measure.prod_restrict] at hf
    exact hf
  have hl : MemLp (fun z => Real.log (u z)) 2 μ := by
    have hh := (c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive).1.add
      (memLp_const (c16LogExtension ε 0))
    convert hh using 1
    ext z
    simp
  obtain ⟨hρ, _⟩ := EinsteinFull.Blueprint.TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell (Measure.map Prod.snd μ)
  have hρ' : MemLp (fun z : ℝ × Vec d => ρ z.2) ⊤ μ :=
    hρ.comp_of_map measurable_snd.aemeasurable
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hχsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ⊤ μ := by
    have hp : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ⊤ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hm : Integrable (fun z => ρ z.2 * χ z.2 ^ 2 * Real.log (u z)) μ := by
    have hh := (hl.integrable (by norm_num)).mul_of_top_right (hρ'.mul hχsq)
    convert hh using 1
  refine ⟨hm, ?_⟩
  have hp : Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2 * Real.log (u z))
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall 0 R))) := by
    rw [Measure.prod_restrict]
    exact hm
  exact hp.integral_prod_left


/-- The actual elliptic flux of the logarithmic gradient is square integrable. -/
theorem c16_weighted_caloric_log_flux_memLp {d : ℕ}
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    ∀ i : Fin d, MemLp (fun z => ((α z.2).mulVec ((u z)⁻¹ • G z)) i) 2
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  let H : ℝ × Vec d → Vec d := fun z => (u z)⁻¹ • G z
  obtain ⟨hF, _, _, _, hder, _⟩ := c16_normalized_log_properties hε
  have hc : Continuous (deriv (c16NormalizedLog ε)) := hF.continuous_deriv (by norm_num)
  have hm : AEStronglyMeasurable H μ := by
    have hh := (hc.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hcal.2.1
    apply hh.congr
    filter_upwards [hpositive] with z hz
    change deriv (c16NormalizedLog ε) (u z) • G z = (u z)⁻¹ • G z
    rw [hder (u z) hz]
  have hv : MemLp H 2 μ := by
    apply (c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive).2.mono' hm
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (H z) i)
  have hg : ∀ i, MemLp (fun z => H z i) 2 μ := memLp_pi_iff.mp hv
  obtain ⟨_, hα⟩ := EinsteinFull.Blueprint.TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell (Measure.map Prod.snd μ)
  intro i
  simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, Function.comp_apply] using
    memLp_finsetSum Finset.univ (fun j _ =>
      ((hα i j).comp_of_map measurable_snd.aemeasurable).mul (hg j))

/-- The logarithmic cutoff flux is integrable in space-time and time. -/
theorem c16_weighted_caloric_log_cutoff_flux_integrable {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => 2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
      (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) ∧
    Integrable (fun t => ∫ x in sourceBall 0 R, 2 * χ x *
      dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x)))
        (fun j => fderiv ℝ χ x (unitVector j))) (volume.restrict (Set.Ioo a b)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  letI : IsFiniteMeasure (volume.restrict (sourceBall (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (c9_sourceBall_measure_ne_top 0 R)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))) := inferInstance
  haveI : IsFiniteMeasure μ := by rw [Measure.prod_restrict] at hf; exact hf
  have hflux := c16_weighted_caloric_log_flux_memLp hκ hε ρ α hell u G hcal hpositive
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hder (i : Fin d) : MemLp (fun z : ℝ × Vec d => fderiv ℝ χ z.2 (unitVector i)) 2 μ := by
    have hc : Continuous (fun x => fderiv ℝ χ x (unitVector i)) :=
      (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hs : HasCompactSupport (fun x => fderiv ℝ χ x (unitVector i)) :=
      hχc.fderiv_apply ℝ (unitVector i)
    obtain ⟨D, hD, hboundD⟩ := (hs.isCompact_range hc).isBounded.exists_pos_norm_le
    have ht : MemLp (fun z : ℝ × Vec d => fderiv ℝ χ z.2 (unitVector i)) ⊤ μ := by
      apply memLp_top_of_bound (hc.comp continuous_snd).aestronglyMeasurable D
      exact ae_of_all μ (fun z => hboundD _ ⟨z.2, rfl⟩)
    exact ht.mono_exponent (by simp)
  have hi : Integrable (fun z => dot ((α z.2).mulVec ((u z)⁻¹ • G z))
      (fun j => fderiv ℝ χ z.2 (unitVector j))) μ := by
    change Integrable (fun z => ∑ i : Fin d, ((α z.2).mulVec ((u z)⁻¹ • G z)) i *
      fderiv ℝ χ z.2 (unitVector i)) μ
    exact integrable_finsetSum Finset.univ (fun i _ => (hflux i).integrable_mul (hder i))
  have hi' : Integrable (fun z => 2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
      (fun j => fderiv ℝ χ z.2 (unitVector j))) μ := by
    have hh := (hi.mul_of_top_right hχtop).const_mul 2
    convert hh using 1 <;> ext z <;> simp only [Pi.mul_apply] <;> ring
  refine ⟨hi', ?_⟩
  have hp : Integrable (fun z : ℝ × Vec d => 2 * χ z.2 *
      dot ((α z.2).mulVec ((u z)⁻¹ • G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall 0 R))) := by
    rw [Measure.prod_restrict]
    exact hi'
  exact hp.integral_prod_left


/-- The actual logarithmic flux and coefficient dissipation are integrable. -/
theorem c16_weighted_caloric_log_coefficient_energy_integrable {d : ℕ}
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) :
    Integrable (fun z => dot ((α z.2).mulVec ((u z)⁻¹ • G z))
      ((u z)⁻¹ • G z)) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  let H : ℝ × Vec d → Vec d := fun z => (u z)⁻¹ • G z
  obtain ⟨hF, _, _, _, hder, _⟩ := c16_normalized_log_properties hε
  have hc : Continuous (deriv (c16NormalizedLog ε)) :=
    hF.continuous_deriv (by norm_num)
  have hm : AEStronglyMeasurable H μ := by
    have hh := (hc.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable).smul hcal.2.1
    apply hh.congr
    filter_upwards [hpositive] with z hz
    change deriv (c16NormalizedLog ε) (u z) • G z = (u z)⁻¹ • G z
    rw [hder (u z) hz]
  have hv : MemLp H 2 μ := by
    apply (c16_weighted_caloric_log_memLp hε ρ α u G hcal hpositive).2.mono' hm
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (H z) i)
  have hg : ∀ i, MemLp (fun z => H z i) 2 μ := memLp_pi_iff.mp hv
  obtain ⟨_, hα⟩ := EinsteinFull.Blueprint.TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell (Measure.map Prod.snd μ)
  have hf (i : Fin d) : MemLp (fun z => ((α z.2).mulVec (H z)) i) 2 μ := by
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, Function.comp_apply] using
      memLp_finsetSum Finset.univ (fun j _ =>
        ((hα i j).comp_of_map measurable_snd.aemeasurable).mul (hg j))
  change Integrable (fun z => ∑ i : Fin d, ((α z.2).mulVec (H z)) i * H z i) μ
  exact integrable_finsetSum Finset.univ (fun i _ => (hf i).integrable_mul (hg i))


/-- The complete logarithmic energy integrand is integrable on the
cylinder and after spatial integration. -/
theorem c16_weighted_caloric_log_energy_integrable {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
        ((u z)⁻¹ • G z) +
      2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) ∧
    Integrable (fun t => ∫ x in sourceBall 0 R,
      χ x ^ 2 * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) +
      2 * χ x * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x)))
        (fun j => fderiv ℝ χ x (unitVector j))) (volume.restrict (Set.Ioo a b)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hχsq : MemLp (fun z : ℝ × Vec d => χ z.2 ^ 2) ⊤ μ := by
    have hp : MemLp (fun z : ℝ × Vec d => χ z.2 * χ z.2) ⊤ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hc := c16_weighted_caloric_log_coefficient_energy_integrable hκ hε ρ α hell u G hcal hpositive
  have he : Integrable (fun z => χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
      ((u z)⁻¹ • G z)) μ := by
    convert hc.mul_of_top_right hχsq using 1 <;> ext z <;> simp only [Pi.mul_apply] <;> ring
  have hx := (c16_weighted_caloric_log_cutoff_flux_integrable hκ hε ρ α hell u G hcal hpositive χ hχ hχc).1
  have hi := he.add hx
  refine ⟨hi, ?_⟩
  have hp : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 *
      dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z) +
      2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall 0 R))) := by
    rw [Measure.prod_restrict]
    exact hi
  exact hp.integral_prod_left


/-- Ellipticity and Young's inequality control the spatial cutoff term in
 the logarithmic energy identity. -/
theorem c16_log_energy_cutoff_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (x e p : Vec d) (χ : ℝ) :
    (κ / 2) * χ ^ 2 * euclideanSq e ≤
      χ ^ 2 * dot e ((α x).mulVec e) +
        2 * χ * dot ((α x).mulVec e) p + (2 / κ ^ 3) * euclideanSq p := by
  have h := c11_weighted_ramp_coefficient_lower hκ hell x e p
    (F0 := 1) (F1 := 1) (F2 := 1) (K := 1) (η := χ) (τ := 0)
    (χ := 1) (χ' := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hk : κ ≤ κ⁻¹ := (hell.2.2 x).1.trans (hell.2.2 x).2.1
  have hkone : κ ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hk hκ.le
    have hi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    nlinarith [sq_nonneg (κ - 1)]
  have hkpow : κ ^ 3 ≤ κ := by nlinarith [sq_nonneg κ, sq_nonneg (κ - 1)]
  have hinv : κ⁻¹ ≤ (κ ^ 3)⁻¹ := (inv_le_inv₀ hκ (show 0 < κ ^ 3 by positivity)).2 hkpow
  have hp : 0 ≤ euclideanSq p := PDE.vecNormSq_nonneg p
  have hm := mul_le_mul_of_nonneg_right hinv hp
  simp only [abs_zero, neg_zero, mul_zero, zero_mul, add_zero, sub_zero, one_mul,
    mul_one, one_pow] at h
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith


/-- The cutoff error has finite spatial integral. -/
theorem c16_cutoff_gradient_square_integrable {d : ℕ} {R : ℝ}
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))
      (volume.restrict (sourceBall 0 R)) := by
  have hi (j : Fin d) : MemLp (fun x => fderiv ℝ χ x (unitVector j)) 2 volume :=
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hχc.fderiv_apply ℝ (unitVector j))
  have hs : Integrable (fun x => ∑ j : Fin d, (fderiv ℝ χ x (unitVector j)) ^ 2) volume :=
    integrable_finsetSum Finset.univ (fun j _ => (hi j).integrable_sq)
  simpa only [euclideanSq, dot, pow_two] using hs.mono_measure (Measure.restrict_le_self (s := sourceBall (0 : Vec d) R))

/-- The coefficient cutoff bound holds after integration in space, for almost
 every time in the cylinder. -/
theorem c16_weighted_caloric_log_spatial_energy_bound {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (κ / 2) * (∫ x in sourceBall 0 R, χ x ^ 2 * euclideanSq ((u (t,x))⁻¹ • G (t,x))) ≤
      (∫ x in sourceBall 0 R, χ x ^ 2 * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) -
        2 * χ x * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) (fun j => fderiv ℝ χ x (unitVector j))) +
      (2 / κ ^ 3) * (∫ x in sourceBall 0 R, euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  have hd := (c16_weighted_caloric_log_dissipation_integrable hε ρ α u G hcal hpositive χ hχ hχc).1
  have hep := (c16_weighted_caloric_log_energy_integrable hκ hε ρ α hell u G hcal hpositive χ hχ hχc).1
  have hx := (c16_weighted_caloric_log_cutoff_flux_integrable hκ hε ρ α hell u G hcal hpositive χ hχ hχc).1
  have he : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z) -
      2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
    convert hep.sub (hx.const_mul 2) using 1 <;> ext z <;> simp only [Pi.sub_apply] <;> ring
  have hd' : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 * euclideanSq ((u z)⁻¹ • G z))
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall 0 R))) := by
    rw [Measure.prod_restrict]
    exact hd
  have he' : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z) -
      2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall 0 R))) := by
    rw [Measure.prod_restrict]
    exact he
  have hp := c16_cutoff_gradient_square_integrable (R := R) χ hχ hχc
  filter_upwards [hd'.prod_right_ae, he'.prod_right_ae] with t ht hte
  have hm := integral_mono (ht.const_mul (κ / 2)) (hte.add (hp.const_mul (2 / κ ^ 3)))
    (fun x => by
      simp only [Pi.add_apply]
      have h := c16_log_energy_cutoff_bound hκ hell x ((u (t,x))⁻¹ • G (t,x))
        (fun j => fderiv ℝ χ x (unitVector j)) (-χ x)
      have hs : dot ((u (t,x))⁻¹ • G (t,x)) ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) =
          dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) := by
        simp only [dot, mul_comm]
      rw [hs] at h
      nlinarith)
  simp only [Pi.add_apply] at hm
  simpa only [integral_const_mul, integral_add hte (hp.const_mul (2 / κ ^ 3))] using hm




/-- The signed energy appearing as the derivative of the logarithmic mass is
integrable in time. -/
theorem c16_weighted_caloric_log_signed_energy_time_integrable {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun t => ∫ x in sourceBall 0 R,
      χ x ^ 2 * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) -
      2 * χ x * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) (fun j => fderiv ℝ χ x (unitVector j)))
      (volume.restrict (Set.Ioo a b)) := by
  have hep := (c16_weighted_caloric_log_energy_integrable hκ hε ρ α hell u G hcal hpositive χ hχ hχc).1
  have hx := (c16_weighted_caloric_log_cutoff_flux_integrable hκ hε ρ α hell u G hcal hpositive χ hχ hχc).1
  have he : Integrable (fun z : ℝ × Vec d => χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z) -
      2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) (fun j => fderiv ℝ χ z.2 (unitVector j)))
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall 0 R))) := by
    rw [Measure.prod_restrict]
    convert hep.sub (hx.const_mul 2) using 1 <;> ext z <;> simp only [Pi.sub_apply] <;> ring
  exact he.integral_prod_left

/-- The signed logarithmic cutoff bound integrated over any ordered
subinterval of the cylinder. -/
theorem c16_weighted_caloric_log_interval_energy_bound {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hpositive : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hst : s ≤ t) :
    (κ / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * euclideanSq ((u (q,x))⁻¹ • G (q,x))) ≤
    (∫ q in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * dot ((α x).mulVec ((u (q,x))⁻¹ • G (q,x))) ((u (q,x))⁻¹ • G (q,x)) -
      2 * χ x * dot ((α x).mulVec ((u (q,x))⁻¹ • G (q,x))) (fun j => fderiv ℝ χ x (unitVector j))) +
    (2 / κ ^ 3) * (t-s) * (∫ x in sourceBall 0 R,
      euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  let D : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * euclideanSq ((u (q,x))⁻¹ • G (q,x))
  let Q : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * dot ((α x).mulVec ((u (q,x))⁻¹ • G (q,x))) ((u (q,x))⁻¹ • G (q,x)) -
    2 * χ x * dot ((α x).mulVec ((u (q,x))⁻¹ • G (q,x))) (fun j => fderiv ℝ χ x (unitVector j))
  let C : ℝ := (2 / κ ^ 3) * ∫ x in sourceBall 0 R,
    euclideanSq (fun j => fderiv ℝ χ x (unitVector j))
  have hsub : Set.Icc s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_of_lt_of_le hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  have hD : IntegrableOn D (Set.Ioo a b) volume :=
    (c16_weighted_caloric_log_dissipation_integrable hε ρ α u G hcal hpositive χ hχ hχc).2
  have hQ : IntegrableOn Q (Set.Ioo a b) volume :=
    c16_weighted_caloric_log_signed_energy_time_integrable hκ hε ρ α hell u G hcal hpositive χ hχ hχc
  have hdi : IntervalIntegrable D volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hD.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hqi : IntervalIntegrable Q volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hQ.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hbound : ∀ᵐ q ∂volume.restrict (Set.Icc s t), (κ / 2) * D q ≤ Q q + C :=
    (c16_weighted_caloric_log_spatial_energy_bound hκ hε ρ α hell u G hcal hpositive χ hχ hχc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hm := intervalIntegral.integral_mono_ae_restrict hst (hdi.const_mul (κ / 2))
    (hqi.add intervalIntegrable_const) hbound
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hqi intervalIntegrable_const] at hm
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hm
  dsimp only [D, Q, C] at hm ⊢
  nlinarith


/-- A distributional logarithmic balance yields a continuous trace and the
integrated cutoff estimate, using the scalar weak-derivative primitive. -/
theorem c16_weighted_log_energy_of_distributional
    (hprimitive : ∀ {a b : ℝ}, a < b → ∀ {f g : ℝ → ℝ},
      IntegrableOn f (Set.Ioo a b) volume → IntegrableOn g (Set.Ioo a b) volume →
      (∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
        tsupport η ⊆ Set.Ioo a b →
        (∫ t in Set.Ioo a b, f t * deriv η t) =
          -(∫ t in Set.Ioo a b, g t * η t)) →
      ∃ C : ℝ, f =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => C + ∫ q in a..t, g q)
    {d : ℕ} {κ R a b ε : ℝ} (hκ : 0 < κ) (hab : a < b) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      (∫ t in Set.Ioo a b, (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))) * deriv η t) =
      -(∫ t in Set.Ioo a b, (∫ x in sourceBall 0 R,
        χ x ^ 2 * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) -
        2 * χ x * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x)))
          (fun j => fderiv ℝ χ x (unitVector j))) * η t)) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((u (q,x))⁻¹ • G (q,x))) ≤
        E t - E s + (2 / κ ^ 3) * (t-s) *
          (∫ x in sourceBall 0 R, euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  let f : ℝ → ℝ := fun t => ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))
  let g : ℝ → ℝ := fun t => ∫ x in sourceBall 0 R,
    χ x ^ 2 * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) -
    2 * χ x * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) (fun j => fderiv ℝ χ x (unitVector j))
  have hf : IntegrableOn f (Set.Ioo a b) volume :=
    (c16_weighted_caloric_log_mass_integrable hκ hε ρ α hell u G hcal hu χ hχ hχc).2
  have hg : IntegrableOn g (Set.Ioo a b) volume :=
    c16_weighted_caloric_log_signed_energy_time_integrable hκ hε ρ α hell u G hcal hu χ hχ hχc
  obtain ⟨C, hC⟩ := hprimitive hab hf hg hweak
  have hgcc : IntegrableOn g (Set.Icc a b) volume := by
    rwa [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  have hi : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    rwa [IntegrableOn, ← Measure.restrict_congr_set (μ := volume) Ioo_ae_eq_Ioc]
  refine ⟨fun t => C + ∫ q in a..t, g q, ?_, hC.symm, ?_⟩
  · have hc : ContinuousOn (fun x => ∫ q in a..x, g q) (Set.Icc a b) :=
      (intervalIntegral.continuousOn_primitive hgcc).congr
        (fun x hx => by rw [intervalIntegral.integral_of_le hx.1])
    exact (continuousOn_const.add hc).mono Set.Ioo_subset_Icc_self
  · intro s hs t ht hst
    have hs' : s ∈ Set.uIcc a b := by simpa [Set.uIcc_of_le hab.le] using ⟨hs.1.le, hs.2.le⟩
    have ht' : t ∈ Set.uIcc a b := by simpa [Set.uIcc_of_le hab.le] using ⟨ht.1.le, ht.2.le⟩
    have his := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs')
    have hit := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht')
    have hadd := intervalIntegral.integral_interval_sub_left hit his
    have hb := c16_weighted_caloric_log_interval_energy_bound hκ hε ρ α hell u G hcal hu χ hχ hχc hs ht hst
    change _ ≤ (C + ∫ q in a..t, g q) - (C + ∫ q in a..s, g q) + _
    change _ ≤ (∫ q in s..t, g q) + _ at hb
    linarith


/-- The logarithmic distributional balance has a continuous representative,
using the native scalar weak-derivative primitive. -/
theorem c16_weighted_log_energy_of_distributional_native
    {d : ℕ} {κ R a b ε : ℝ} (hκ : 0 < κ) (hab : a < b) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      (∫ t in Set.Ioo a b, (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))) * deriv η t) =
      -(∫ t in Set.Ioo a b, (∫ x in sourceBall 0 R,
        χ x ^ 2 * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x))) ((u (t,x))⁻¹ • G (t,x)) -
        2 * χ x * dot ((α x).mulVec ((u (t,x))⁻¹ • G (t,x)))
          (fun j => fderiv ℝ χ x (unitVector j))) * η t)) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((u (q,x))⁻¹ • G (q,x))) ≤
        E t - E s + (2 / κ ^ 3) * (t-s) *
          (∫ x in sourceBall 0 R, euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  exact c16_weighted_log_energy_of_distributional
    (fun {_ _} hab {_ _} hf hg hw => c13_w11_ae_eq_ac_representative hab hf hg hw)
    hκ hab hε ρ α hell u G hcal hu χ hχ hχc hweak


/-- Algebra for the logarithmic chain rule with a separated square test. -/
theorem c16_log_chain_flux_identity {d : ℕ} (A : Mat d) (V D : Vec d)
    (r η χ : ℝ) :
    r * dot (A.mulVec V) (fun j => η * (2 * χ * D j)) -
      r ^ 2 * dot (A.mulVec V) V * (η * χ ^ 2) =
    η * (2 * χ * dot (A.mulVec (r • V)) D -
      χ ^ 2 * dot (A.mulVec (r • V)) (r • V)) := by
  simp only [Matrix.mulVec_smul, dot, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring


/-- Specialization of the renormalized chain rule to a separated logarithmic
cutoff test. -/
theorem c16_normalized_log_separated_balance
    (hchain : ∀ {d : ℕ} {κ R a b : ℝ}, 0 < κ → 0 < R → a < b →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G →
      ∀ (F : ℝ → ℝ), ContDiff ℝ 2 F → F 0 = 0 →
      ∀ M : ℝ, 0 ≤ M → (∀ r, |deriv (deriv F) r| ≤ M) →
      ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
      (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0)
    {d : ℕ} {κ R a b ε : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηI : tsupport η ⊆ Set.Ioo a b) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * (Real.log (u z) - c16LogExtension ε 0)) * (deriv η z.1 * χ z.2 ^ 2) +
      η z.1 * (2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
          (fun j => fderiv ℝ χ z.2 (unitVector j)) -
        χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z))) = 0 := by
  obtain ⟨hF, hF0, ⟨M, hM, hd⟩, hval, hder, hder2⟩ := c16_normalized_log_properties hε
  let ψ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hψ := c5_separated_square_cutoff η hη hηc hηI χ hχ hχc hχU
  have hc := hchain hκ hR hab ρ α hell u G hcal (c16NormalizedLog ε) hF hF0 M hM
    (fun r => (hd r).2) ψ hψ.1 hψ.2.1 hψ.2.2
  have heq : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * c16NormalizedLog ε (u z)) * fderiv ℝ ψ z (1,0) +
      deriv (c16NormalizedLog ε) (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv (c16NormalizedLog ε)) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) =
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * (Real.log (u z) - c16LogExtension ε 0)) * (deriv η z.1 * χ z.2 ^ 2) +
      η z.1 * (2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
          (fun j => fderiv ℝ χ z.2 (unitVector j)) -
        χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z))) := by
    apply integral_congr_ae
    filter_upwards [hu] with z hz
    dsimp only [ψ]
    rw [hval _ hz, hder _ hz, hder2 _ hz,
      c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by norm_cast))
        χ (hχ.differentiable (by norm_cast)) z]
    simp_rw [c5_separated_square_cutoff_fderiv η (hη.differentiable (by norm_cast))
      χ (hχ.differentiable (by norm_cast)) z]
    rw [← inv_pow]
    have hflux := c16_log_chain_flux_identity (α z.2) (G z)
      (fun j => fderiv ℝ χ z.2 (unitVector j)) (u z)⁻¹ (η z.1) (χ z.2)
    linarith
  rw [← heq]
  exact hc


/-- The time-independent density times the square cutoff is integrable on
the finite cylinder. -/
theorem c16_density_cutoff_integrable {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  letI : IsFiniteMeasure (volume.restrict (sourceBall (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (c9_sourceBall_measure_ne_top 0 R)
  have hp : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))) := inferInstance
  haveI : IsFiniteMeasure μ := by
    rw [Measure.prod_restrict] at hp
    exact hp
  obtain ⟨hρ, _⟩ := EinsteinFull.Blueprint.TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell (Measure.map Prod.snd μ)
  have hρ' : MemLp (fun z : ℝ × Vec d => ρ z.2) ⊤ μ :=
    hρ.comp_of_map measurable_snd.aemeasurable
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχ' : MemLp (fun z : ℝ × Vec d => χ z.2) ⊤ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hχ2 : MemLp ((fun z : ℝ × Vec d => χ z.2) * (fun z => χ z.2)) ⊤ μ := hχ'.mul hχ'
  have htop : MemLp ((fun z : ℝ × Vec d => ρ z.2) * ((fun z => χ z.2) * (fun z => χ z.2))) ⊤ μ := hρ'.mul hχ2
  have h := htop.mono_exponent (show (1 : ℝ≥0∞) ≤ ⊤ by simp)
  convert h.integrable (by simp) using 1 <;> ext z <;> simp only [Pi.mul_apply, pow_two] <;> ring


/-- A spacetime balance for integrable mass and energy gives the corresponding
distributional identity after spatial integration. -/
theorem c16_spacetime_balance_to_time_test {d : ℕ} (I : Set ℝ) (U : Set (Vec d))
    (f g : ℝ × Vec d → ℝ)
    (hf : Integrable f (volume.restrict (I ×ˢ U)))
    (hg : Integrable g (volume.restrict (I ×ˢ U)))
    (w v : ℝ → ℝ)
    (hw : MemLp (fun z : ℝ × Vec d => w z.1) ∞ (volume.restrict (I ×ˢ U)))
    (hv : MemLp (fun z : ℝ × Vec d => v z.1) ∞ (volume.restrict (I ×ˢ U)))
    (hbal : (∫ z in I ×ˢ U, -(w z.1 * f z) - v z.1 * g z) = 0) :
    (∫ t in I, (∫ x in U, f (t,x)) * w t) =
      -(∫ t in I, (∫ x in U, g (t,x)) * v t) := by
  have hfw : Integrable (fun z : ℝ × Vec d => w z.1 * f z)
      (volume.restrict (I ×ˢ U)) := by
    convert hf.mul_of_top_left hw using 1 <;> ext z <;> simp only [Pi.mul_apply, mul_comm]
  have hgv : Integrable (fun z : ℝ × Vec d => v z.1 * g z)
      (volume.restrict (I ×ˢ U)) := by
    convert hg.mul_of_top_left hv using 1 <;> ext z <;> simp only [Pi.mul_apply, mul_comm]
  change (∫ z, ((-(fun z => w z.1 * f z)) - (fun z => v z.1 * g z)) z ∂(volume.restrict (I ×ˢ U))) = 0 at hbal
  simp only [Pi.sub_apply] at hbal
  rw [integral_sub hfw.neg hgv] at hbal
  simp only [Pi.neg_apply] at hbal
  rw [integral_neg,
    c5_integral_time_multiplier_spacetime I U f hf w hw,
    c5_integral_time_multiplier_spacetime I U g hg v hv] at hbal
  simp_rw [mul_comm (w _), mul_comm (v _)] at hbal
  linarith


/-- Remove a constant logarithmic normalization from a spacetime balance. -/
theorem c16_denormalize_spacetime_balance {d : ℕ} {a b R : ℝ}
    (ρ : Vec d → ℝ) (hρ : Measurable ρ) (C : ℝ) (hρbound : ∀ x, ‖ρ x‖ ≤ C)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηI : tsupport η ⊆ Set.Ioo a b)
    (f g : ℝ × Vec d → ℝ) (c : ℝ)
    (hf : Integrable f (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hg : Integrable g (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hk : Integrable (fun z : ℝ × Vec d => ρ z.2 * χ z.2 ^ 2)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hw : MemLp (fun z : ℝ × Vec d => deriv η z.1) ∞
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hv : MemLp (fun z : ℝ × Vec d => η z.1) ∞
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hbal : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(deriv η z.1 * (f z - c * (ρ z.2 * χ z.2 ^ 2))) - η z.1 * g z) = 0) :
    (∫ t in Set.Ioo a b, (∫ x in sourceBall 0 R, f (t,x)) * deriv η t) =
      -(∫ t in Set.Ioo a b, (∫ x in sourceBall 0 R, g (t,x)) * η t) := by
  let I := Set.Ioo a b
  let U := sourceBall (0 : Vec d) R
  let μ := volume.restrict (I ×ˢ U)
  let k : ℝ × Vec d → ℝ := fun z => ρ z.2 * χ z.2 ^ 2
  have hψ := c5_separated_square_cutoff η hη hηc hηI χ hχ hχc hχU
  have hz := c11_density_time_derivative_integral_zero_on ρ hρ C hρbound I U
    (fun z : ℝ × Vec d => η z.1 * χ z.2 ^ 2) hψ.1 hψ.2.1 hψ.2.2
  have hz' : (∫ z in I ×ˢ U, deriv η z.1 * k z) = 0 := by
    calc
      (∫ z in I ×ˢ U, deriv η z.1 * k z) =
          ∫ z in I ×ˢ U, ρ z.2 * fderiv ℝ (fun z : ℝ × Vec d => η z.1 * χ z.2 ^ 2) z (1,0) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by norm_cast))
              χ (hχ.differentiable (by norm_cast)) z]
            dsimp [k]
            ring
      _ = 0 := hz
  have hfw : Integrable (fun z : ℝ × Vec d => deriv η z.1 * f z) μ := by
    convert hf.mul_of_top_left hw using 1 <;> ext z <;> simp only [Pi.mul_apply, mul_comm]
  have hgv : Integrable (fun z : ℝ × Vec d => η z.1 * g z) μ := by
    convert hg.mul_of_top_left hv using 1 <;> ext z <;> simp only [Pi.mul_apply, mul_comm]
  have hkw : Integrable (fun z : ℝ × Vec d => deriv η z.1 * k z) μ := by
    convert hk.mul_of_top_left hw using 1 <;> ext z <;> simp only [Pi.mul_apply, mul_comm, k]
  have hbalance : (∫ z in I ×ˢ U, -(deriv η z.1 * f z) - η z.1 * g z) = 0 := by
    have heq : (∫ z in I ×ˢ U,
        -(deriv η z.1 * (f z - c * k z)) - η z.1 * g z) =
        (∫ z in I ×ˢ U, (-(deriv η z.1 * f z) - η z.1 * g z) +
          c * (deriv η z.1 * k z)) := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    rw [heq] at hbal
    change (∫ z, (((-(fun z => deriv η z.1 * f z)) - (fun z => η z.1 * g z)) +
      c • (fun z => deriv η z.1 * k z)) z ∂μ) = 0 at hbal
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hbal
    rw [integral_add (hfw.neg.sub hgv) (hkw.const_mul c)] at hbal
    rw [integral_const_mul, hz', mul_zero, add_zero] at hbal
    exact hbal
  exact c16_spacetime_balance_to_time_test I U f g hf hg (deriv η) η hw hv hbalance


/-- A renormalized caloric chain rule gives the weighted logarithmic energy
balance with a continuous representative. -/
theorem c16_weighted_caloric_log_energy_balance_of_renormalization
    (hchain : ∀ {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M),
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0)
 {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((u (q,x))⁻¹ • G (q,x))) ≤
        E t - E s + (2 / κ ^ 3) * (t-s) *
          (∫ x in sourceBall 0 R,
            euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  apply c16_weighted_log_energy_of_distributional_native hκ hab hε ρ α hell u G hcal hu χ hχ hχc
  intro η hη hηc hηI
  let I := Set.Ioo a b
  let U := sourceBall (0 : Vec d) R
  let μ := volume.restrict (I ×ˢ U)
  let f : ℝ × Vec d → ℝ := fun z => ρ z.2 * χ z.2 ^ 2 * Real.log (u z)
  let g : ℝ × Vec d → ℝ := fun z =>
    χ z.2 ^ 2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z)) ((u z)⁻¹ • G z) -
      2 * χ z.2 * dot ((α z.2).mulVec ((u z)⁻¹ • G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j))
  have hf : Integrable f μ :=
    (c16_weighted_caloric_log_mass_integrable hκ hε ρ α hell u G hcal hu χ hχ hχc).1
  have hep := (c16_weighted_caloric_log_energy_integrable hκ hε ρ α hell u G hcal hu χ hχ hχc).1
  have hx := (c16_weighted_caloric_log_cutoff_flux_integrable hκ hε ρ α hell u G hcal hu χ hχ hχc).1
  have hg : Integrable g μ := by
    convert hep.sub (hx.const_mul 2) using 1 <;> ext z <;> simp only [Pi.sub_apply] <;> dsimp [g] <;> ring
  have hk := c16_density_cutoff_integrable (R := R) (a := a) (b := b) hκ ρ α hell χ hχ hχc
  have hηd := hη.continuous_deriv (by norm_cast)
  obtain ⟨B, hB⟩ := hηc.deriv.exists_bound_of_continuous hηd
  have hw : MemLp (fun z : ℝ × Vec d => deriv η z.1) ∞ μ := by
    apply memLp_top_of_bound (hηd.comp continuous_fst).aestronglyMeasurable B
    exact ae_of_all μ (fun z => hB z.1)
  obtain ⟨D, hD⟩ := hηc.exists_bound_of_continuous hη.continuous
  have hv : MemLp (fun z : ℝ × Vec d => η z.1) ∞ μ := by
    apply memLp_top_of_bound (hη.continuous.comp continuous_fst).aestronglyMeasurable D
    exact ae_of_all μ (fun z => hD z.1)
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hb0 := c16_normalized_log_separated_balance hchain hκ hR hab hε ρ α hell u G hcal hu χ hχ hχc hχU η hη hηc hηI
  have hb : (∫ z in I ×ˢ U,
      -(deriv η z.1 * (f z - c16LogExtension ε 0 * (ρ z.2 * χ z.2 ^ 2))) - η z.1 * g z) = 0 := by
    convert hb0 using 1
    apply integral_congr_ae
    filter_upwards with z
    dsimp [f, g]
    ring
  exact c16_denormalize_spacetime_balance ρ hell.1 κ⁻¹ hρbound χ hχ hχc hχU η hη hηc hηI
    f g (c16LogExtension ε 0) hf hg hk hw hv hb


/-- The weighted logarithmic energy balance follows from caloric renormalization. -/
theorem c16_weighted_caloric_log_energy_balance
 {d : ℕ}
    {κ R a b ε : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b) (hε : 0 < ε)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.log (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * euclideanSq ((u (q,x))⁻¹ • G (q,x))) ≤
        E t - E s + (2 / κ ^ 3) * (t-s) *
          (∫ x in sourceBall 0 R,
            euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  exact c16_weighted_caloric_log_energy_balance_of_renormalization
    (fun hκ hR hab ρ α hell u G hcal F hF hF0 M hM hder =>
      c13_actual_weighted_caloric_renormalization hκ hR hab ρ α hell u G hcal F hF hF0 M hM hder)
    hκ hR hab hε ρ α hell u G hcal hu χ hχ hχc hχU

end

end EinsteinFull.Calculus
