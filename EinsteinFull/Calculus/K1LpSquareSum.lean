import Homogenization.Probability.IndependentSums.Rosenthal.Corollaries
import Mathlib
open MeasureTheory ProbabilityTheory
namespace EinsteinFull.Calculus.K1

/-- The constant `2 p + 4 C_B √p` of the ℓ²-form `Lᵖ` bound for sums of independent centred
variables, obtained from the real-exponent Rosenthal inequality. -/
noncomputable def lpSqConst (p : ℝ) : ℝ :=
  2 * p + 4 * Homogenization.IndependentSums.rosenthalBennettIntegralConst * Real.sqrt p

theorem toReal_eLpNorm_rpow {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] {f : Ω → E} {q : ℝ} (hq : 0 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ) :
    (eLpNorm f (ENNReal.ofReal q) μ).toReal ^ q = ∫ ω, ‖f ω‖ ^ q ∂μ := by
  have h0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have h1 : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hf.eLpNorm_eq_integral_rpow_norm h0 h1, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal hq.le]
  · exact Real.rpow_inv_rpow (integral_nonneg fun _ => by positivity) hq.ne'
  · exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _

theorem lp_le_l2 {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {p : ℝ}
    (hp : 2 ≤ p) :
    (∑ i ∈ s, a i ^ p) ^ p⁻¹ ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  set t := Real.sqrt (∑ i ∈ s, a i ^ 2) with ht
  have hS : 0 ≤ ∑ i ∈ s, a i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hp0 : 0 < p := by linarith
  have hle : ∀ i ∈ s, a i ^ p ≤ a i ^ 2 * t ^ (p - 2) := by
    intro i hi
    have hat : a i ≤ t := by
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (f := fun i => a i ^ 2) (fun j _ => by positivity) hi
    have : a i ^ p = a i ^ (2:ℝ) * a i ^ (p - 2) := by
      rw [← Real.rpow_add' (ha i) (by linarith)]; ring_nf
    rw [this, Real.rpow_two]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ha i) hat (by linarith)) (by positivity)
  have hsum : ∑ i ∈ s, a i ^ p ≤ t ^ p := by
    calc ∑ i ∈ s, a i ^ p ≤ ∑ i ∈ s, a i ^ 2 * t ^ (p - 2) := Finset.sum_le_sum hle
      _ = t ^ 2 * t ^ (p - 2) := by
        rw [← Finset.sum_mul, ht, Real.sq_sqrt hS]
      _ = t ^ p := by
        rw [← Real.rpow_two, ← Real.rpow_add' ht0 (by linarith)]; ring_nf
  calc (∑ i ∈ s, a i ^ p) ^ p⁻¹ ≤ (t ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _) hsum (by positivity)
    _ = t := Real.rpow_rpow_inv ht0 hp0.ne'

theorem real_eLpNorm_sum_le_sqrt_sum_sq {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} (s : Finset ι) {p : ℝ}
    (hp : 2 ≤ p) (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (hLp : ∀ i, MemLp (X i) (ENNReal.ofReal p) μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (eLpNorm (∑ i ∈ s, X i) (ENNReal.ofReal p) μ).toReal ≤
      lpSqConst p * Real.sqrt (∑ i ∈ s, (eLpNorm (X i) (ENNReal.ofReal p) μ).toReal ^ 2) := by
  have hp0 : 0 < p := by linarith
  set a : ι → ℝ := fun i => (eLpNorm (X i) (ENNReal.ofReal p) μ).toReal with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have hC : 0 ≤ Homogenization.IndependentSums.rosenthalBennettIntegralConst := by
    unfold Homogenization.IndependentSums.rosenthalBennettIntegralConst; positivity
  have hq : 0 ≤ lpSqConst p := by unfold lpSqConst; positivity
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty, eLpNorm_zero, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero, le_refl]
  have hLps : MemLp (∑ i ∈ s, X i) (ENNReal.ofReal p) μ :=
    memLp_finsetSum' s fun i _ => hLp i
  have hrp : ∀ i, ∫ ω, |X i ω| ^ p ∂μ = a i ^ p := fun i => by
    rw [ha]; simp only
    rw [toReal_eLpNorm_rpow hp0 (hLp i)]; simp [Real.norm_eq_abs]
  have hint : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ := by
    intro i _
    have := (hLp i).integrable_norm_rpow (by simpa using hp0) ENNReal.ofReal_ne_top
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using this
  have key := Homogenization.IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
    (μ := μ) hs hp h_indep h_meas hint (fun i _ => hmean i)
  have hLHS : (eLpNorm (∑ i ∈ s, X i) (ENNReal.ofReal p) μ).toReal =
      (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ p⁻¹ := by
    have := toReal_eLpNorm_rpow hp0 hLps
    rw [← Real.rpow_rpow_inv (ENNReal.toReal_nonneg (a := eLpNorm (∑ i ∈ s, X i) (ENNReal.ofReal p) μ)) hp0.ne', this]
    simp [Real.norm_eq_abs, Finset.sum_apply]
  have hmom : ∀ i, ProbabilityTheory.moment (X i) 2 μ ≤ a i ^ 2 := by
    intro i
    have h2 : MemLp (X i) (ENNReal.ofReal 2) μ :=
      (hLp i).mono_exponent (by gcongr)
    have e2 := toReal_eLpNorm_rpow (by norm_num : (0:ℝ) < 2) h2
    have hfin : eLpNorm (X i) (ENNReal.ofReal p) μ ≠ ⊤ := (hLp i).eLpNorm_ne_top
    have hmono : (eLpNorm (X i) (ENNReal.ofReal 2) μ).toReal ≤ a i :=
      ENNReal.toReal_mono hfin (eLpNorm_le_eLpNorm_of_exponent_le (by gcongr))
    have : ProbabilityTheory.moment (X i) 2 μ =
        (eLpNorm (X i) (ENNReal.ofReal 2) μ).toReal ^ (2:ℝ) := by
      rw [e2, ProbabilityTheory.moment]
      simp [Real.norm_eq_abs, sq_abs]
    rw [this, Real.rpow_two]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hmono 2
  have h1 : (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) := by
    simp_rw [hrp]; exact lp_le_l2 s a ha0 hp
  have h2 : Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2) :=
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => hmom i)
  rw [hLHS]
  refine key.trans ?_
  unfold lpSqConst
  have hsp := Real.sqrt_nonneg p
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * p),
    mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC) hsp)]


theorem complex_eLpNorm_sum_le_sqrt_sum_sq {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ι → Ω → ℂ} (s : Finset ι) {p : ℝ}
    (hp : 2 ≤ p) (h_indep : iIndepFun f μ) (h_meas : ∀ i, Measurable (f i))
    (hLp : ∀ i, MemLp (f i) (ENNReal.ofReal p) μ) (hmean : ∀ i, ∫ ω, f i ω ∂μ = 0) :
    (eLpNorm (∑ i ∈ s, f i) (ENNReal.ofReal p) μ).toReal ≤
      2 * lpSqConst p *
        Real.sqrt (∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ).toReal ^ 2) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa using (by linarith : (1:ℝ) ≤ p)
  set X : ι → Ω → ℝ := fun i ω => (f i ω).re with hX
  set Y : ι → Ω → ℝ := fun i ω => (f i ω).im with hY
  have hXi : iIndepFun X μ := h_indep.comp (fun _ => Complex.re) (fun _ => Complex.measurable_re)
  have hYi : iIndepFun Y μ := h_indep.comp (fun _ => Complex.im) (fun _ => Complex.measurable_im)
  have hXm : ∀ i, Measurable (X i) := fun i => Complex.measurable_re.comp (h_meas i)
  have hYm : ∀ i, Measurable (Y i) := fun i => Complex.measurable_im.comp (h_meas i)
  have hXL : ∀ i, MemLp (X i) (ENNReal.ofReal p) μ := fun i => (hLp i).re
  have hYL : ∀ i, MemLp (Y i) (ENNReal.ofReal p) μ := fun i => (hLp i).im
  have hXmean : ∀ i, ∫ ω, X i ω ∂μ = 0 := fun i => by
    have := integral_re ((hLp i).integrable hp1) (μ := μ)
    simp only [RCLike.re_to_complex] at this
    simp only [hX]; rw [this, hmean i]; simp
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := fun i => by
    have := integral_im ((hLp i).integrable hp1) (μ := μ)
    simp only [RCLike.im_to_complex] at this
    simp only [hY]; rw [this, hmean i]; simp
  have rX := real_eLpNorm_sum_le_sqrt_sum_sq s hp hXi hXm hXL hXmean
  have rY := real_eLpNorm_sum_le_sqrt_sum_sq s hp hYi hYm hYL hYmean
  set a : ι → ℝ := fun i => (eLpNorm (f i) (ENNReal.ofReal p) μ).toReal with ha
  have hXa : ∀ i, (eLpNorm (X i) (ENNReal.ofReal p) μ).toReal ≤ a i := fun i =>
    ENNReal.toReal_mono (hLp i).eLpNorm_ne_top
      (eLpNorm_mono (hXL i).aestronglyMeasurable fun ω => by simpa [hX] using Complex.abs_re_le_norm (f i ω))
  have hYa : ∀ i, (eLpNorm (Y i) (ENNReal.ofReal p) μ).toReal ≤ a i := fun i =>
    ENNReal.toReal_mono (hLp i).eLpNorm_ne_top
      (eLpNorm_mono (hYL i).aestronglyMeasurable fun ω => by simpa [hY] using Complex.abs_im_le_norm (f i ω))
  have hsq : ∀ (Z : ι → Ω → ℝ), (∀ i, (eLpNorm (Z i) (ENNReal.ofReal p) μ).toReal ≤ a i) →
      Real.sqrt (∑ i ∈ s, (eLpNorm (Z i) (ENNReal.ofReal p) μ).toReal ^ 2) ≤
        Real.sqrt (∑ i ∈ s, a i ^ 2) := fun Z hZ =>
    Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ ENNReal.toReal_nonneg (hZ i) 2)
  have hq : 0 ≤ lpSqConst p := by
    unfold lpSqConst Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have : 0 ≤ p := by linarith
    positivity
  have hXs : MemLp (∑ i ∈ s, X i) (ENNReal.ofReal p) μ := memLp_finsetSum' s fun i _ => hXL i
  have hYs : MemLp (∑ i ∈ s, Y i) (ENNReal.ofReal p) μ := memLp_finsetSum' s fun i _ => hYL i
  set g1 : Ω → ℂ := fun ω => ((∑ i ∈ s, X i) ω : ℝ) with hg1
  set g2 : Ω → ℂ := fun ω => ((∑ i ∈ s, Y i) ω : ℝ) * Complex.I with hg2
  have hsum : (∑ i ∈ s, f i) = g1 + g2 := by
    funext ω
    simp only [hg1, hg2, hX, hY, Pi.add_apply, Finset.sum_apply, Complex.ofReal_sum]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Complex.re_add_im (f i ω)).symm
  have hg1m : AEStronglyMeasurable g1 μ := (Complex.continuous_ofReal.comp_aestronglyMeasurable hXs.aestronglyMeasurable)
  have hg2m : AEStronglyMeasurable g2 μ :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hYs.aestronglyMeasurable).mul_const _
  have e1 : eLpNorm g1 (ENNReal.ofReal p) μ ≤ eLpNorm (∑ i ∈ s, X i) (ENNReal.ofReal p) μ :=
    eLpNorm_mono hg1m fun ω => by simp [hg1, ← Complex.ofReal_sum]
  have e2 : eLpNorm g2 (ENNReal.ofReal p) μ ≤ eLpNorm (∑ i ∈ s, Y i) (ENNReal.ofReal p) μ :=
    eLpNorm_mono hg2m fun ω => by simp [hg2, ← Complex.ofReal_sum]
  have f1 : eLpNorm g1 (ENNReal.ofReal p) μ ≠ ⊤ := ne_top_of_le_ne_top hXs.eLpNorm_ne_top e1
  have f2 : eLpNorm g2 (ENNReal.ofReal p) μ ≠ ⊤ := ne_top_of_le_ne_top hYs.eLpNorm_ne_top e2
  have tri : eLpNorm (∑ i ∈ s, f i) (ENNReal.ofReal p) μ ≤
      eLpNorm g1 (ENNReal.ofReal p) μ + eLpNorm g2 (ENNReal.ofReal p) μ := by
    rw [hsum]; exact eLpNorm_add_le hp1
  have tri' : (eLpNorm (∑ i ∈ s, f i) (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (∑ i ∈ s, X i) (ENNReal.ofReal p) μ).toReal +
        (eLpNorm (∑ i ∈ s, Y i) (ENNReal.ofReal p) μ).toReal := by
    calc _ ≤ (eLpNorm g1 (ENNReal.ofReal p) μ + eLpNorm g2 (ENNReal.ofReal p) μ).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨f1, f2⟩) tri
      _ = (eLpNorm g1 (ENNReal.ofReal p) μ).toReal + (eLpNorm g2 (ENNReal.ofReal p) μ).toReal :=
          ENNReal.toReal_add f1 f2
      _ ≤ _ := add_le_add (ENNReal.toReal_mono hXs.eLpNorm_ne_top e1)
          (ENNReal.toReal_mono hYs.eLpNorm_ne_top e2)
  have h1 := rX.trans (mul_le_mul_of_nonneg_left (hsq X hXa) hq)
  have h2 := rY.trans (mul_le_mul_of_nonneg_left (hsq Y hYa) hq)
  linarith


theorem complex_eLpNorm_sum_le_colored {Ω ι κ : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype κ] (col : ι → κ)
    {f : ι → Ω → ℂ} (s : Finset ι) {p : ℝ} (hp : 2 ≤ p)
    (h_indep : ∀ c : κ, iIndepFun (fun i : {i : ι // col i = c} => f i) μ)
    (h_meas : ∀ i, Measurable (f i))
    (hLp : ∀ i, MemLp (f i) (ENNReal.ofReal p) μ) (hmean : ∀ i, ∫ ω, f i ω ∂μ = 0) :
    (eLpNorm (∑ i ∈ s, f i) (ENNReal.ofReal p) μ).toReal ≤
      2 * lpSqConst p * Real.sqrt (Fintype.card κ) *
        Real.sqrt (∑ i ∈ s, (eLpNorm (f i) (ENNReal.ofReal p) μ).toReal ^ 2) := by
  classical
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa using (by linarith : (1:ℝ) ≤ p)
  set a : ι → ℝ := fun i => (eLpNorm (f i) (ENNReal.ofReal p) μ).toReal with ha
  set K := 2 * lpSqConst p with hK
  have hq : 0 ≤ lpSqConst p := by
    unfold lpSqConst Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have : 0 ≤ p := by linarith
    positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  let sc : κ → Finset ι := fun c => s.filter fun i => col i = c
  have hfib : ∀ (g : ι → ℝ), ∑ c, ∑ i ∈ sc c, g i = ∑ i ∈ s, g i := fun g =>
    Finset.sum_fiberwise s col g
  have hfibf : (∑ i ∈ s, f i) = ∑ c, ∑ i ∈ sc c, f i :=
    (Finset.sum_fiberwise s col f).symm
  set S : κ → ℝ := fun c => ∑ i ∈ sc c, a i ^ 2 with hS
  have hSc : ∀ c, (eLpNorm (∑ i ∈ sc c, f i) (ENNReal.ofReal p) μ).toReal ≤
      K * Real.sqrt (S c) := by
    intro c
    have := complex_eLpNorm_sum_le_sqrt_sum_sq (μ := μ)
      (f := fun i : {i : ι // col i = c} => f i) (s.subtype fun i => col i = c) hp (h_indep c)
      (fun i => h_meas i) (fun i => hLp i) (fun i => hmean i)
    have e1 : (∑ i ∈ s.subtype fun i => col i = c, (fun i : {i : ι // col i = c} => f i) i) =
        ∑ i ∈ sc c, f i := by
      funext ω
      simp only [Finset.sum_apply]
      exact Finset.sum_subtype_eq_sum_filter (fun i => f i ω)
    have e2 : ∑ i ∈ s.subtype fun i => col i = c,
        (eLpNorm (f i) (ENNReal.ofReal p) μ).toReal ^ 2 = S c := by
      exact Finset.sum_subtype_eq_sum_filter (fun i => a i ^ 2)
    rw [e1, e2] at this
    exact this
  have htri : eLpNorm (∑ c, ∑ i ∈ sc c, f i) (ENNReal.ofReal p) μ ≤
      ∑ c, eLpNorm (∑ i ∈ sc c, f i) (ENNReal.ofReal p) μ :=
    eLpNorm_sum_le hp1
  have hfin : ∀ c, eLpNorm (∑ i ∈ sc c, f i) (ENNReal.ofReal p) μ ≠ ⊤ := fun c =>
    (memLp_finsetSum' _ fun i _ => hLp i).eLpNorm_ne_top
  have h1 : (eLpNorm (∑ i ∈ s, f i) (ENNReal.ofReal p) μ).toReal ≤
      ∑ c, (eLpNorm (∑ i ∈ sc c, f i) (ENNReal.ofReal p) μ).toReal := by
    rw [hfibf]
    rw [← ENNReal.toReal_sum fun c _ => hfin c]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun c _ => hfin c) htri
  have h2 : ∑ c, Real.sqrt (S c) ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
    have hS0 : ∀ c, 0 ≤ S c := fun c => Finset.sum_nonneg fun i _ => by positivity
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ))
      (f := fun c => Real.sqrt (S c))
    have hsq : ∑ c, Real.sqrt (S c) ^ 2 = ∑ i ∈ s, a i ^ 2 := by
      rw [← hfib (fun i => a i ^ 2)]
      exact Finset.sum_congr rfl fun c _ => Real.sq_sqrt (hS0 c)
    rw [hsq, Finset.card_univ] at hcs
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le hcs
  calc _ ≤ ∑ c, K * Real.sqrt (S c) := h1.trans (Finset.sum_le_sum fun c _ => hSc c)
    _ = K * ∑ c, Real.sqrt (S c) := by rw [Finset.mul_sum]
    _ ≤ K * (Real.sqrt (Fintype.card κ) * Real.sqrt (∑ i ∈ s, a i ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 hK0
    _ = _ := by rw [hK]; ring

end EinsteinFull.Calculus.K1
