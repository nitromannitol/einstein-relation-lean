import EinsteinFull.Calculus.RadialEnergyEvolutionSupport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing the bounded radial tests

The primitive has its exact power limit, including the factor `1/p`. A single
positive sequence removes the saturation and regularization together.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal Interval

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem radialWeight_le {ε R a s b : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ha : 0 ≤ a) (hs : 0 ≤ s) (hb : ε + s ≤ b) :
    radialTruncationWeight ε R a s ≤ b ^ a := by
  have hsat : R * s / (R + s) ≤ s := by
    apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hR hs)).mpr
    nlinarith only [sq_nonneg s]
  apply Real.rpow_le_rpow (radialTruncationBase_pos_le hε hR hs).1.le _ ha
  unfold radialTruncationBase
  linarith only [hsat, hb]

/-- A pointwise bound uniform in the positive saturation and in `0 < ε ≤ 1`. -/
theorem norm_radialTruncationPrimitive_le_power {ε R a : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) (ha : 0 ≤ a) (z : ℂ) :
    ‖radialTruncationPrimitive ε R a z‖ ≤ (1 + ‖z‖) ^ (2 * (1 + a)) := by
  rw [radialTruncationPrimitive_eq_integral, norm_mul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hI : ‖∫ s in 0..‖z‖ ^ 2, radialTruncationWeight ε R a s‖ ≤
      (1 + ‖z‖) ^ (2 * a) * ‖z‖ ^ 2 := by
    calc
      _ ≤ (1 + ‖z‖) ^ (2 * a) * |‖z‖ ^ 2 - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le (sq_nonneg ‖z‖)] at hs
        have hs0 : 0 ≤ s := hs.1.le
        rw [Real.norm_eq_abs, abs_of_nonneg
          (show 0 ≤ radialTruncationWeight ε R a s from
            Real.rpow_nonneg (radialTruncationBase_pos_le hε hR hs0).1.le _)]
        have hb : ε + s ≤ (1 + ‖z‖) ^ 2 := by
          nlinarith only [hs.2, hε1, norm_nonneg z]
        convert radialWeight_le hε hR ha hs0 hb using 1
        rw [Real.rpow_mul (by positivity : 0 ≤ 1 + ‖z‖)]
        simp only [Real.rpow_two]
      _ = _ := by rw [sub_zero, abs_of_nonneg (sq_nonneg ‖z‖)]
  have hq : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith only [norm_nonneg z]
  calc
    _ ≤ (1 / 2 : ℝ) * ((1 + ‖z‖) ^ (2 * a) * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hI (by norm_num)
    _ ≤ (1 + ‖z‖) ^ (2 * a) * (1 + ‖z‖) ^ 2 := by
      have hp : 0 ≤ (1 + ‖z‖) ^ (2 * a) := Real.rpow_nonneg (by positivity) _
      nlinarith only [mul_le_mul_of_nonneg_left hq hp,
        mul_nonneg hp (sq_nonneg ‖z‖)]
    _ = _ := by
      rw [← Real.rpow_natCast (1 + ‖z‖) 2, ← Real.rpow_add (by positivity)]
      congr 1
      ring

private theorem tendsto_radialWeight {ε R : ℕ → ℝ} {a s : ℝ} (ha : 0 ≤ a)
    (hs : 0 ≤ s) (hε : Tendsto ε atTop (𝓝 0)) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => radialTruncationWeight (ε n) (R n) a s) atTop (𝓝 (s ^ a)) := by
  have hi : Tendsto (fun n => s / R n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hR
  have hb : Tendsto (fun n => ε n + s / (1 + s / R n)) atTop (𝓝 s) := by
    convert hε.add (tendsto_const_nhds.div (tendsto_const_nhds.add hi)
      (by norm_num : (1 : ℝ) + 0 ≠ 0)) using 1
    simp only [add_zero, div_one, zero_add]
  have hw := (Real.continuousAt_rpow_const s a (Or.inr ha)).tendsto.comp hb
  apply hw.congr'
  filter_upwards [hR.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  change (ε n + s / (1 + s / R n)) ^ a = _
  unfold radialTruncationWeight radialTruncationBase
  congr 1
  have hden : R n + s ≠ 0 := (add_pos_of_pos_of_nonneg hn hs).ne'
  field_simp [hn.ne', hden]

/-- The exact scalar limit retains the normalization `1 / (2(1+a))`. -/
theorem tendsto_radialTruncationPrimitive {ε R : ℕ → ℝ} {a : ℝ}
    (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1) (hR : ∀ n, 0 < R n)
    (ha : 0 ≤ a) (hεlim : Tendsto ε atTop (𝓝 0))
    (hRlim : Tendsto R atTop atTop) (z : ℂ) :
    Tendsto (fun n => radialTruncationPrimitive (ε n) (R n) a z) atTop
      (𝓝 (‖z‖ ^ (2 * (1 + a)) / (2 * (1 + a)))) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (radialTruncationWeight (ε n) (R n) a) (volume.restrict (Ι 0 (‖z‖ ^ 2))) := by
    apply ((continuousOn_radialTruncationWeight_slope (a := a) (hε n) (hR n)).1.mono
      (show Set.uIoc 0 (‖z‖ ^ 2) ⊆ Set.Ici 0 from ?_)).aestronglyMeasurable
      measurableSet_uIoc
    intro s hs
    rw [Set.uIoc_of_le (sq_nonneg ‖z‖)] at hs
    exact hs.1.le
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => (1 + ‖z‖ ^ 2) ^ a)
    (Eventually.of_forall hm)
    (Eventually.of_forall fun n => Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le (sq_nonneg ‖z‖)] at hs
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ radialTruncationWeight (ε n) (R n) a s from
          Real.rpow_nonneg (radialTruncationBase_pos_le (hε n) (hR n) hs.1.le).1.le _)]
      exact radialWeight_le (hε n) (hR n) ha hs.1.le (add_le_add (hε1 n) hs.2))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 + ‖z‖ ^ 2) ^ a)
      volume 0 (‖z‖ ^ 2))
    (Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le (sq_nonneg ‖z‖)] at hs
      exact tendsto_radialWeight ha hs.1.le hεlim hRlim)
  have he : (1 / 2 : ℝ) * (∫ s in 0..‖z‖ ^ 2, s ^ a) =
      ‖z‖ ^ (2 * (1 + a)) / (2 * (1 + a)) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < a)),
      Real.zero_rpow (by linarith : a + 1 ≠ 0), sub_zero]
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg z)]
    have hh : a + 1 = 1 + a := by ring
    rw [hh]
    field_simp
  simpa only [radialTruncationPrimitive_eq_integral, he] using
    (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul ht

/-- For genuine Lp data the cutoff primitive integrals converge to the exact
power moment. The only domination is supplied by that same Lp hypothesis. -/
theorem MemLp.tendsto_integral_radialTruncationPrimitive
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hf : MemLp f (ENNReal.ofReal (2 * (1 + a))) μ)
    {ε R : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hR : ∀ n, 0 < R n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hRlim : Tendsto R atTop atTop) :
    Tendsto (fun n => ∫ ω, radialTruncationPrimitive (ε n) (R n) a (f ω) ∂μ)
      atTop (𝓝 (∫ ω, ‖f ω‖ ^ (2 * (1 + a)) / (2 * (1 + a)) ∂μ)) := by
  have hp : 0 < 2 * (1 + a) := by linarith
  have hi : Integrable (fun ω => (1 + ‖f ω‖) ^ (2 * (1 + a))) μ := by
    have hh := ((memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ))
      (ENNReal.ofReal (2 * (1 + a))) μ).add hf.norm).integrable_norm_rpow
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    convert hh using 1
    ext ω
    rw [ENNReal.toReal_ofReal hp.le, Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 + ‖f ω‖)]
  refine tendsto_integral_of_dominated_convergence _ ?_ hi ?_ ?_
  · intro n
    have hc : Continuous (radialTruncationPrimitive (ε n) (R n) a) :=
      continuous_iff_continuousAt.mpr fun z =>
        (hasFDerivAt_radialTruncationPrimitive (hε n) (hR n) z).continuousAt
    exact hc.comp_aestronglyMeasurable hf.aestronglyMeasurable
  · intro n
    exact Eventually.of_forall fun ω =>
      norm_radialTruncationPrimitive_le_power (hε n) (hε1 n) (hR n) ha (f ω)
  · exact Eventually.of_forall fun ω =>
      tendsto_radialTruncationPrimitive hε hε1 hR ha hεlim hRlim (f ω)

private theorem integrable_integral_le_of_nonneg_limit
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℕ → ℝ} {c : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hF0 : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ F n ω)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)))
    (hbound : ∀ n, (∫ ω, F n ω ∂μ) ≤ C n) (hC : Tendsto C atTop (𝓝 c)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) ≤ c := by
  have hc : 0 ≤ c := ge_of_tendsto hC (Eventually.of_forall fun n =>
    (integral_nonneg_of_ae (hF0 n)).trans (hbound n))
  have hmeas := aestronglyMeasurable_of_tendsto_ae _
    (fun n => (hF n).aestronglyMeasurable) hlim
  have hfatou : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact (ENNReal.tendsto_ofReal hω).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hupper : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal c := by
    apply hfatou.trans
    calc
      _ ≤ liminf (fun n => ENNReal.ofReal (C n)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall ?_)
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (hF0 n)]
        exact ENNReal.ofReal_le_ofReal (hbound n)
      _ = _ := (ENNReal.tendsto_ofReal hC).liminf_eq
  have hfi : Integrable f μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have he : (fun ω => ENNReal.ofReal ‖f ω‖) =ᵐ[μ]
        (fun ω => ENNReal.ofReal (f ω)) := by
      filter_upwards [hf0] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg hω]
    rw [lintegral_congr_ae he]
    exact hupper.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hf0] at hupper
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp hupper

/-- The untruncated forward p-moment estimate on all actual L2 data that also
belong to Lp, for every real p = 2(1+a) ≥ 2. In particular the output Lp
membership is proved rather than assumed. -/
theorem IsComplexEnvironmentSemigroup.power_moment_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {a : ℝ} (ha : 0 ≤ a) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q)) (t : ℝ≥0) :
    MemLp (P t f) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ∧
      (∫ ω, ‖P t f ω‖ ^ (2 * (1 + a)) ∂reducedLaw Q) ≤
        (∫ ω, ‖f ω‖ ^ (2 * (1 + a)) ∂reducedLaw Q) *
          Real.exp (((2 * (1 + a)) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
            (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)) * (t : ℝ)) := by
  letI := reducedLaw_probability Q
  let r (n : ℕ) : ℝ := (n : ℝ) + 1
  let e (n : ℕ) : ℝ := (r n)⁻¹
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have he (n : ℕ) : 0 < e n := inv_pos.mpr (hr n)
  have he1 (n : ℕ) : e n ≤ 1 := by
    apply (inv_le_one₀ (hr n)).mpr
    dsimp only [r]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hrlim : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have helim : Tendsto e atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hrlim
  let p : ℝ := 2 * (1 + a)
  let A : ℝ := Real.exp ((p * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2)) * (t : ℝ))
  have hp : 0 < p := by dsimp only [p]; linarith
  have hlimit := MemLp.tendsto_integral_radialTruncationPrimitive ha hf he he1 hr helim hrlim
  have hbounded := integrable_integral_le_of_nonneg_limit
    (F := fun n ω => radialTruncationPrimitive (e n) (r n) a (P t f ω))
    (f := fun ω => ‖P t f ω‖ ^ p / p)
    (C := fun n => (∫ ω, radialTruncationPrimitive (e n) (r n) a (f ω)
      ∂reducedLaw Q) * A)
    (c := (∫ ω, ‖f ω‖ ^ p / p ∂reducedLaw Q) * A)
    (fun n => integrable_radialTruncationPrimitive (reducedLaw Q) (P t f) (he n) (hr n) ha)
    (fun n => Eventually.of_forall fun ω =>
      radialTruncationPrimitive_nonneg (he n) (hr n) (P t f ω))
    (Eventually.of_forall fun ω => div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hp.le)
    (Eventually.of_forall fun ω =>
      tendsto_radialTruncationPrimitive he he1 hr ha helim hrlim (P t f ω))
    (fun n => hP.radialTruncation_energy_growth_all f (he n) (hr n) ha t)
    (hlimit.mul_const A)
  have hout : Integrable (fun ω => ‖P t f ω‖ ^ p) (reducedLaw Q) := by
    convert hbounded.1.const_mul p using 1
    ext ω
    exact (mul_div_cancel₀ _ hp.ne').symm
  have hmem : MemLp (P t f) (ENNReal.ofReal p) (reducedLaw Q) := by
    apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable (P t f))
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp.le] using hout
  refine ⟨hmem, ?_⟩
  have hb := hbounded.2
  simp only [div_eq_mul_inv, integral_mul_const] at hb
  have hh : (∫ ω, ‖P t f ω‖ ^ p ∂reducedLaw Q) ≤
      (∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * A := by
    have heq : ((∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * p⁻¹ * A) * p =
        (∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * A := by
      calc
        _ = (∫ ω, ‖f ω‖ ^ p ∂reducedLaw Q) * A * (p⁻¹ * p) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hp.ne', mul_one]
    have hmul := mul_le_mul_of_nonneg_right hb hp.le
    rw [heq, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one] at hmul
    exact hmul
  exact hh

/-- Taking the exact pth root gives leading constant one and a quadratic force
rate on the actual forward family. -/
theorem IsComplexEnvironmentSemigroup.eLpNorm_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {a : ℝ} (ha : 0 ≤ a) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q)) (t : ℝ≥0) :
    eLpNorm (P t f) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) *
        ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ))) := by
  let p := 2 * (1 + a)
  let c := ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ)
  have hp : 0 < p := by dsimp only [p]; linarith
  obtain ⟨hout, hb⟩ := hP.power_moment_growth ha f hf t
  rw [hout.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg fun ω =>
      Real.rpow_nonneg (norm_nonneg (f ω)) _) _)]
  apply ENNReal.ofReal_le_ofReal
  have hm := Real.rpow_le_rpow (integral_nonneg fun ω =>
    Real.rpow_nonneg (norm_nonneg (P t f ω)) p) hb (inv_nonneg.mpr hp.le)
  apply hm.trans_eq
  rw [Real.mul_rpow (integral_nonneg fun ω => Real.rpow_nonneg (norm_nonneg (f ω)) p)
    (Real.exp_pos _).le, ← Real.exp_mul]
  congr 2
  change (p * _ * (t : ℝ)) * p⁻¹ = c
  dsimp only [c]
  field_simp

/-- Every datum of the genuine finite Lp space, p ≥ 2, embeds in actual L2
and satisfies the forward bound; no density or output-membership premise is
needed. -/
theorem IsComplexEnvironmentSemigroup.eLpNorm_growth_Lp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {a : ℝ} (ha : 0 ≤ a)
    (f : Lp ℂ (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q)) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    let h₂ : MemLp f 2 (reducedLaw Q) := (Lp.memLp f).mono_exponent
      ((ENNReal.natCast_le_ofReal (by decide : (2 : ℕ) ≠ 0)).mpr
        (by norm_num only [Nat.cast_ofNat]; linarith))
    MemLp (P t (h₂.toLp f)) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ∧
      eLpNorm (P t (h₂.toLp f)) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) ≤
        eLpNorm f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) *
          ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
            (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ))) := by
  dsimp only
  letI := reducedLaw_probability Q
  let h₂ : MemLp f 2 (reducedLaw Q) := (Lp.memLp f).mono_exponent
    ((ENNReal.natCast_le_ofReal (by decide : (2 : ℕ) ≠ 0)).mpr
        (by norm_num only [Nat.cast_ofNat]; linarith))
  have hf : MemLp (h₂.toLp f) (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) :=
    (Lp.memLp f).ae_eq h₂.coeFn_toLp.symm
  refine ⟨(hP.power_moment_growth ha (h₂.toLp f) hf t).1, ?_⟩
  have h := hP.eLpNorm_growth ha (h₂.toLp f) hf t
  rw [eLpNorm_congr_ae h₂.coeFn_toLp] at h
  exact h

end EinsteinFull
