import EinsteinFull.Calculus.ComplexGradientDuhamelSupport
import EinsteinFull.Calculus.SqrtVolterraSupport

/-!
# Forced stationary horizontal gradient smoothing

The actual gradient convolution and scalar absorption give a short-time
bound independent of the generator output. The semigroup law extends it
to all positive times; actual forced resolvents and gradient graph closedness
extend it to every complex L2 datum.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- On the full forced domain, a short positive time smooths with a constant independent of the output. -/
theorem IsComplexEnvironmentSemigroup.norm_gradient_le_of_small
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) (ht : 0 < t)
    (hsmall : 8 * (‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
      Real.sqrt (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (t : ℝ) ≤ 1)
    {H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) H) :
    ‖H‖ ≤ (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) * ‖f‖ := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let b := ‖ζ‖ * ((d : ℝ) * K)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_nonneg _)
    (zero_le_one.trans Q.ellipticity_parameter)
  have hb : 0 ≤ b := mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hK)
  obtain ⟨G, hGc, hG, hconv⟩ := hP.exists_gradient_orbit_convolution hfg
  have hv : ∀ s ∈ Ioc 0 (t : ℝ), ‖G s‖ ≤
      (Real.sqrt K * ‖f‖) / Real.sqrt s + (b * Real.sqrt K) *
        (∫ r in (0 : ℝ)..s, ‖G r‖ / Real.sqrt (s-r)) := by
    intro s hs
    have he := hconv s.toNNReal (Real.toNNReal_pos.2 hs.1)
    rw [Real.coe_toNNReal s hs.1.le] at he
    have hi : (∫ r in (0 : ℝ)..s, Real.sqrt (K/(s-r)) * ‖G r‖) =
        Real.sqrt K * (∫ r in (0 : ℝ)..s, ‖G r‖ / Real.sqrt (s-r)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      change Real.sqrt (K/(s-r)) * ‖G r‖ = _
      rw [Real.sqrt_div hK]
      ring
    change ‖G s‖ ≤ Real.sqrt (K/s) * ‖f‖ + b * _ at he
    rw [hi, Real.sqrt_div hK] at he
    convert he using 1; ring
  have hbound := sqrt_volterra_le_of_small hGc.norm
    (mul_nonneg (Real.sqrt_nonneg K) (norm_nonneg f))
    (mul_nonneg hb (Real.sqrt_nonneg K)) (show (0 : ℝ) < t from ht)
    (fun s _ => norm_nonneg (G s)) hsmall hv (t : ℝ) ⟨ht, le_rfl⟩
  have hGt : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (G (t : ℝ)) := by simpa only [Real.toNNReal_coe] using hG (t : ℝ)
  have heq : G (t : ℝ) = H := WithLp.ofLp_injective 2 (hGt.unique hH)
  rw [heq] at hbound
  convert hbound using 1; ring

private theorem eight_mul_sqrt_le_exp {B t : ℝ} (ht : 0 ≤ t) :
    8 * B * Real.sqrt t ≤ Real.exp (64 * B ^ 2 * t) := by
  have he : (8 * B * Real.sqrt t) ^ 2 = 64 * B ^ 2 * t := by
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
    ring
  have hb : 8 * B * Real.sqrt t ≤ (8 * B * Real.sqrt t) ^ 2 + 1 := by
    nlinarith only [sq_nonneg (8 * B * Real.sqrt t - 1/2)]
  rw [he] at hb
  exact hb.trans (Real.add_one_le_exp _)

/-- The full-domain forced gradient has a uniform quadratic-force exponential smoothing bound. -/
theorem IsComplexEnvironmentSemigroup.norm_gradient_forced_le_of_generator
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) (ht : 0 < t)
    {H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) H) :
    ‖H‖ ≤ (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let B := (‖ζ‖ * ((d : ℝ) * K)) * Real.sqrt K
  let ω := complexForceShift d Λ₀ ζ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_nonneg _)
    (zero_le_one.trans Q.ellipticity_parameter)
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hK)) (Real.sqrt_nonneg _)
  have hω : 0 ≤ ω := complexForceShift_nonneg Q ζ
  have hωeq : ω = B ^ 2 := by
    change K * (‖ζ‖ * ((d : ℝ) * K)) ^ 2 =
      ((‖ζ‖ * ((d : ℝ) * K)) * Real.sqrt K) ^ 2
    simp only [mul_pow, Real.sq_sqrt hK]
    ring
  have hc : 0 ≤ 2 * Real.sqrt K / Real.sqrt (t : ℝ) := by positivity
  by_cases hsmall : 8 * B * Real.sqrt (t : ℝ) ≤ 1
  · have hb := hP.norm_gradient_le_of_small hfg t ht hsmall hH
    have he : 1 ≤ Real.exp (65 * ω * (t : ℝ)) :=
      Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hω) t.property)
    exact hb.trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right hc he) (norm_nonneg f))
  have hBpos : 0 < B := by
    by_contra! hn
    have hz : B = 0 := le_antisymm hn hB
    exact hsmall (by simp only [hz, mul_zero, zero_mul]; norm_num)
  have h8B : 0 < 8 * B := mul_pos (by norm_num) hBpos
  let δ : ℝ≥0 := ⟨((8 * B)⁻¹) ^ 2, sq_nonneg _⟩
  have hδpos : 0 < δ := sq_pos_of_pos (inv_pos.2 h8B)
  have hroot : Real.sqrt (δ : ℝ) = (8 * B)⁻¹ := Real.sqrt_sq (inv_nonneg.2 h8B.le)
  have hδsmall : 8 * B * Real.sqrt (δ : ℝ) ≤ 1 := by
    rw [hroot, mul_inv_cancel₀ h8B.ne']
  have hδle : δ ≤ t := by
    have hi : (8 * B)⁻¹ < Real.sqrt (t : ℝ) := by
      rw [← one_div]
      apply (div_lt_iff₀ h8B).2
      simpa only [mul_comm] using lt_of_not_ge hsmall
    change ((8 * B)⁻¹) ^ 2 ≤ (t : ℝ)
    have hs := (sq_le_sq₀ (inv_nonneg.2 h8B.le) (Real.sqrt_nonneg (t : ℝ))).2 hi.le
    exact hs.trans (Real.sq_sqrt t.property).le
  have hHt : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P δ (P (t-δ) f)) H := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, add_tsub_cancel_of_le hδle]
    exact hH
  have hb := hP.norm_gradient_le_of_small (hP.map_generator hfg (t-δ)) δ hδpos hδsmall hHt
  have hn : ‖P (t-δ) f‖ ≤ Real.exp (ω * (t : ℝ)) * ‖f‖ := by
    apply ((P (t-δ)).le_opNorm f).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    exact (hP.norm_le (t-δ)).trans (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (by exact_mod_cast tsub_le_self) hω))
  have hcoef : (2 * Real.sqrt K / Real.sqrt (δ : ℝ)) * Real.exp (ω * (t : ℝ)) ≤
      (2 * Real.sqrt K / Real.sqrt (t : ℝ)) * Real.exp (65 * ω * (t : ℝ)) := by
    calc
      _ = (2 * Real.sqrt K / Real.sqrt (t : ℝ)) *
          (8 * B * Real.sqrt (t : ℝ)) * Real.exp (ω * (t : ℝ)) := by
        rw [hroot]
        field_simp
      _ ≤ (2 * Real.sqrt K / Real.sqrt (t : ℝ)) *
          Real.exp (64 * ω * (t : ℝ)) * Real.exp (ω * (t : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hc
        rw [hωeq]
        exact eight_mul_sqrt_le_exp t.property
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  exact hb.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (norm_nonneg f)))

private theorem cauchySeq_of_norm_sub_control {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {u : ℕ → E} {v : ℕ → F}
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n m, ‖v n-v m‖ ≤ C * ‖u n-u m‖)
    (hu : CauchySeq u) : CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < C+1 := add_pos_of_nonneg_of_pos hC zero_lt_one
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε/(C+1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ C * ‖u n-u m‖ := hb n m
    _ ≤ (C+1) * ‖u n-u m‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

/-- Every complex L2 datum gains an actual forced horizontal gradient at every positive time. -/
theorem IsComplexEnvironmentSemigroup.exists_gradient_forced
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ht : 0 < t) :
    ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G ∧
      ‖G‖ ≤ (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ := by
  let C := (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
    Real.exp (65 * complexForceShift d Λ₀ ζ * (t : ℝ))
  have hCnonneg : 0 ≤ C := by positivity
  set u : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n =>
    forcedComplexResolventApproximation Q i ζ n f with hu_def
  set v : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n =>
    forcedComplexYosida Q i ζ n f + (complexForceShift d Λ₀ ζ : ℂ) • u n with hv_def
  clear_value u v
  have hg (n : ℕ) : IsComplexGeneratorPair Q i ζ (u n) (v n) := by
    rw [hv_def, hu_def]
    exact forcedComplexYosida_graph Q i ζ n f
  have he (n : ℕ) : ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t (u n)) G := by
    obtain ⟨G, hG, _⟩ := hP.map_generator (hg n) t
    exact ⟨WithLp.toLp 2 G, hG⟩
  choose G hG using he
  have hb (n m : ℕ) : ‖G n-G m‖ ≤ C * ‖u n-u m‖ := by
    have hd : IsComplexGeneratorPair Q i ζ (u n-u m) (v n-v m) := by
      simpa only [neg_one_smul, ← sub_eq_add_neg] using (hg n).add ((hg m).smul (-1))
    have hD : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P t (u n-u m)) (G n-G m) := by
      intro j
      simpa only [map_sub, PiLp.sub_apply, Pi.sub_apply, neg_one_smul, ← sub_eq_add_neg] using
        (hG n j).add ((hG m j).smul (-1))
    exact hP.norm_gradient_forced_le_of_generator hd t ht (H := G n-G m) hD
  have hu : Tendsto u atTop (𝓝 f) := by
    rw [hu_def]
    exact tendsto_forcedComplexResolventApproximation Q i ζ f
  have hCauchy : CauchySeq G := cauchySeq_of_norm_sub_control hCnonneg hb hu.cauchySeq
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hPH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) H := by
    letI := reducedLaw_probability Q
    apply complexHorizontalGradient_of_tendsto
      (Q := reducedLaw Q) (hQ := reducedLaw_stationary Q) (l := atTop)
      (p := fun n : ℕ => (P t (u n), (G n).ofLp)) (q := (P t f, H.ofLp))
      (Eventually.of_forall hG)
    exact (((P t).continuous.tendsto f).comp hu).prodMk_nhds
      ((PiLp.continuous_ofLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))).tendsto H |>.comp hH)
  refine ⟨H, hPH, ?_⟩
  apply le_of_tendsto_of_tendsto hH.norm (hu.norm.const_mul C)
  exact Eventually.of_forall fun n =>
    hP.norm_gradient_forced_le_of_generator (hg n) t ht (H := G n) (hG n)

end EinsteinFull
