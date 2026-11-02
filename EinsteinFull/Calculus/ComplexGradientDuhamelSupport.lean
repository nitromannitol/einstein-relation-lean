import EinsteinFull.Calculus.ComplexUnforcedGradientSupport
import EinsteinFull.Calculus.ComplexDuhamelSupport
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Horizontal gradients of the stationary Duhamel identity

Positive unforced time regularization allows the actual bounded horizontal
gradient to pass through the Bochner integral. Full generator graph continuity
removes the regularization in the resulting singular convolution estimate.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The square-root kernel times a continuous scalar function is integrable up to its singular endpoint. -/
theorem intervalIntegrable_sqrt_div_sub_mul {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t)
    {v : ℝ → ℝ} (hv : Continuous v) :
    IntervalIntegrable (fun s => Real.sqrt (K/(t-s)) * v s) volume 0 t := by
  have hp := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
    (show -1 < -(1/2 : ℝ) by norm_num)).comp_sub_left t
  simp only [sub_zero, sub_self] at hp
  have hk := hp.symm.const_mul (Real.sqrt K)
  have he : IntervalIntegrable (fun s => Real.sqrt (K/(t-s))) volume 0 t := by
    apply IntervalIntegrable.congr (f := fun s => Real.sqrt K * (t-s) ^ (-(1/2 : ℝ))) ?_ hk
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    change Real.sqrt K * (t-s) ^ (-(1/2 : ℝ)) = Real.sqrt (K/(t-s))
    rw [Real.rpow_neg (sub_nonneg.mpr hs.2), ← Real.sqrt_eq_rpow,
      Real.sqrt_div hK, div_eq_mul_inv]
  exact he.mul_continuousOn hv.continuousOn

/-- Actual unforced gradients converge to the initial gradient in the full generator graph. -/
theorem IsComplexEnvironmentSemigroup.tendsto_unforcedGradient_of_generator
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    {α : Type*} {l : Filter α} {τ : α → ℝ≥0} (hτ : ∀ x, 0 < τ x)
    (hτ0 : Tendsto τ l (𝓝 0)) :
    Tendsto (fun x => hR.unforcedGradient (τ x) (hτ x) f) l (𝓝 G) := by
  have hu := ((hR.2.2.1 f).tendsto 0).comp hτ0
  have hv := ((hR.2.2.1 g).tendsto 0).comp hτ0
  simp only [hR.1, ContinuousLinearMap.id_apply] at hu hv
  exact tendsto_complexHorizontalGradient_of_generator
    (fun x => hR.map_generator hfg (τ x))
    (fun x => hR.unforcedGradient_spec (τ x) (hτ x) f) hfg hG hu hv

/-- A positive unforced time makes the differentiated Duhamel identity a bounded-map integral identity. -/
theorem IsComplexEnvironmentSemigroup.unforcedGradient_duhamel
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (δ : ℝ≥0) (hδ : 0 < δ) (t : ℝ≥0) :
    hR.unforcedGradient δ hδ (P t f) = hR.unforcedGradient δ hδ (R t f) +
      ζ • (∫ s in (0 : ℝ)..(t : ℝ), hR.unforcedGradient δ hδ
        (R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s)))) := by
  have he := congrArg (hR.unforcedGradient δ hδ) (hP.integral_force_drift hR hfg hG t)
  rw [map_smul, map_sub, ← (hR.unforcedGradient δ hδ).intervalIntegral_comp_comm
    (hP.intervalIntegrable_force_drift hR hfg hG t)] at he
  exact (eq_add_of_sub_eq he.symm).trans (add_comm _ _)

private theorem norm_gradient_after_unforced_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    (δ : ℝ≥0) (hδ : 0 < δ) (s : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖hR.unforcedGradient δ hδ (R s f)‖ ≤
      Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / ((δ : ℝ)+(s : ℝ))) * ‖f‖ := by
  have he := congrArg (fun A => A f) (hR.unforcedGradient_add δ hδ s)
  rw [ContinuousLinearMap.comp_apply] at he
  rw [← he]
  exact ((hR.unforcedGradient (δ+s) _).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hR.norm_unforcedGradient_le (δ+s) _) (norm_nonneg f))

private theorem norm_regularized_gradient_duhamel_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (δ : ℝ≥0) (hδ : 0 < δ) (t : ℝ≥0) (ht : 0 < t) :
    ‖hR.unforcedGradient δ hδ (P t f)‖ ≤
      Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t : ℝ)) * ‖f‖ +
      ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        (∫ s in (0 : ℝ)..(t : ℝ), Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t-s)) * ‖G s‖) := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let C := (d : ℝ) * K
  have hK : 0 ≤ K := mul_nonneg (Real.exp_nonneg _) (le_trans zero_le_one Q.ellipticity_parameter)
  have hGc : Continuous G := continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
    ((hP.2.2.1 g).comp continuous_real_toNNReal)
  have hb : ‖hR.unforcedGradient δ hδ (R t f)‖ ≤ Real.sqrt (K/(t : ℝ)) * ‖f‖ :=
    (norm_gradient_after_unforced_le hR δ hδ t f).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_left hK ht (le_add_of_nonneg_left δ.property))) (norm_nonneg f))
  have hi : ‖∫ s in (0 : ℝ)..(t : ℝ), hR.unforcedGradient δ hδ
      (R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s)))‖ ≤
      C * (∫ s in (0 : ℝ)..(t : ℝ), Real.sqrt (K/(t-s)) * ‖G s‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (μ := volume) t.property
    · filter_upwards [volume.ae_ne (t : ℝ)] with s hst hs
      have hst' : s < (t : ℝ) := lt_of_le_of_ne hs.2 hst
      have hr : 0 < (t : ℝ)-s := sub_pos.mpr hst'
      have he : ((Real.toNNReal (t-s) : ℝ≥0) : ℝ) = t-s := Real.coe_toNNReal _ hr.le
      have hn := norm_gradient_after_unforced_le hR δ hδ (Real.toNNReal (t-s))
        (complexForceDrift Q i (G s))
      rw [he] at hn
      calc
        _ ≤ Real.sqrt (K/((δ : ℝ)+(t-s))) * ‖complexForceDrift Q i (G s)‖ := hn
        _ ≤ Real.sqrt (K/(t-s)) * (C * ‖G s‖) :=
          mul_le_mul (Real.sqrt_le_sqrt
            (div_le_div_of_nonneg_left hK hr (le_add_of_nonneg_left δ.property)))
            (norm_complexForceDrift_apply_le Q i (G s))
            (norm_nonneg _) (Real.sqrt_nonneg _)
        _ = _ := by ring
    · exact (intervalIntegrable_sqrt_div_sub_mul hK t.property hGc.norm).const_mul C
  rw [hP.unforcedGradient_duhamel hR hfg hG δ hδ t]
  calc
    _ ≤ ‖hR.unforcedGradient δ hδ (R t f)‖ +
        ‖ζ • (∫ s in (0 : ℝ)..(t : ℝ), hR.unforcedGradient δ hδ
          (R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s))))‖ := norm_add_le _ _
    _ ≤ Real.sqrt (K/(t : ℝ)) * ‖f‖ + ‖ζ‖ *
        (C * (∫ s in (0 : ℝ)..(t : ℝ), Real.sqrt (K/(t-s)) * ‖G s‖)) := by
      rw [norm_smul]
      exact add_le_add hb (mul_le_mul_of_nonneg_left hi (norm_nonneg ζ))
    _ = _ := by dsimp only [C, K]; ring

/-- The actual forced gradient satisfies the singular square-root convolution inequality on the full domain. -/
theorem IsComplexEnvironmentSemigroup.norm_gradient_le_duhamel_convolution
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) (ht : 0 < t) :
    ‖G (t : ℝ)‖ ≤ Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t : ℝ)) * ‖f‖ +
      ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        (∫ s in (0 : ℝ)..(t : ℝ), Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t-s)) * ‖G s‖) := by
  let τ : ℕ → ℝ≥0 := fun n => 1/((n : ℝ≥0)+1)
  have hτ : ∀ n, 0 < τ n := fun n => by dsimp only [τ]; positivity
  have hτ0 : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hGt : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (G (t : ℝ)) := by simpa only [Real.toNNReal_coe] using hG (t : ℝ)
  have hu := (hP.map_generator hfg t).change_force 0 hGt
  have hl := hR.tendsto_unforcedGradient_of_generator hu hGt hτ hτ0
  exact le_of_tendsto hl.norm (Eventually.of_forall fun n =>
    norm_regularized_gradient_duhamel_le hP hR hfg hG (τ n) (hτ n) t ht)

/-- A full forced-domain datum has a continuous actual gradient orbit obeying the convolution estimate. -/
theorem IsComplexEnvironmentSemigroup.exists_gradient_orbit_convolution
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, 0 < t → ‖G (t : ℝ)‖ ≤
        Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t : ℝ)) * ‖f‖ +
        ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
          (∫ s in (0 : ℝ)..(t : ℝ), Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀)/(t-s)) * ‖G s‖) := by
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  exact ⟨G, hGc, hG, fun t ht => hP.norm_gradient_le_duhamel_convolution
    (isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i) hfg hG t ht⟩

end EinsteinFull
