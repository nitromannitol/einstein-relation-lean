import EinsteinFull.Calculus.C3FluxGeneralTestTransfer
import EinsteinFull.Calculus.CarverSFluxBlockMoments

open MeasureTheory
open EinsteinRelation

namespace EinsteinFull.Blueprint

private lemma c3_integrate_four_cutoff_recovery {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (J : Lp ℂ 2 (reducedLaw Q))
    (c : ℂ) (f a b u v : Vec d → ℂ)
    (h : ∀ y, f y = c * ((a y - b y) + Complex.I * (u y - v y)))
    (ha : Integrable (fun y => a y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hb : Integrable (fun y => b y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hu : Integrable (fun y => u y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hv : Integrable (fun y => v y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J)) :
    (∫ y, f y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
      c • ((∫ y, a y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) -
        (∫ y, b y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) +
        Complex.I • ((∫ y, u y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) -
          (∫ y, v y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J))) := by
  let T := fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J
  have hfun : (fun y => f y • T y) = fun y => c •
      ((a y • T y - b y • T y) + Complex.I • (u y • T y - v y • T y)) := by
    funext y
    rw [h y]
    simp only [mul_smul, add_smul, sub_smul]
  change (∫ y, f y • T y) = _
  rw [hfun, integral_smul]
  change c • (∫ y, (((fun y => a y • T y) - (fun y => b y • T y)) +
    Complex.I • ((fun y => u y • T y) - (fun y => v y • T y))) y) = _
  have hadd := integral_add (ha.sub hb) ((hu.sub hv).fun_smul Complex.I)
  change (∫ y, (a y • T y - b y • T y) +
    Complex.I • (u y • T y - v y • T y)) = _ at hadd
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at ⊢ hadd
  rw [hadd]
  have hab := integral_sub ha hb
  have huv := integral_sub hu hv
  change (∫ y, a y • T y - b y • T y) = _ at hab
  change (∫ y, u y • T y - v y • T y) = _ at huv
  rw [hab, integral_smul, huv]

private lemma c3_centered_integrate_four_cutoff_recovery {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (J : Lp ℂ 2 (reducedLaw Q))
    (c : ℂ) (f a b u v : Vec d → ℂ)
    (h : ∀ y, f y = c * ((a y - b y) + Complex.I * (u y - v y)))
    (ha : Integrable (fun y => a y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hb : Integrable (fun y => b y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hu : Integrable (fun y => u y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hv : Integrable (fun y => v y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J)) :
    centeredComplexLp Q (∫ y, f y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J) =
      c • ((centeredComplexLp Q (∫ y, a y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y J) -
        centeredComplexLp Q (∫ y, b y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y J)) +
        Complex.I • (centeredComplexLp Q (∫ y, u y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y J) -
        centeredComplexLp Q (∫ y, v y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y J))) := by
  rw [c3_integrate_four_cutoff_recovery Q J c f a b u v h ha hb hu hv]
  simp only [← centeredComplexLpCLM_apply, map_smul, map_add, map_sub]

private lemma c3_gaussian_cutoff_flux_integrable {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (x z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun y : Vec d =>
      (((χ (y - z) : ℂ) * iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q i s hs 0) (x - y)
          (fun q => unitVector (dirs q))) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)) := by
  obtain ⟨hcont, hint⟩ :=
    carverS_block_weight_continuous_integrable Q i s hs k dirs χ hχ hχc x z
  have htrans : Continuous (fun y : Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) :=
    (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
      (continuous_id.prodMk continuous_const)
  apply (hint.norm.mul_const ‖J‖).mono' (hcont.smul htrans).aestronglyMeasurable
  filter_upwards with y
  change ‖(((χ (y - z) : ℂ) * iteratedFDeriv ℝ k
    (homogenizedGaussianKernel Q i s hs 0) (x - y)
      (fun q => unitVector (dirs q))) •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)‖ ≤ _
  rw [norm_smul, norm_complexTranslation]

private lemma c3_gaussian_site_components_integrable {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (z : Vec d)
    (J : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun y : Vec d =>
      (((χ (y - z) : ℂ) * homogenizedGaussianKernel Q i s hs 0 (-(y - z))) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)) ∧
    Integrable (fun y : Vec d =>
      (((χ (y - z) : ℂ) * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0)
        (-(y - z)) (unitVector j)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)) := by
  constructor
  · simpa only [iteratedFDeriv_zero_apply, neg_sub] using
      c3_gaussian_cutoff_flux_integrable Q i s hs 0 (fun q => Fin.elim0 q)
        χ hχ hχc z z J
  · simpa only [iteratedFDeriv_one_apply, neg_sub] using
      c3_gaussian_cutoff_flux_integrable Q i s hs 1 (fun _ => j)
        χ hχ hχc z z J

private lemma c3_gaussian_site_cutoff_difference_integrable {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (θ baseline : Vec d → ℝ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) baseline) (hbc : HasCompactSupport baseline)
    (z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun y : Vec d =>
      (homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
        ((θ (y - z) - baseline (y - z) : ℝ) : ℂ)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) ∧
    Integrable (fun y : Vec d =>
      (fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z)) (unitVector j) *
        ((θ (y - z) - baseline (y - z) : ℝ) : ℂ)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) := by
  have h := c3_gaussian_site_components_integrable Q i j s hs
    (fun x => θ x - baseline x) (hθ.sub hb) (hθc.sub hbc) z J
  constructor
  · simpa only [Complex.ofReal_sub, mul_comm] using h.1
  · simpa only [Complex.ofReal_sub, mul_comm] using h.2

private lemma c3_four_site_recovery_components_integrable {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (θ : Bool → Bool → Vec d → ℝ) (baseline : Vec d → ℝ)
    (hθ : ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q))
    (hb : ContDiff ℝ (⊤ : ℕ∞) baseline) (hbc : HasCompactSupport baseline)
    (z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) :
    let kernel := homogenizedGaussianKernel Q i s hs 0
    Integrable (fun y : Vec d => (kernel (-(y - z)) *
      ((θ true false (y - z) - baseline (y - z) : ℝ) : ℂ)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) ∧
    Integrable (fun y : Vec d => (fderiv ℝ kernel (-(y - z)) (unitVector j) *
      ((θ false false (y - z) - baseline (y - z) : ℝ) : ℂ)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) ∧
    Integrable (fun y : Vec d => (kernel (-(y - z)) *
      ((θ true true (y - z) - baseline (y - z) : ℝ) : ℂ)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) ∧
    Integrable (fun y : Vec d => (fderiv ℝ kernel (-(y - z)) (unitVector j) *
      ((θ false true (y - z) - baseline (y - z) : ℝ) : ℂ)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) := by
  exact ⟨(c3_gaussian_site_cutoff_difference_integrable Q i j s hs
      (θ true false) baseline (hθ true false).1 (hθ true false).2 hb hbc z J).1,
    (c3_gaussian_site_cutoff_difference_integrable Q i j s hs
      (θ false false) baseline (hθ false false).1 (hθ false false).2 hb hbc z J).2,
    (c3_gaussian_site_cutoff_difference_integrable Q i j s hs
      (θ true true) baseline (hθ true true).1 (hθ true true).2 hb hbc z J).1,
    (c3_gaussian_site_cutoff_difference_integrable Q i j s hs
      (θ false true) baseline (hθ false true).1 (hθ false true).2 hb hbc z J).2⟩

private lemma c3_centered_v2_cutoff_difference {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (χ χ₀ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀) (hχ₀c : HasCompactSupport χ₀)
    (x z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) :
    let kernel := fun y : Vec d => iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun q => unitVector (dirs q))
    let trans := fun y : Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J
    centeredComplexLp Q (∫ y : Vec d,
      (((χ (y - z) - χ₀ (y - z) : ℝ) : ℂ) * kernel y) • trans y) =
      centeredComplexLp Q (∫ y : Vec d, ((χ (y - z) : ℂ) * kernel y) • trans y) -
      centeredComplexLp Q (∫ y : Vec d, ((χ₀ (y - z) : ℂ) * kernel y) • trans y) := by
  dsimp only
  have ha := c3_gaussian_cutoff_flux_integrable Q i s hs k dirs χ hχ hχc x z J
  have hb := c3_gaussian_cutoff_flux_integrable Q i s hs k dirs χ₀ hχ₀ hχ₀c x z J
  have heq : (fun y : Vec d =>
      (((χ (y - z) - χ₀ (y - z) : ℝ) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
          (fun q => unitVector (dirs q))) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
      (fun y : Vec d => ((χ (y - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
          (fun q => unitVector (dirs q))) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) -
      (fun y : Vec d => ((χ₀ (y - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
          (fun q => unitVector (dirs q))) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) := by
    funext y
    simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, sub_smul]
  rw [heq]
  change centeredComplexLp Q (∫ y : Vec d,
    ((χ (y - z) : ℂ) * iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun q => unitVector (dirs q))) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J -
    ((χ₀ (y - z) : ℂ) * iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun q => unitVector (dirs q))) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) = _
  rw [integral_sub ha hb]
  simp only [← centeredComplexLpCLM_apply, map_sub]

private lemma c3_v2_recovery_kernel_zero {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (dirs : Fin 0 → Fin d) (y : Vec d) :
    iteratedFDeriv ℝ 0 (homogenizedGaussianKernel Q i s hs 0)
      y (fun j => unitVector (dirs j)) = homogenizedGaussianKernel Q i s hs 0 y := by
  simp only [iteratedFDeriv_zero_apply]

private lemma c3_v2_recovery_kernel_one {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (y : Vec d) :
    iteratedFDeriv ℝ 1 (homogenizedGaussianKernel Q i s hs 0)
      y (fun _ => unitVector j) =
        fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) y (unitVector j) := by
  simp only [iteratedFDeriv_one_apply]

private lemma c3_centered_v2_recovery_zero {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (χ χ₀ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀)
    (hχ₀c : HasCompactSupport χ₀) (z : Vec d)
    (J : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (∫ y : Vec d,
      (homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
        ((χ (y - z) - χ₀ (y - z) : ℝ) : ℂ)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
      centeredComplexLp Q (∫ y : Vec d, ((χ (y - z) : ℂ) *
        homogenizedGaussianKernel Q i s hs 0 (z - y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) -
      centeredComplexLp Q (∫ y : Vec d, ((χ₀ (y - z) : ℂ) *
        homogenizedGaussianKernel Q i s hs 0 (z - y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) := by
  simpa only [c3_v2_recovery_kernel_zero, neg_sub, mul_comm] using
    c3_centered_v2_cutoff_difference Q i s hs 0 (fun j => Fin.elim0 j)
      χ χ₀ hχ hχc hχ₀ hχ₀c z z J

private lemma c3_centered_v2_recovery_one {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (χ χ₀ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀)
    (hχ₀c : HasCompactSupport χ₀) (z : Vec d)
    (J : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (∫ y : Vec d,
      (fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z)) (unitVector j) *
        ((χ (y - z) - χ₀ (y - z) : ℝ) : ℂ)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
      centeredComplexLp Q (∫ y : Vec d, ((χ (y - z) : ℂ) *
        fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (z - y) (unitVector j)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) -
      centeredComplexLp Q (∫ y : Vec d, ((χ₀ (y - z) : ℂ) *
        fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (z - y) (unitVector j)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) := by
  simpa only [c3_v2_recovery_kernel_one, neg_sub, mul_comm] using
    c3_centered_v2_cutoff_difference Q i s hs 1 (fun _ => j)
      χ χ₀ hχ hχc hχ₀ hχ₀c z z J

private lemma c3_centered_integrate_split_recovery {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (J : Lp ℂ 2 (reducedLaw Q))
    (c₀ c₁ : ℂ) (f a b u v : Vec d → ℂ)
    (h : ∀ y, f y = c₀ * (a y + Complex.I * u y) -
      c₁ * (b y + Complex.I * v y))
    (ha : Integrable (fun y => a y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hb : Integrable (fun y => b y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hu : Integrable (fun y => u y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J))
    (hv : Integrable (fun y => v y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J)) :
    centeredComplexLp Q (∫ y, f y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y J) =
      c₀ • (centeredComplexLp Q (∫ y, a y • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) y J) + Complex.I •
        centeredComplexLp Q (∫ y, u y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y J)) -
      c₁ • (centeredComplexLp Q (∫ y, b y • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) y J) + Complex.I •
        centeredComplexLp Q (∫ y, v y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y J)) := by
  have hrec : ∀ y, f y = (1 : ℂ) *
      ((c₀ * a y - c₁ * b y) + Complex.I * (c₀ * u y - c₁ * v y)) := by
    intro y
    rw [h y]
    ring
  have h' := c3_centered_integrate_four_cutoff_recovery Q J 1 f
    (fun y => c₀ * a y) (fun y => c₁ * b y)
    (fun y => c₀ * u y) (fun y => c₁ * v y) hrec
    (by simpa only [mul_smul] using ha.fun_smul c₀)
    (by simpa only [mul_smul] using hb.fun_smul c₁)
    (by simpa only [mul_smul] using hu.fun_smul c₀)
    (by simpa only [mul_smul] using hv.fun_smul c₁)
  simp only [mul_smul, integral_smul, ← centeredComplexLpCLM_apply,
    map_smul, one_smul] at h'
  simp only [smul_add, smul_sub, smul_smul] at h' ⊢
  rw [mul_comm Complex.I c₀, mul_comm Complex.I c₁] at h'
  simp only [← centeredComplexLpCLM_apply] at ⊢
  convert h' using 1 <;> abel

private lemma c3_cutoff_site_as_split_v2_blocks {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) (c₀ c₁ : ℂ)
    (χ : Vec d → ℝ) (ψ : SchwartzMap (Vec d) ℂ)
    (θ : Bool → Bool → Vec d → ℝ) (baseline : Vec d → ℝ)
    (hθ : ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q))
    (hb : ContDiff ℝ (⊤ : ℕ∞) baseline) (hbc : HasCompactSupport baseline)
    (hrec : ∀ y : Vec d,
      (χ (y - z) : ℂ) * ψ (-y) =
        c₀ * (homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
            ((θ true false (y - z) - baseline (y - z) : ℝ) : ℂ) +
          Complex.I * (homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
            ((θ true true (y - z) - baseline (y - z) : ℝ) : ℂ))) -
        c₁ * (fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z))
            (unitVector j) * ((θ false false (y - z) - baseline (y - z) : ℝ) : ℂ) +
          Complex.I * (fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z))
            (unitVector j) * ((θ false true (y - z) - baseline (y - z) : ℝ) : ℂ)))) :
    let B₀ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * homogenizedGaussianKernel Q i s hs 0 (z - y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
    let B₁ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0)
        (z - y) (unitVector j)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
    centeredComplexLp Q (∫ y : Vec d, ((χ (y - z) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
      c₀ • ((B₀ (θ true false) - B₀ baseline) +
        Complex.I • (B₀ (θ true true) - B₀ baseline)) -
      c₁ • ((B₁ (θ false false) - B₁ baseline) +
        Complex.I • (B₁ (θ false true) - B₁ baseline)) := by
  dsimp only
  have hint := c3_four_site_recovery_components_integrable Q i j s hs θ baseline hθ hb hbc z J
  have heq := c3_centered_integrate_split_recovery Q J c₀ c₁
    (fun y => (χ (y - z) : ℂ) * ψ (-y))
    (fun y => homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
      ((θ true false (y - z) - baseline (y - z) : ℝ) : ℂ))
    (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z)) (unitVector j) *
      ((θ false false (y - z) - baseline (y - z) : ℝ) : ℂ))
    (fun y => homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
      ((θ true true (y - z) - baseline (y - z) : ℝ) : ℂ))
    (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z)) (unitVector j) *
      ((θ false true (y - z) - baseline (y - z) : ℝ) : ℂ))
    hrec hint.1 hint.2.1 hint.2.2.1 hint.2.2.2
  rw [c3_centered_v2_recovery_zero Q i s hs _ _ (hθ true false).1 (hθ true false).2 hb hbc z J,
    c3_centered_v2_recovery_one Q i j s hs _ _ (hθ false false).1 (hθ false false).2 hb hbc z J,
    c3_centered_v2_recovery_zero Q i s hs _ _ (hθ true true).1 (hθ true true).2 hb hbc z J,
    c3_centered_v2_recovery_one Q i j s hs _ _ (hθ false true).1 (hθ false true).2 hb hbc z J] at heq
  exact heq

lemma c3_cutoff_site_as_eight_v2_blocks_split {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (z : Vec d) (J : Lp ℂ 2 (reducedLaw Q)) (c₀ c₁ : ℂ)
    (χ : Vec d → ℝ) (ψ : SchwartzMap (Vec d) ℂ)
    (θ : Bool → Bool → Vec d → ℝ) (baseline : Vec d → ℝ)
    (hθ : ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q))
    (hb : ContDiff ℝ (⊤ : ℕ∞) baseline) (hbc : HasCompactSupport baseline)
    (hrec : ∀ y : Vec d,
      (χ (y - z) : ℂ) * ψ (-y) =
        c₀ * homogenizedGaussianKernel Q i s hs 0 (-(y - z)) *
          (((θ true false (y - z) - baseline (y - z) : ℝ) : ℂ) +
            Complex.I * ((θ true true (y - z) - baseline (y - z) : ℝ) : ℂ)) -
        c₁ * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(y - z)) (unitVector j) *
          (((θ false false (y - z) - baseline (y - z) : ℝ) : ℂ) +
            Complex.I * ((θ false true (y - z) - baseline (y - z) : ℝ) : ℂ))) :
    let B₀ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * homogenizedGaussianKernel Q i s hs 0 (z - y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
    let B₁ := fun ξ : Vec d → ℝ => centeredComplexLp Q (∫ y : Vec d,
      ((ξ (y - z) : ℂ) * fderiv ℝ (homogenizedGaussianKernel Q i s hs 0)
        (z - y) (unitVector j)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J)
    centeredComplexLp Q (∫ y : Vec d, ((χ (y - z) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J) =
      c₀ • ((B₀ (θ true false) - B₀ baseline) +
        Complex.I • (B₀ (θ true true) - B₀ baseline)) -
      c₁ • ((B₁ (θ false false) - B₁ baseline) +
        Complex.I • (B₁ (θ false true) - B₁ baseline)) := by
  apply c3_cutoff_site_as_split_v2_blocks Q i j s hs z J c₀ c₁ χ ψ θ baseline hθ hb hbc
  intro y
  rw [hrec y]
  ring

end EinsteinFull.Blueprint
