import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Blueprint.G1.Proofs.S3RealSemigroup

/-!
# Translation averages on the stationary `L²` carrier

`tavg Q k f = ∫ k(x) • T_x f dx` for an integrable continuous complex kernel `k`. The Gaussian
averages of the paper (`gaussianAverage`, `homogeneousAverage`, `gaussianDerivativeAverage`) are
instances. Two kernels commute, and the bilinear transpose of `tavg k` is `tavg (k ∘ neg)`.
-/

open MeasureTheory

noncomputable section

namespace EinsteinFull.S3Dual

open EinsteinRelation EinsteinFull

variable {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)

/-- The translation average with kernel `k`. -/
def tavg (k : Vec d → ℂ) (f : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  ∫ x : Vec d, k x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f

theorem integrable_tavg {k : Vec d → ℂ} (hk : Integrable k) (hc : Continuous k)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => k x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  letI := reducedLaw_probability Q
  exact integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) k hk hc f

/-- Translation commutes with a translation average. -/
theorem translation_tavg {k : Vec d → ℂ} (hk : Integrable k) (hc : Continuous k) (x : Vec d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (tavg Q k f) =
      ∫ y : Vec d, k y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (x + y) f := by
  change (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap
    (∫ y : Vec d, k y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f) = _
  rw [← (complexTranslation _ _ x).toContinuousLinearMap.integral_comp_comm
    (integrable_tavg Q hk hc f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul, complexTranslation_add]

theorem integrable_tavg_product {k₁ k₂ : Vec d → ℂ} (h1 : Integrable k₁) (c1 : Continuous k₁)
    (h2 : Integrable k₂) (c2 : Continuous k₂) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : Vec d × Vec d => (k₁ p.1 * k₂ p.2) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (p.1 + p.2) f)
      (volume.prod volume) := by
  letI := reducedLaw_probability Q
  have hT : Continuous (fun p : Vec d × Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (p.1 + p.2) f) :=
    (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
      ((continuous_fst.add continuous_snd).prodMk continuous_const)
  refine ((h1.norm.mul_prod h2.norm).mul_const ‖f‖).mono'
    ((((c1.comp continuous_fst).mul (c2.comp continuous_snd)).smul hT).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun p => by
    simp only [norm_smul, norm_mul, norm_complexTranslation, le_refl]

/-- Two translation averages commute. -/
theorem tavg_comm {k₁ k₂ : Vec d → ℂ} (h1 : Integrable k₁) (c1 : Continuous k₁)
    (h2 : Integrable k₂) (c2 : Continuous k₂) (f : Lp ℂ 2 (reducedLaw Q)) :
    tavg Q k₁ (tavg Q k₂ f) = tavg Q k₂ (tavg Q k₁ f) := by
  have hp := integrable_tavg_product Q h1 c1 h2 c2 f
  have e : ∀ (a b : Vec d → ℂ) (ha : Integrable a) (ca : Continuous a)
      (hb : Integrable b) (cb : Continuous b),
      tavg Q a (tavg Q b f) = ∫ x : Vec d, ∫ y : Vec d, (a x * b y) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (x + y) f := by
    intro a b ha ca hb cb
    unfold tavg
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x => ?_
    dsimp only
    have := translation_tavg Q hb cb x f
    unfold tavg at this
    rw [this, ← integral_smul]
    simp only [smul_smul]
  rw [e k₁ k₂ h1 c1 h2 c2, e k₂ k₁ h2 c2 h1 c1, integral_integral_swap hp]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [mul_comm (k₂ y) (k₁ x), add_comm y x]

/-- Bilinear transpose of a translation. -/
theorem integral_translation_mul (x : Vec d) (f g : Lp ℂ 2 (reducedLaw Q)) :
    ∫ ω, (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) ω * g ω
        ∂reducedLaw Q =
      ∫ ω, f ω * (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g) ω
        ∂reducedLaw Q := by
  rw [← lpStar_inner_eq_integral, ← lpStar_inner_eq_integral]
  have h := (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).inner_map_map
    (star f) (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g)
  rw [complexTranslation_star] at h
  have h2 : complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g) = g := by
    simpa using complexTranslation_neg_cancel (reducedLaw Q) (reducedLaw_stationary Q) (-x) g
  rw [h2] at h
  exact h

/-- Pairing a translation average with a test class. -/
theorem integral_tavg_mul {k : Vec d → ℂ} (hk : Integrable k) (hc : Continuous k)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    ∫ ω, (tavg Q k f) ω * g ω ∂reducedLaw Q =
      ∫ x : Vec d, k x * ∫ ω, f ω *
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g) ω
          ∂reducedLaw Q := by
  have hL : ∀ u : Lp ℂ 2 (reducedLaw Q),
      ∫ ω, u ω * g ω ∂reducedLaw Q = innerSL ℂ (star g) u := by
    intro u
    rw [innerSL_apply_apply, lpStar_inner_eq_integral]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  rw [hL, tavg, ← (innerSL ℂ (star g)).integral_comp_comm (integrable_tavg Q hk hc f)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [map_smul, smul_eq_mul, ← hL, integral_translation_mul]

/-- The bilinear transpose of a translation average has the reflected kernel. -/
theorem integral_tavg_mul_eq {k : Vec d → ℂ} (hk : Integrable k) (hc : Continuous k)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    ∫ ω, (tavg Q k f) ω * g ω ∂reducedLaw Q =
      ∫ ω, f ω * (tavg Q (fun x => k (-x)) g) ω ∂reducedLaw Q := by
  have hk' : Integrable (fun x => k (-x)) := hk.comp_neg
  have hc' : Continuous (fun x => k (-x)) := hc.comp continuous_neg
  have hL : ∀ u : Lp ℂ 2 (reducedLaw Q),
      ∫ ω, f ω * u ω ∂reducedLaw Q = innerSL ℂ (star f) u := by
    intro u
    rw [innerSL_apply_apply, lpStar_inner_eq_integral]
  rw [integral_tavg_mul Q hk hc, hL, tavg, ← (innerSL ℂ (star f)).integral_comp_comm
    (integrable_tavg Q hk' hc' g)]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [map_smul, smul_eq_mul, neg_neg, ← hL]

end EinsteinFull.S3Dual
