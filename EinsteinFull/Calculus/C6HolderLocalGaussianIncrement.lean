import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.G2.Proofs.W4BootstrapPoint
import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeBoundSupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
private lemma normalized_rpow_bound (u α : ℝ) (hu : 0 ≤ u)
    (hα : 0 < α) (hα1 : α ≤ 1) : u ^ α ≤ 1 + u ^ 2 := by
  by_cases hu1 : u ≤ 1
  · exact (Real.rpow_le_one hu hu1 hα.le).trans (by linarith [sq_nonneg u])
  · have h : u ^ α ≤ u ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hu1) (by linarith)
    rw [Real.rpow_two] at h
    linarith

private lemma scaled_rpow_bound (r s α : ℝ) (hr : 0 ≤ r) (hs : 0 < s)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    r ^ α ≤ s ^ (α / 2) * (1 + r ^ 2 / s) := by
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h := normalized_rpow_bound (r / Real.sqrt s) α (by positivity) hα hα1
  have hp : (Real.sqrt s) ^ α = s ^ (α / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    congr 1
    ring
  rw [div_pow, Real.sq_sqrt hs.le, Real.div_rpow hr hroot.le, hp] at h
  simpa only [mul_comm] using (div_le_iff₀ (Real.rpow_pos_of_pos hs _)).mp h

private lemma polynomial_gaussian_absorption (b v : ℝ) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    (1 + b * v) * Real.exp (-2 * v) ≤ (1 + b) * Real.exp (-v) := by
  have h1 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : v * Real.exp (-v) ≤ 1 := by
    calc
      _ ≤ Real.exp v * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right zero_le_one).trans
          (Real.add_one_le_exp v)) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h3 : (1 + b * v) * Real.exp (-v) ≤ 1 + b := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hb]
  calc
    _ = ((1 + b * v) * Real.exp (-v)) * Real.exp (-v) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

private lemma gaussian_holder_envelope {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (s α : ℝ) (hs : 0 < s)
    (hα : 0 < α) (hα1 : α ≤ 1) (x : Vec d) :
    euclideanNorm x ^ α * anisotropicGaussian (homogenizedCoefficient Q) s x ≤
      (s ^ (α / 2) * ((1 + 4 * sourceReducedBound Λ) *
        (4 : ℝ) ^ ((d : ℝ) / 2))) *
        anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by
  let K := sourceReducedBound Λ
  let q := dot x ((homogenizedCoefficient Q)⁻¹.mulVec x)
  let c := (2 * Real.pi * s) ^ (-(d : ℝ) / 2) /
    Real.sqrt (homogenizedCoefficient Q).det
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg Λ])
  have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  have hsq : euclideanNorm x ^ 2 = euclideanSq x := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
  have hquad := (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  have hbound : euclideanNorm x ^ 2 ≤ K * q := by
    change K⁻¹ * euclideanSq x ≤ q at hquad
    have h := mul_le_mul_of_nonneg_left hquad hK.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul, hsq] using h
  have hq : 0 ≤ q := by nlinarith [sq_nonneg (euclideanNorm x)]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he : anisotropicGaussian (homogenizedCoefficient Q) s x =
      c * Real.exp (-q / (2 * s)) := by
    dsimp [anisotropicGaussian, c, q]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hpoly : 1 + euclideanNorm x ^ 2 / s ≤ 1 + K * q / s := by
    exact add_le_add_right (div_le_div_of_nonneg_right hbound hs.le) 1
  have habs := polynomial_gaussian_absorption (4 * K) (q / (4 * s))
    (by positivity) (by positivity)
  have habs' : (1 + K * q / s) * Real.exp (-q / (2 * s)) ≤
      (1 + 4 * K) * Real.exp (-q / (8 * s)) := by
    have heq : 4 * K * (q / (4 * s)) = K * q / s := by ring
    have heq' : -2 * (q / (4 * s)) = -q / (2 * s) := by ring
    rw [heq, heq'] at habs
    exact habs.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        simp only [← neg_div]
        apply (div_le_div_iff₀ (by positivity : 0 < 4 * s)
          (by positivity : 0 < 8 * s)).mpr
        nlinarith)) (by positivity))
  have hfour := anisotropicGaussian_four_time (homogenizedCoefficient Q) s hs x
  have hfour' : c * Real.exp (-q / (8 * s)) =
      (4 : ℝ) ^ ((d : ℝ) / 2) *
        anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by
    convert hfour using 1
    dsimp [c, q]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  calc
    _ ≤ (s ^ (α / 2) * (1 + euclideanNorm x ^ 2 / s)) *
        anisotropicGaussian (homogenizedCoefficient Q) s x :=
      mul_le_mul_of_nonneg_right (scaled_rpow_bound _ s α hn hs hα hα1)
        (by dsimp [anisotropicGaussian]; positivity)
    _ ≤ (s ^ (α / 2) * (1 + K * q / s)) *
        (c * Real.exp (-q / (2 * s))) := by
      rw [he]
      gcongr
    _ = (s ^ (α / 2) * c) * ((1 + K * q / s) * Real.exp (-q / (2 * s))) := by ring
    _ ≤ (s ^ (α / 2) * c) * ((1 + 4 * K) * Real.exp (-q / (8 * s))) :=
      mul_le_mul_of_nonneg_left habs' (by positivity)
    _ = (s ^ (α / 2) * (1 + 4 * K)) * (c * Real.exp (-q / (8 * s))) := by ring
    _ = _ := by rw [hfour']; ring

private lemma gaussian_local_tail_envelope {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (s R : ℝ) (hs : 0 < s) (hR : 0 < R)
    (x : Vec d) (hx : R ≤ euclideanNorm x) :
    anisotropicGaussian (homogenizedCoefficient Q) s x ≤
      (Real.exp (-(1 / (8 * sourceReducedBound Λ)) * R ^ 2 / s) *
        (4 : ℝ) ^ ((d : ℝ) / 2)) *
        anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by
  let K := sourceReducedBound Λ
  let q := dot x ((homogenizedCoefficient Q)⁻¹.mulVec x)
  let b := (2 * Real.pi * s) ^ (-(d : ℝ) / 2) /
    Real.sqrt (homogenizedCoefficient Q).det
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg Λ])
  have hsq : euclideanNorm x ^ 2 = euclideanSq x := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
  have hquad := (homogenizedCoefficient_inv_quadratic_bounds Q x).1
  have hnq : euclideanNorm x ^ 2 ≤ K * q := by
    change K⁻¹ * euclideanSq x ≤ q at hquad
    have h := mul_le_mul_of_nonneg_left hquad hK.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul, hsq] using h
  have hRq : R ^ 2 ≤ K * q := (pow_le_pow_left₀ hR.le hx 2).trans hnq
  have hq : 0 ≤ q := by nlinarith [sq_nonneg (euclideanNorm x)]
  have he : -q / (2 * s) ≤ -(1 / (8 * K)) * R ^ 2 / s + -q / (8 * s) := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < 8 * K * s by positivity)).mp
    field_simp
    nlinarith
  have hfour : b * Real.exp (-q / (8 * s)) =
      (4 : ℝ) ^ ((d : ℝ) / 2) *
        anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by
    convert anisotropicGaussian_four_time (homogenizedCoefficient Q) s hs x using 1
    dsimp [b, q]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hg : anisotropicGaussian (homogenizedCoefficient Q) s x =
      b * Real.exp (-q / (2 * s)) := by
    dsimp [anisotropicGaussian, b, q]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  calc
    _ ≤ b * Real.exp (-(1 / (8 * K)) * R ^ 2 / s + -q / (8 * s)) := by
      rw [hg]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by dsimp [b]; positivity)
    _ = Real.exp (-(1 / (8 * K)) * R ^ 2 / s) * (b * Real.exp (-q / (8 * s))) := by
      rw [Real.exp_add]; ring
    _ = _ := by rw [hfour]; ring

/-- Local stationary Hölder increments control Gaussian unsmoothing, with an
exponentially small error from translations outside the prescribed radius. -/
theorem holder_gaussian_unsmoothing_of_local_increment_bound :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p α : ℝ),
  2 ≤ p → 0 < α → α ≤ 1 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (f : Lp ℂ 2 (reducedLaw Q)) (A M R : ℝ),
    0 ≤ A → 0 ≤ M → 0 < R →
    MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M →
    (∀ x : Vec d, euclideanNorm x ≤ R →
      eLpNorm (fun ω => f (translate x ω) - f ω)
        (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (A * (euclideanNorm x / R) ^ α)) →
    ∀ (s : ℝ) (hs : 0 < s), s ≤ R ^ 2 →
      MemLp ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (C * (A * (s / R ^ 2) ^ (α / 2) +
          M * Real.exp (-c * R ^ 2 / s))) := by
  intro d hd D p α hp hα hα1
  let K := sourceReducedBound D.ellipticity
  let H := (4 : ℝ) ^ ((d : ℝ) / 2)
  let C := (1 + 4 * K) * H + 2 * H
  let c := 1 / (8 * K)
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg D.ellipticity])
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨C, c, by dsimp [C]; positivity, by dsimp [c]; positivity, ?_⟩
  intro Q f A M R hA hM hR hf hfM hinc s hs _hsR
  let B := C * (A * (s / R ^ 2) ^ (α / 2) + M * Real.exp (-c * R ^ 2 / s))
  let := reducedLaw_probability Q
  let q := ENNReal.ofReal p
  have hq : 2 ≤ q := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  let : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  let : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let : PolishSpace (FieldPair d) := inferInstance
  let fp : Lp ℂ q (reducedLaw Q) := hf.toLp f
  let τ : Vec d → Lp ℂ q (reducedLaw Q) →ₗᵢ[ℂ] Lp ℂ q (reducedLaw Q) :=
    fun x => Lp.compMeasurePreservingₗᵢ ℂ (translate x)
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
  have hc : Continuous (fun x : Vec d => τ x fp) := by
    let g : Vec d → C(FieldPair d, FieldPair d) := fun x =>
      ⟨translate x, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
    have hg : Continuous g := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact Probability.continuous_translate
    exact continuous_const.compMeasurePreservingLp hg
      (fun x => measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
      ENNReal.ofReal_ne_top
  let i : Fin d := ⟨0, by omega⟩
  let k := homogenizedGaussianKernel Q i s hs 0
  have hk : Continuous k := by
    change Continuous (fun x : Vec d => homogenizedGaussianKernel Q i s hs 0 x)
    unfold homogenizedGaussianKernel
    fun_prop
  have hki : Integrable k := integrable_homogenizedGaussianKernel Q i s hs 0
  have hkreal (x : Vec d) : k x =
      (anisotropicGaussian (homogenizedCoefficient Q) s x : ℂ) :=
    homogenizedGaussianKernel_zero_eq_ofReal Q i s hs x
  have hknorm (x : Vec d) : ‖k x‖ = anisotropicGaussian (homogenizedCoefficient Q) s x := by
    rw [hkreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    unfold anisotropicGaussian
    positivity
  have hkm : ∫ x, k x = 1 := by
    simp_rw [hkreal]
    rw [integral_complex_ofReal, integral_anisotropicGaussian _
      (posDef_homogenizedCoefficient Q) s hs, Complex.ofReal_one]
  have hi : Integrable (fun x : Vec d => k x • τ x fp) := by
    apply Integrable.mono' (hki.norm.mul_const ‖fp‖) (hk.fun_smul hc).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by rw [norm_smul, (τ x).norm_map]
  have hi0 : Integrable (fun x : Vec d => k x • fp) := hki.smul_const fp
  have hid : Integrable (fun x : Vec d => k x • (fp - τ x fp)) := by
    have heq : (fun x : Vec d => k x • (fp - τ x fp)) =
        (fun x : Vec d => k x • fp) - (fun x : Vec d => k x • τ x fp) := by
      funext x
      exact smul_sub (k x) fp (τ x fp)
    rw [heq]
    exact hi0.sub hi
  let v := ∫ x : Vec d, k x • (fp - τ x fp)
  have hfp : complexLpToL2 (reducedLaw Q) hq fp = f := by
    apply Lp.ext
    exact hf.coeFn_toLp
  have hτ (x : Vec d) : complexLpToL2 (reducedLaw Q) hq (τ x fp) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f := by
    rw [← hfp]
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving fp
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)).trans
      (coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexLpToL2 (reducedLaw Q) hq fp)).symm
  have hv : complexLpToL2 (reducedLaw Q) hq v = f - gaussianAverage hd Q s hs f := by
    change (complexLpToL2CLM (reducedLaw Q) hq) v = _
    dsimp only [v]
    rw [← ContinuousLinearMap.integral_comp_comm _ hid]
    change (∫ x : Vec d, complexLpToL2 (reducedLaw Q) hq (k x • (fp - τ x fp))) = _
    simp_rw [map_smul, map_sub, hfp, hτ, smul_sub]
    rw [integral_sub (hki.smul_const f)
      (integrable_kernel_complexTranslation _ _ k hki hk f), integral_smul_const, hkm, one_smul]
    rfl
  have hnorm (x : Vec d) (hx : euclideanNorm x ≤ R) :
      ‖fp - τ x fp‖ ≤ A * (euclideanNorm x / R) ^ α := by
    have heq : (fun ω => (fp - τ x fp) ω) =ᵐ[reducedLaw Q]
        (fun ω => f ω - f (translate x ω)) := by
      filter_upwards [Lp.coeFn_sub fp (τ x fp), hf.coeFn_toLp,
        Lp.coeFn_compMeasurePreserving fp
          (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x),
        (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hf.coeFn_toLp]
        with ω hsub hf0 hcomp hftrans
      exact hsub.trans (congrArg₂ (· - ·) hf0 (hcomp.trans hftrans))
    rw [Lp.norm_def, eLpNorm_congr_ae heq]
    have he : eLpNorm (fun ω => f ω - f (translate x ω)) q (reducedLaw Q) =
        eLpNorm (fun ω => f (translate x ω) - f ω) q (reducedLaw Q) := by
      have hfun : (fun ω => f ω - f (translate x ω)) =
          -(fun ω => f (translate x ω) - f ω) := by
        funext ω
        exact (neg_sub _ _).symm
      rw [hfun, eLpNorm_neg]
    rw [he]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hinc x hx)).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hA (Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) hR.le) _)))
  have hfpM : ‖fp‖ ≤ M := by
    rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfM).trans_eq
      (ENNReal.toReal_ofReal hM)
  have hglobal (x : Vec d) : ‖fp - τ x fp‖ ≤ 2 * M := by
    calc
      _ ≤ ‖fp‖ + ‖τ x fp‖ := norm_sub_le _ _
      _ = 2 * ‖fp‖ := by rw [(τ x).norm_map]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfpM (by norm_num)
  have hratio : s ^ (α / 2) / R ^ α = (s / R ^ 2) ^ (α / 2) := by
    rw [Real.div_rpow hs.le (sq_nonneg R), ← Real.rpow_natCast_mul hR.le]
    congr 2
    ring
  have hnearC : (1 + 4 * K) * H ≤ C := by
    exact le_add_of_nonneg_right (by positivity)
  have hfarC : 2 * H ≤ C := by
    exact le_add_of_nonneg_left (by positivity)
  have hnearB : A / R ^ α * (s ^ (α / 2) * ((1 + 4 * K) * H)) ≤ B := by
    have ht : 0 ≤ A * (s / R ^ 2) ^ (α / 2) := by positivity
    have heq : A / R ^ α * (s ^ (α / 2) * ((1 + 4 * K) * H)) =
        ((1 + 4 * K) * H) * (A * (s / R ^ 2) ^ (α / 2)) := by
      rw [← hratio]; ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hnearC ht).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by dsimp [C]; positivity))
  have hfarB : 2 * M * (Real.exp (-c * R ^ 2 / s) * H) ≤ B := by
    have ht : 0 ≤ M * Real.exp (-c * R ^ 2 / s) := by positivity
    calc
      _ = (2 * H) * (M * Real.exp (-c * R ^ 2 / s)) := by ring
      _ ≤ C * (M * Real.exp (-c * R ^ 2 / s)) := mul_le_mul_of_nonneg_right hfarC ht
      _ ≤ B := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by dsimp [C]; positivity)
  have hmajor (x : Vec d) : ‖k x • (fp - τ x fp)‖ ≤
      B * anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by
    have hg0 : 0 ≤ anisotropicGaussian (homogenizedCoefficient Q) s x := by
      unfold anisotropicGaussian; positivity
    have hg4 : 0 ≤ anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by
      unfold anisotropicGaussian; positivity
    rw [norm_smul, hknorm]
    by_cases hx : euclideanNorm x ≤ R
    · calc
        _ ≤ anisotropicGaussian (homogenizedCoefficient Q) s x *
            (A * (euclideanNorm x / R) ^ α) := mul_le_mul_of_nonneg_left (hnorm x hx) hg0
        _ = (A / R ^ α) * (euclideanNorm x ^ α *
            anisotropicGaussian (homogenizedCoefficient Q) s x) := by
          rw [Real.div_rpow (show 0 ≤ euclideanNorm x from Real.sqrt_nonneg _) hR.le]; ring
        _ ≤ (A / R ^ α) * ((s ^ (α / 2) * ((1 + 4 * K) * H)) *
            anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x) :=
          mul_le_mul_of_nonneg_left (gaussian_holder_envelope Q s α hs hα hα1 x) (by positivity)
        _ = (A / R ^ α * (s ^ (α / 2) * ((1 + 4 * K) * H))) *
            anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hnearB hg4
    · calc
        _ ≤ anisotropicGaussian (homogenizedCoefficient Q) s x * (2 * M) :=
          mul_le_mul_of_nonneg_left (hglobal x) hg0
        _ ≤ ((Real.exp (-c * R ^ 2 / s) * H) *
            anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x) * (2 * M) :=
          mul_le_mul_of_nonneg_right
            (gaussian_local_tail_envelope Q s R hs hR x (le_of_not_ge hx)) (by positivity)
        _ = (2 * M * (Real.exp (-c * R ^ 2 / s) * H)) *
            anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfarB hg4
  have hvnorm : ‖v‖ ≤ B := by
    calc
      _ ≤ ∫ x : Vec d, B * anisotropicGaussian (homogenizedCoefficient Q) (4 * s) x :=
        norm_integral_le_of_norm_le
          ((integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q)
            (4 * s) (by positivity)).const_mul B) (Filter.Eventually.of_forall hmajor)
      _ = B := by
        rw [integral_const_mul, integral_anisotropicGaussian _
          (posDef_homogenizedCoefficient Q) _ (by positivity), mul_one]
  have hcoe : ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ) =ᵐ[reducedLaw Q] v := by
    exact (Lp.coeFn_sub f _).symm.trans (by rw [← hv]; rfl)
  constructor
  · exact MemLp.ae_eq hcoe.symm (Lp.memLp v)
  · rw [eLpNorm_congr_ae hcoe, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hvnorm

end EinsteinFull.Blueprint
