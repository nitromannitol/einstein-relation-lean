import EinsteinRelation.Correctors.RadialPoissonKernelSmooth
import EinsteinRelation.Correctors.HeatTransferIdentity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Actual radial dyadic averaging and Poisson kernels

Source: `paper/main.tex:1003–1025`, Step 1 of Proposition 6.1. A fixed radial
smooth bump is normalized in the actual coordinate Lebesgue measure. Its
dyadic differences have zero radial mass and hence explicit compact Poisson
kernels. These are the isotropic kernels before the homogenized linear change
of coordinates.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- A smooth radial profile constant near zero gives a smooth spatial function
(`paper/main.tex:1003–1010`). -/
theorem contDiff_radial_of_flat {d : ℕ} {b : ℝ → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t, 0 ≤ t → t < ε → b t = b 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => b (euclideanNorm x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hO : IsOpen {y : Vec d | euclideanNorm y < ε} :=
      isOpen_lt euclideanNorm_continuous continuous_const
    apply (contDiffAt_const (c := b 0)).congr_of_eventuallyEq
    apply Filter.eventually_of_mem (hO.mem_nhds (by
      simpa only [Set.mem_setOf_eq, euclideanNorm_zero_vec] using hε))
    exact fun y hy => hflat _ (Real.sqrt_nonneg _) hy
  · exact hb.contDiffAt.comp x
      (euclideanNorm_contDiffAt _ (euclideanNorm_pos_of_ne_zero hx))

/-- A radial profile vanishing beyond a finite radius has compact spatial
support (`paper/main.tex:1003–1010`). -/
theorem hasCompactSupport_radial_of_tail_zero {d : ℕ} {b : ℝ → ℝ} {ρ : ℝ}
    (hzero : ∀ t, ρ ≤ t → b t = 0) :
    HasCompactSupport (fun x : Vec d => b (euclideanNorm x)) := by
  refine HasCompactSupport.intro
    (isCompact_univ_pi fun _ : Fin d => isCompact_Icc (a := -ρ) (b := ρ)) ?_
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ∉ Set.Icc (-ρ) ρ := by
    by_contra hn
    push_neg at hn
    exact hx (fun i _ => hn i)
  have hlt : ρ < |x i| := by
    by_contra hn
    exact hi (abs_le.mp (not_lt.mp hn))
  exact hzero _ (hlt.le.trans (abs_coord_le_euclideanNorm x i))

private def profileBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem profileBump_flat {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1 / 2) :
    profileBump t = 1 := by
  apply profileBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg ht]
    using ht'.le

private theorem profileBump_tail {t : ℝ} (ht : 1 ≤ t) : profileBump t = 0 := by
  apply profileBump.zero_of_le_dist
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : 0 ≤ t)] using ht

private theorem profileBump_radial_smooth (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => profileBump (euclideanNorm x)) := by
  apply contDiff_radial_of_flat profileBump.contDiff (by norm_num : (0 : ℝ) < 1 / 2)
  intro t ht ht'
  rw [profileBump_flat ht ht', profileBump_flat (by norm_num) (by norm_num)]

private theorem profileBump_radial_compact (d : ℕ) :
    HasCompactSupport (fun x : Vec d => profileBump (euclideanNorm x)) :=
  hasCompactSupport_radial_of_tail_zero (fun _ ht => profileBump_tail ht)

private def profileMass (d : ℕ) : ℝ := ∫ x : Vec d, profileBump (euclideanNorm x)

private theorem profileMass_pos (d : ℕ) : 0 < profileMass d := by
  apply (profileBump_radial_smooth d).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (profileBump_radial_compact d) (fun _ => profileBump.nonneg) (x := 0)
  rw [euclideanNorm_zero_vec, profileBump_flat (by norm_num) (by norm_num)]
  norm_num

/-- The fixed normalized radial profile for Step 1 of Proposition 6.1
(`paper/main.tex:1003–1007`). -/
def radialMollifierProfile (d : ℕ) (t : ℝ) : ℝ := (profileMass d)⁻¹ * profileBump t

theorem radialMollifierProfile_contDiff (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialMollifierProfile d) :=
  contDiff_const.mul profileBump.contDiff

theorem radialMollifierProfile_nonneg (d : ℕ) (t : ℝ) :
    0 ≤ radialMollifierProfile d t :=
  mul_nonneg (inv_nonneg.mpr (profileMass_pos d).le) profileBump.nonneg

theorem radialMollifierProfile_tail (d : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    radialMollifierProfile d t = 0 := by
  simp only [radialMollifierProfile, profileBump_tail ht, mul_zero]

theorem radialMollifierProfile_flat (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1 / 2) :
    radialMollifierProfile d t = radialMollifierProfile d 0 := by
  simp only [radialMollifierProfile, profileBump_flat ht ht',
    profileBump_flat (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1 / 2)]

theorem integral_radialMollifierProfile (d : ℕ) :
    (∫ x : Vec d, radialMollifierProfile d (euclideanNorm x)) = 1 := by
  simp only [radialMollifierProfile]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (profileMass_pos d).ne'

/-- The scale-`r` radial averaging kernel, before the homogenized change of
coordinates (`paper/main.tex:1003–1007`). -/
def radialAverage (d : ℕ) (r : ℝ) (x : Vec d) : ℝ :=
  scaledProfile d r (radialMollifierProfile d) (euclideanNorm x)

theorem radialAverage_contDiff {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (radialAverage d r) := by
  exact contDiff_radial_of_flat
    (scaledProfile_contDiff (d := d) (radialMollifierProfile_contDiff d))
    (mul_pos hr (by norm_num : (0 : ℝ) < 1 / 2))
    (scaledProfile_flat (d := d) hr (fun _ ht ht' => radialMollifierProfile_flat d ht ht'))

theorem radialAverage_tail {d : ℕ} {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : r ≤ euclideanNorm x) : radialAverage d r x = 0 := by
  apply scaledProfile_eq_zero_of_ge hr (fun _ ht => radialMollifierProfile_tail d ht)
  simpa only [mul_one] using hx

theorem radialAverage_hasCompactSupport {d : ℕ} {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (radialAverage d r) := by
  exact hasCompactSupport_radial_of_tail_zero (fun _ ht =>
    scaledProfile_eq_zero_of_ge hr (fun _ hs => radialMollifierProfile_tail d hs)
      (by simpa only [mul_one] using ht))

theorem radialAverage_nonneg (d : ℕ) (r : ℝ) (hr : 0 < r) (x : Vec d) :
    0 ≤ radialAverage d r x :=
  mul_nonneg (inv_nonneg.mpr (pow_pos hr _).le) (radialMollifierProfile_nonneg d _)

theorem integral_radialAverage {d : ℕ} {r : ℝ} (hr : 0 < r) :
    (∫ x : Vec d, radialAverage d r x) = 1 := by
  have hfun : radialAverage d r = fun x : Vec d =>
      (r ^ d)⁻¹ * radialMollifierProfile d (euclideanNorm (r⁻¹ • x)) := by
    funext x
    simp only [radialAverage, scaledProfile, TimeChange.euclideanNorm_smul,
      abs_of_pos (inv_pos.mpr hr), div_eq_inv_mul]
  have hchange := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x : Vec d => radialMollifierProfile d (euclideanNorm x)) r⁻¹
  rw [hfun, integral_const_mul, hchange]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, inv_pow,
    inv_inv, abs_of_pos (pow_pos hr d), smul_eq_mul, integral_radialMollifierProfile,
    mul_one, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]

/-- The unscaled zero-mass dyadic source (`paper/main.tex:1009–1018`). -/
def radialBandProfile (d : ℕ) (t : ℝ) : ℝ :=
  radialMollifierProfile d t - scaledProfile d 2 (radialMollifierProfile d) t

theorem radialBandProfile_contDiff (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialBandProfile d) :=
  (radialMollifierProfile_contDiff d).sub
    (scaledProfile_contDiff (d := d) (radialMollifierProfile_contDiff d))

theorem radialBandProfile_tail (d : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    radialBandProfile d t = 0 := by
  rw [radialBandProfile, radialMollifierProfile_tail d (by linarith),
    scaledProfile_eq_zero_of_ge (by norm_num : (0 : ℝ) < 2)
      (fun _ hs => radialMollifierProfile_tail d hs) (by simpa using ht), sub_self]

theorem radialBandProfile_flat (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1 / 2) :
    radialBandProfile d t = radialBandProfile d 0 := by
  have hsc := scaledProfile_flat (d := d) (ε := (1 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 2)
    (fun s hs hs' => radialMollifierProfile_flat d (t := s) hs hs') t ht (by linarith)
  rw [radialBandProfile, radialBandProfile, radialMollifierProfile_flat d ht ht', hsc]

theorem radialBandProfile_mass {d : ℕ} (hd : 2 ≤ d) :
    radialMass d (radialBandProfile d) 2 = 0 := by
  have hb := (radialMollifierProfile_contDiff d).continuous
  have hsc := (scaledProfile_contDiff (d := d) (r := 2)
    (radialMollifierProfile_contDiff d)).continuous
  have htail : (∫ t in (1 : ℝ)..2, radialMollifierProfile d t * t ^ (d - 1)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact ae_of_all _ fun t ht => by
      rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      rw [radialMollifierProfile_tail d ht.1.le, zero_mul]
  have hmass : radialMass d (radialMollifierProfile d) 2 =
      radialMass d (radialMollifierProfile d) 1 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      ((hb.mul (continuous_pow (d - 1))).intervalIntegrable (μ := volume) 0 1)
      ((hb.mul (continuous_pow (d - 1))).intervalIntegrable (μ := volume) 1 2)
    rw [htail, add_zero] at hadd
    exact hadd.symm
  change (∫ t in (0 : ℝ)..2,
    (radialMollifierProfile d t - scaledProfile d 2 (radialMollifierProfile d) t) *
      t ^ (d - 1)) = 0
  simp only [sub_mul]
  rw [intervalIntegral.integral_sub ((hb.mul (continuous_pow (d - 1))).intervalIntegrable _ _)
    ((hsc.mul (continuous_pow (d - 1))).intervalIntegrable _ _)]
  change radialMass d (radialMollifierProfile d) 2 -
    radialMass d (scaledProfile d 2 (radialMollifierProfile d)) 2 = 0
  have hm2 : radialMass d (scaledProfile d 2 (radialMollifierProfile d)) 2 =
      radialMass d (radialMollifierProfile d) 1 := by
    simpa only [mul_one] using radialMass_scaledProfile (g := radialMollifierProfile d)
      hd (by norm_num : (0 : ℝ) < 2) 1
  rw [hm2, hmass, sub_self]

/-- The scaled dyadic source is exactly the difference of consecutive
averaging kernels (`paper/main.tex:1009–1025`). -/
theorem scaledProfile_radialBandProfile (d : ℕ) (r t : ℝ) :
    scaledProfile d r (radialBandProfile d) t =
      scaledProfile d r (radialMollifierProfile d) t -
        scaledProfile d (2 * r) (radialMollifierProfile d) t := by
  simp only [scaledProfile, radialBandProfile, mul_sub, mul_pow, mul_inv_rev, div_div]
  rw [mul_comm r 2]
  ring

/-- The explicit compact radial solution of
`ΔK_r = θ_r - θ_{2r}` (`paper/main.tex:1009–1025`). The factor two for the
paper's operator `Δ/2` is applied after transporting the kernel. -/
def radialBandKernel (d : ℕ) (r : ℝ) : Vec d → ℝ :=
  radialKernel d (scaledProfile d r (radialBandProfile d)) (r * 2)

theorem radialBandKernel_contDiff {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (radialBandKernel d r) :=
  radialKernel_contDiff hd (scaledProfile_contDiff (d := d) (radialBandProfile_contDiff d))
    (mul_pos hr (by norm_num : (0 : ℝ) < 2))
    (mul_pos hr (by norm_num : (0 : ℝ) < 1 / 2))
    (scaledProfile_flat (d := d) hr (fun t ht ht' => radialBandProfile_flat d (t := t) ht ht'))

theorem radialBandKernel_hasCompactSupport {d : ℕ} (hd : 2 ≤ d) {r : ℝ}
    (hr : 0 < r) : HasCompactSupport (radialBandKernel d r) :=
  radialKernel_hasCompactSupport
    (scaledProfile_contDiff (d := d) (radialBandProfile_contDiff d)).continuous
    (fun _ ht => scaledProfile_eq_zero_of_ge hr (fun _ hs => radialBandProfile_tail d hs) ht)
    ((radialMass_scaledProfile hd hr 2).trans (radialBandProfile_mass hd))

theorem radialBandKernel_tail {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : 2 * r ≤ euclideanNorm x) : radialBandKernel d r x = 0 :=
  radialKernel_eq_zero_of_ge
    (scaledProfile_contDiff (d := d) (radialBandProfile_contDiff d)).continuous
    (fun _ ht => scaledProfile_eq_zero_of_ge hr (fun _ hs => radialBandProfile_tail d hs) ht)
    ((radialMass_scaledProfile hd hr 2).trans (radialBandProfile_mass hd)) (by linarith)

theorem coordLaplacian_radialBandKernel {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r)
    (x : Vec d) :
    coordLaplacian (radialBandKernel d r) x = radialAverage d r x - radialAverage d (2 * r) x := by
  have hs := radialKernel_spec hd (scaledProfile_contDiff (d := d) (radialBandProfile_contDiff d))
    (mul_pos hr (by norm_num : (0 : ℝ) < 2))
    (fun _ ht => scaledProfile_eq_zero_of_ge hr (fun _ ht' => radialBandProfile_tail d ht') ht)
    ((radialMass_scaledProfile hd hr 2).trans (radialBandProfile_mass hd))
    (mul_pos hr (by norm_num : (0 : ℝ) < 1 / 2))
    (scaledProfile_flat (d := d) hr (fun t ht ht' => radialBandProfile_flat d (t := t) ht ht'))
  exact (hs.2.2.2 x).trans (scaledProfile_radialBandProfile d r (euclideanNorm x))

/-- Every coordinate derivative of the actual dyadic kernels has the exact
`r^(2-k)` scaling of `eq.scalar-kernel-bounds` (`paper/main.tex:1015–1018`). -/
theorem radialBandKernel_derivative_bounds {d : ℕ} (hd : 2 ≤ d) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      Integrable (coordinateIterate cs (radialBandKernel d r)) volume ∧
      (∫ x : Vec d, |coordinateIterate cs (radialBandKernel d r) x|) =
        C * (r ^ 2 / r ^ cs.length) :=
  radialKernel_scaled_derivative_bounds hd (radialBandProfile_contDiff d)
    (by norm_num : (0 : ℝ) < 2) (fun _ ht => radialBandProfile_tail d ht)
    (radialBandProfile_mass hd) (by norm_num : (0 : ℝ) < 1 / 2)
    (fun t ht ht' => radialBandProfile_flat d (t := t) ht ht') cs

end EinsteinRelation.Correctors
