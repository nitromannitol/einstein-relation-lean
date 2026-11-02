import EinsteinFull.Work.W6.PhysicalLocalEnergySupport
import EinsteinRelation.Correctors.WeakDivergenceH1Testing

/-! Local spatial H1 localization and distributional cutoff testing.

The coordinate carrier and measure are those of the physical forms. Weak
identities are actual smooth compact test identities, separately on real and
imaginary parts. No stationary realization or time derivative is asserted.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- A local complex L2 function becomes globally L2 after a spatial test multiplier. -/
theorem physicalLocal_memLp_mul_test {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {u : Vec d → ℂ} {φ : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict U)) (hφ : IsSpatialTest U φ) :
    MemLp (fun x => (φ x : ℂ) * u x) 2 volume := by
  apply memLp_re_im_iff.mp
  constructor
  · simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      Correctors.memLp_mul_spatialTest_univ hU hu.re hφ
  · simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using
      Correctors.memLp_mul_spatialTest_univ hU hu.im hφ

/-- Construct the actual whole-space physical H1 classes of a localized local H1
function, including the cutoff derivative and AE representatives. -/
theorem physicalLocalH1_mul_test {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {u : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∃ (v : Lp ℂ 2 (volume : Measure (Vec d)))
      (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v H ∧
      (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) * u x) ∧
      (∀ j, (H j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (φ x : ℂ) * G x j + u x * (coordinateDerivative j φ x : ℂ))) ∧
      (∀ᵐ x ∂volume, x ∉ tsupport φ → v x = 0 ∧ ∀ j, H j x = 0) := by
  have hv := physicalLocal_memLp_mul_test hU hu hφ
  have hH (j : Fin d) : MemLp (fun x => (φ x : ℂ) * G x j +
      u x * (coordinateDerivative j φ x : ℂ)) 2 volume := by
    have hD := physicalLocal_memLp_mul_test hU hu
      (Correctors.isSpatialTest_coordinateDerivative hφ j)
    exact (physicalLocal_memLp_mul_test hU (hG j) hφ).add
      (by simpa only [mul_comm] using hD)
  let v := hv.toLp _
  let H (j : Fin d) := (hH j).toLp _
  refine ⟨v, H, ?_, hv.coeFn_toLp, fun j => (hH j).coeFn_toLp, ?_⟩
  · rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
      v H _ _ hv.coeFn_toLp (fun j => (hH j).coeFn_toLp)]
    constructor
    · intro j
      simpa only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using
        Correctors.hasWeakPartialDerivative_mul_spatialTest (hre j) hφ
    · intro j
      simpa only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add] using
        Correctors.hasWeakPartialDerivative_mul_spatialTest (him j) hφ
  · filter_upwards [hv.coeFn_toLp, ae_all_iff.mpr (fun j => (hH j).coeFn_toLp)]
      with x hx hJ hxφ
    have hz := image_eq_zero_of_notMem_tsupport hxφ
    have hDz (j : Fin d) : coordinateDerivative j φ x = 0 := by
      simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxφ,
        ContinuousLinearMap.zero_apply]
    constructor
    · rw [hx, hz, Complex.ofReal_zero, zero_mul]
    · intro j
      rw [hJ j, hz, hDz j, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]

/-- Construct the cutoff-squared conjugate test from local data, with its actual
whole-space physical H1 domain witness and vanishing outside the cutoff support. -/
theorem physicalLocalH1_cutoff_test {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {u : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) ^ 2 * star (u x)) ∧
      (∀ j, (J j : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (φ x : ℂ) ^ 2 * star (G x j) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x))) ∧
      (∀ᵐ x ∂volume, x ∉ tsupport φ → w x = 0 ∧ ∀ j, J j x = 0) := by
  obtain ⟨v, H, hv, hvr, hHr, _⟩ := physicalLocalH1_mul_test hU hu hG hre him hφ
  obtain ⟨hφb, hDφ⟩ := physicalLocalEnergy_cutoff_bounds φ hφ.1 hφ.2.1
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth φ hφ.1 hφb hDφ
    (star v) (fun j => star (H j)) (physicalH1Graph_star v H hv)
  have hwr' : (w : Vec d → ℂ) =ᵐ[volume]
      (fun x => (φ x : ℂ) ^ 2 * star (u x)) := by
    filter_upwards [hwr, Lp.coeFn_star v, hvr] with x hx hs hvx
    rw [hx, hs, Pi.star_apply, hvx, star_mul, Complex.star_def, Complex.conj_ofReal, pow_two, mul_assoc]
    ring
  have hJr' (j : Fin d) : (J j : Vec d → ℂ) =ᵐ[volume] (fun x =>
      (φ x : ℂ) ^ 2 * star (G x j) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x)) := by
    filter_upwards [hJr j, Lp.coeFn_star v, Lp.coeFn_star (H j), hvr, hHr j]
      with x hx hs hJs hvx hHx
    rw [hx, hs, hJs]
    simp only [Pi.star_apply]
    rw [hvx, hHx]
    simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  refine ⟨w, J, hw, hwr', hJr', ?_⟩
  filter_upwards [hwr', ae_all_iff.mpr hJr'] with x hx hJ hxφ
  have hz := image_eq_zero_of_notMem_tsupport hxφ
  constructor
  · rw [hx, hz, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  · intro j
    rw [hJ j, hz, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_mul, zero_mul, zero_add, zero_mul]

private theorem complex_pairing_of_components {d : ℕ} (m : Measure (Vec d))
    (P Q : Vec d → Fin d → ℂ) (h w : Vec d → ℂ)
    (hP : ∀ j, MemLp (fun x => P x j) 2 m)
    (hQ : ∀ j, MemLp (fun x => Q x j) 2 m)
    (hh : MemLp h 2 m) (hw : MemLp w 2 m)
    (hrr : (∫ x, ∑ j, (P x j).re * (Q x j).re ∂m) = -(∫ x, (h x).re * (w x).re ∂m))
    (hii : (∫ x, ∑ j, (P x j).im * (Q x j).im ∂m) = -(∫ x, (h x).im * (w x).im ∂m))
    (hri : (∫ x, ∑ j, (P x j).re * (Q x j).im ∂m) = -(∫ x, (h x).re * (w x).im ∂m))
    (hir : (∫ x, ∑ j, (P x j).im * (Q x j).re ∂m) = -(∫ x, (h x).im * (w x).re ∂m)) :
    (∫ x, ∑ j, P x j * Q x j ∂m) = -(∫ x, h x * w x ∂m) := by
  have hpq : Integrable (fun x => ∑ j, P x j * Q x j) m :=
    integrable_finset_sum _ fun j _ => (hP j).integrable_mul (hQ j)
  have hhw : Integrable (fun x => h x * w x) m := hh.integrable_mul hw
  have hrrI : Integrable (fun x => ∑ j, (P x j).re * (Q x j).re) m :=
    integrable_finset_sum Finset.univ fun j _ => (hP j).re.integrable_mul (hQ j).re
  have hiiI : Integrable (fun x => ∑ j, (P x j).im * (Q x j).im) m :=
    integrable_finset_sum Finset.univ fun j _ => (hP j).im.integrable_mul (hQ j).im
  have hriI : Integrable (fun x => ∑ j, (P x j).re * (Q x j).im) m :=
    integrable_finset_sum Finset.univ fun j _ => (hP j).re.integrable_mul (hQ j).im
  have hirI : Integrable (fun x => ∑ j, (P x j).im * (Q x j).re) m :=
    integrable_finset_sum Finset.univ fun j _ => (hP j).im.integrable_mul (hQ j).re
  apply Complex.ext
  · change RCLike.re (∫ x, ∑ j, P x j * Q x j ∂m) =
      -RCLike.re (∫ x, h x * w x ∂m)
    rw [← integral_re hpq, ← integral_re hhw]
    simp only [RCLike.re_eq_complex_re, Complex.re_sum, Complex.mul_re,
      Finset.sum_sub_distrib]
    rw [integral_sub hrrI hiiI, integral_sub (f := fun x => (h x).re * (w x).re)
      (g := fun x => (h x).im * (w x).im) (hh.re.integrable_mul hw.re)
      (hh.im.integrable_mul hw.im), hrr, hii]
    ring
  · change RCLike.im (∫ x, ∑ j, P x j * Q x j ∂m) =
      -RCLike.im (∫ x, h x * w x ∂m)
    rw [← integral_im hpq, ← integral_im hhw]
    simp only [RCLike.im_eq_complex_im, Complex.im_sum, Complex.mul_im,
      Finset.sum_add_distrib]
    rw [integral_add hriI hirI, integral_add (f := fun x => (h x).re * (w x).im)
      (g := fun x => (h x).im * (w x).re) (hh.re.integrable_mul hw.im)
      (hh.im.integrable_mul hw.re), hri, hir]
    ring

/-- Density extends an actual local complex distributional divergence identity
from smooth compact tests to the cutoff-squared conjugate H1 test. No global
spatial L2 assumption is imposed on the original fields. -/
theorem physicalWeakDivergence_cutoff_H1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {u h : Vec d → ℂ} {G P : Vec d → Fin d → ℂ}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hP : ∀ j, MemLp (fun x => P x j) 2 (volume.restrict U))
    (hh : MemLp h 2 (volume.restrict U))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    (hdivre : HasWeakDivergence U (fun x j => (P x j).re) (fun x => (h x).re))
    (hdivim : HasWeakDivergence U (fun x j => (P x j).im) (fun x => (h x).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    (∫ x in U, ∑ j, P x j * ((φ x : ℂ) ^ 2 * star (G x j) +
      2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x))) =
      -(∫ x in U, h x * ((φ x : ℂ) ^ 2 * star (u x))) := by
  let Q (x : Vec d) (j : Fin d) := (φ x : ℂ) ^ 2 * star (G x j) +
    2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x)
  let w (x : Vec d) := (φ x : ℂ) ^ 2 * star (u x)
  obtain ⟨v, J, _, hvr, hJr, _⟩ := physicalLocalH1_cutoff_test
    hU.measurableSet hu hG hre him hφ
  have hQ (j : Fin d) : MemLp (fun x => Q x j) 2 (volume.restrict U) :=
    ((Lp.memLp (J j)).ae_eq (hJr j)).restrict U
  have hw : MemLp w 2 (volume.restrict U) :=
    ((Lp.memLp v).ae_eq hvr).restrict U
  have hQr (x : Vec d) (j : Fin d) : (Q x j).re =
      φ x ^ 2 * (G x j).re + 2 * φ x * (u x).re * coordinateDerivative j φ x := by
    simp only [Q, pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hQi (x : Vec d) (j : Fin d) : (Q x j).im =
      -(φ x ^ 2 * (G x j).im + 2 * φ x * (u x).im * coordinateDerivative j φ x) := by
    simp only [Q, pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hwr (x : Vec d) : (w x).re = φ x ^ 2 * (u x).re := by
    simp only [w, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, zero_mul, sub_zero]
  have hwi (x : Vec d) : (w x).im = -(φ x ^ 2 * (u x).im) := by
    simp only [w, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_im, zero_mul, add_zero, mul_neg]
  apply complex_pairing_of_components (volume.restrict U) P Q h w hP hQ hh hw
  · simp_rw [hQr, hwr]
    exact Correctors.weakDivergence_test_cutoff_H1 hU hu.re
      (fun j => (hG j).re) (fun j => (hP j).re) hh.re hre hdivre hφ
  · simp_rw [hQi, hwi, mul_neg, Finset.sum_neg_distrib, integral_neg]
    have he := Correctors.weakDivergence_test_cutoff_H1 hU hu.im
      (fun j => (hG j).im) (fun j => (hP j).im) hh.im him hdivim hφ
    exact congrArg Neg.neg he
  · simp_rw [hQi, hwi, mul_neg, Finset.sum_neg_distrib, integral_neg]
    have he := Correctors.weakDivergence_test_cutoff_H1 hU hu.im
      (fun j => (hG j).im) (fun j => (hP j).re) hh.re him hdivre hφ
    exact congrArg Neg.neg he
  · simp_rw [hQr, hwr]
    exact Correctors.weakDivergence_test_cutoff_H1 hU hu.re
      (fun j => (hG j).re) (fun j => (hP j).im) hh.im hre hdivim hφ

/-- Compact local H1 witnesses suffice to construct the whole-space conjugate
test. The open precompact testing domain is constructed inside the original domain. -/
theorem physicalLocalH1_cutoff_test_of_compacts {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {u : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : ∀ K, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K))
    (hG : ∀ K, IsCompact K → K ⊆ U →
      ∀ j, MemLp (fun x => G x j) 2 (volume.restrict K))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) ^ 2 * star (u x)) ∧
      (∀ j, (J j : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (φ x : ℂ) ^ 2 * star (G x j) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x))) ∧
      (∀ᵐ x ∂volume, x ∉ tsupport φ → w x = 0 ∧ ∀ j, J j x = 0) := by
  obtain ⟨V, hV, hφV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  have hsub : V ⊆ U := subset_closure.trans hVU
  exact physicalLocalH1_cutoff_test hV.measurableSet
    ((hu _ hcV hVU).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (fun j => (hG _ hcV hVU j).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (Correctors.hasWeakGradient_mono hsub hre)
    (Correctors.hasWeakGradient_mono hsub him) ⟨hφ.1, hφ.2.1, hφV⟩

/-- The complex cutoff identity for genuinely local H1 and L2 fields. All
integrals are whole-space Lebesgue integrals of compactly localized expressions;
no original field is required to be globally L2, even on the original domain. -/
theorem physicalWeakDivergence_cutoff_locallyH1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {u h : Vec d → ℂ} {G P : Vec d → Fin d → ℂ}
    (hu : ∀ K, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K))
    (hG : ∀ K, IsCompact K → K ⊆ U →
      ∀ j, MemLp (fun x => G x j) 2 (volume.restrict K))
    (hP : ∀ K, IsCompact K → K ⊆ U →
      ∀ j, MemLp (fun x => P x j) 2 (volume.restrict K))
    (hh : ∀ K, IsCompact K → K ⊆ U → MemLp h 2 (volume.restrict K))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    (hdivre : HasWeakDivergence U (fun x j => (P x j).re) (fun x => (h x).re))
    (hdivim : HasWeakDivergence U (fun x j => (P x j).im) (fun x => (h x).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    (∫ x, ∑ j, P x j * ((φ x : ℂ) ^ 2 * star (G x j) +
      2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x))) =
      -(∫ x, h x * ((φ x : ℂ) ^ 2 * star (u x))) := by
  obtain ⟨V, hV, hφV, hVU, hcV⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  have hsub : V ⊆ U := subset_closure.trans hVU
  have he := physicalWeakDivergence_cutoff_H1 hV
    ((hu _ hcV hVU).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (fun j => (hG _ hcV hVU j).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (fun j => (hP _ hcV hVU j).mono_measure (Measure.restrict_mono_set _ subset_closure))
    ((hh _ hcV hVU).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (Correctors.hasWeakGradient_mono hsub hre)
    (Correctors.hasWeakGradient_mono hsub him)
    (Correctors.hasWeakDivergence_mono hsub hdivre)
    (Correctors.hasWeakDivergence_mono hsub hdivim) ⟨hφ.1, hφ.2.1, hφV⟩
  have hz {x : Vec d} (hx : x ∉ V) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφV h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp only [hz hx, Complex.ofReal_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_add,
      Finset.sum_const_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hz hx, Complex.ofReal_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero])] at he
  exact he

private theorem local_cutoff_sq_integrable {d : ℕ} (m : Measure (Vec d))
    (φ : Vec d → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) ∞ m)
    {u : Vec d → ℂ} (hu : MemLp u 2 m) :
    Integrable (fun x => φ x ^ 2 * ‖u x‖ ^ 2) m := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
    (hφ.fun_mul hu).norm.integrable_sq

/-- The Euclidean energy and force/cutoff remainder are integrable for local L2
data on the testing domain. No H1 or equation is required for this fact. -/
theorem physicalLocalTesting_energy_integrable {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (ζ : ℂ) {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    Integrable (fun x => φ x ^ 2 * (∑ j, ‖G x j‖ ^ 2)) (volume.restrict U) ∧
      Integrable (fun x => (‖ζ‖ ^ 2 * φ x ^ 2 +
        (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) (volume.restrict U) := by
  obtain ⟨hφb, hDφ⟩ := physicalLocalEnergy_cutoff_bounds φ hφ.1 hφ.2.1
  constructor
  · simpa only [Finset.mul_sum] using
      (integrable_finset_sum Finset.univ fun j _ =>
        local_cutoff_sq_integrable _ φ (hφb.restrict U) (hG j))
  · have h1 := (local_cutoff_sq_integrable _ φ (hφb.restrict U) hu).const_mul (‖ζ‖ ^ 2)
    have h2 := integrable_finset_sum Finset.univ fun j _ =>
      local_cutoff_sq_integrable _ (coordinateDerivative j φ) ((hDφ j).restrict U) hu
    convert h1.add h2 using 1
    funext x
    change (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) * ‖u x‖ ^ 2 =
      ‖ζ‖ ^ 2 * (φ x ^ 2 * ‖u x‖ ^ 2) + ∑ j, (coordinateDerivative j φ x) ^ 2 * ‖u x‖ ^ 2
    rw [add_mul, Finset.sum_mul]
    ring

/-- The literal anisotropic forward distributional equation yields its cutoff
energy identity by density. `V` is a supplied local L2 term, not a constructed
time derivative. Arbitrary complex force retains its sign in the equation. -/
theorem physicalLocalTesting_forced_identity {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ (volume.restrict U))
    (i : Fin d) (ζ : ℂ) {u V F : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hV : MemLp V 2 (volume.restrict U)) (hF : MemLp F 2 (volume.restrict U))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    (hdivre : HasWeakDivergence U
      (fun x j => ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k).re)
      (fun x => (V x - F x - ζ * ∑ j, (a x j i : ℂ) * G x j).re))
    (hdivim : HasWeakDivergence U
      (fun x j => ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k).im)
      (fun x => (V x - F x - ζ * ∑ j, (a x j i : ℂ) * G x j).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    let I := fun x => (1 / 2 : ℂ) * (∑ j : Fin d, ∑ k : Fin d,
      ((φ x : ℂ) ^ 2 * star (G x j) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x)) *
          (a x j k : ℂ) * G x k) -
      ζ * (φ x : ℂ) ^ 2 * star (u x) * (∑ j, (a x j i : ℂ) * G x j)
    Integrable I (volume.restrict U) ∧
      (∫ x in U, I x) = ∫ x in U, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x) := by
  intro I
  let P (x : Vec d) (j : Fin d) := (1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k
  let D (x : Vec d) := ∑ j, (a x j i : ℂ) * G x j
  let Q (x : Vec d) (j : Fin d) := (φ x : ℂ) ^ 2 * star (G x j) +
    2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x)
  let w (x : Vec d) := (φ x : ℂ) ^ 2 * star (u x)
  have hP (j : Fin d) : MemLp (fun x => P x j) 2 (volume.restrict U) :=
    (memLp_finset_sum Finset.univ (fun k _ => (ha j k).fun_mul (hG k))).const_mul _
  have hD : MemLp D 2 (volume.restrict U) :=
    memLp_finset_sum Finset.univ (fun j _ => (ha j i).fun_mul (hG j))
  obtain ⟨v, J, _, hvr, hJr, _⟩ := physicalLocalH1_cutoff_test
    hU.measurableSet hu hG hre him hφ
  have hQ (j : Fin d) : MemLp (fun x => Q x j) 2 (volume.restrict U) :=
    ((Lp.memLp (J j)).ae_eq (hJr j)).restrict U
  have hw : MemLp w 2 (volume.restrict U) :=
    ((Lp.memLp v).ae_eq hvr).restrict U
  have hPQ : Integrable (fun x => ∑ j, P x j * Q x j) (volume.restrict U) :=
    integrable_finset_sum Finset.univ fun j _ => (hP j).integrable_mul (hQ j)
  have hDw : Integrable (fun x => ζ * (D x * w x)) (volume.restrict U) :=
    (hD.integrable_mul hw).const_mul ζ
  have hFV : Integrable (fun x => (V x - F x) * w x) (volume.restrict U) :=
    (hV.sub hF).integrable_mul hw
  have hrep (x : Vec d) : I x = (∑ j, P x j * Q x j) - ζ * (D x * w x) := by
    dsimp only [I, P, Q, D, w]
    simp only [Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have hI : Integrable I (volume.restrict U) := by
    rw [show I = (fun x => (∑ j, P x j * Q x j) - ζ * (D x * w x)) from funext hrep]
    exact hPQ.sub hDw
  have he := physicalWeakDivergence_cutoff_H1 hU hu hG hP
    ((hV.sub hF).sub (hD.const_mul ζ)) hre him hdivre hdivim hφ
  change (∫ x in U, ∑ j, P x j * Q x j) =
    -(∫ x in U, (V x - F x - ζ * D x) * w x) at he
  have he' : (∫ x in U, ∑ j, P x j * Q x j) =
      -(∫ x in U, (V x - F x) * w x) + ∫ x in U, ζ * (D x * w x) := by
    have hsplit (x : Vec d) : (V x - F x - ζ * D x) * w x =
        (V x - F x) * w x - ζ * (D x * w x) := by ring
    simp_rw [hsplit] at he
    rw [integral_sub hFV hDw, neg_sub] at he
    simpa only [sub_eq_add_neg, add_comm] using he
  refine ⟨hI, ?_⟩
  simp_rw [hrep]
  rw [integral_sub hPQ hDw, he', add_sub_cancel_right, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by dsimp only [w]; ring

/-- The spatial energy theorem consumes a genuine smooth-test distributional equation
by the proved density bridge, using local physical fields throughout. -/
theorem physicalLocalEnergy_distributional {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ (volume.restrict U))
    (κ B : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Vec d,
      κ * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ))
    (hA : ∀ᵐ x ∂(volume.restrict U), ∀ j k, |a x j k| ≤ B)
    (i : Fin d) (ζ : ℂ) {u V F : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hV : MemLp V 2 (volume.restrict U)) (hF : MemLp F 2 (volume.restrict U))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    (hdivre : HasWeakDivergence U
      (fun x j => ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k).re)
      (fun x => (V x - F x - ζ * ∑ j, (a x j i : ℂ) * G x j).re))
    (hdivim : HasWeakDivergence U
      (fun x j => ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k).im)
      (fun x => (V x - F x - ζ * ∑ j, (a x j i : ℂ) * G x j).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    (κ / 4) * (∫ x in U, φ x ^ 2 * (∑ j, ‖G x j‖ ^ 2)) ≤
      (∫ x in U, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        (∫ x in U, (‖ζ‖ ^ 2 * φ x ^ 2 +
          (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) := by
  obtain ⟨hI, hId⟩ := physicalLocalTesting_forced_identity
    hU a ha i ζ hu hG hV hF hre him hdivre hdivim hφ
  obtain ⟨hE, hM⟩ := physicalLocalTesting_energy_integrable hu hG ζ hφ
  have hIre := hI.re
  simp only [RCLike.re_eq_complex_re] at hIre
  have hIr := integral_re hI
  simp only [RCLike.re_eq_complex_re] at hIr
  rw [← hId, ← hIr, ← integral_const_mul, ← integral_const_mul,
    ← integral_add hIre (hM.const_mul _)]
  apply integral_mono_ae (hE.const_mul _) (hIre.add (hM.const_mul _))
  filter_upwards [hlower, hA] with x hlx hAx
  simpa only [mul_assoc] using! physicalLocalEnergy_pointwise
    (a x) i κ B hκ hlx hAx (φ x) (fun j => coordinateDerivative j φ x)
      ζ (u x) (G x)

/-- The local spatial energy estimate for fields that are L2 only on compact
subsets of the open domain. The testing domain and H1 test are constructed. -/
theorem physicalLocalEnergy_locallyH1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ (volume.restrict U))
    (κ B : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Vec d,
      κ * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ))
    (hA : ∀ᵐ x ∂(volume.restrict U), ∀ j k, |a x j k| ≤ B)
    (i : Fin d) (ζ : ℂ) {u V F : Vec d → ℂ} {G : Vec d → Fin d → ℂ}
    (hu : ∀ K, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K))
    (hG : ∀ K, IsCompact K → K ⊆ U →
      ∀ j, MemLp (fun x => G x j) 2 (volume.restrict K))
    (hV : ∀ K, IsCompact K → K ⊆ U → MemLp V 2 (volume.restrict K))
    (hF : ∀ K, IsCompact K → K ⊆ U → MemLp F 2 (volume.restrict K))
    (hre : HasWeakGradient U (fun x => (u x).re) (fun x j => (G x j).re))
    (him : HasWeakGradient U (fun x => (u x).im) (fun x j => (G x j).im))
    (hdivre : HasWeakDivergence U
      (fun x j => ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k).re)
      (fun x => (V x - F x - ζ * ∑ j, (a x j i : ℂ) * G x j).re))
    (hdivim : HasWeakDivergence U
      (fun x j => ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G x k).im)
      (fun x => (V x - F x - ζ * ∑ j, (a x j i : ℂ) * G x j).im))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) :
    (κ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G x j‖ ^ 2)) ≤
      (∫ x, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
          (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) := by
  obtain ⟨W, hW, hφW, hWU, hcW⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  have hsub : W ⊆ U := subset_closure.trans hWU
  have hlowerW := hlower.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))
  have hAW := hA.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))
  have he := physicalLocalEnergy_distributional hW a
    (fun j k => (ha j k).mono_measure (Measure.restrict_mono_set _ hsub))
    κ B hκ hlowerW hAW i ζ
    ((hu _ hcW hWU).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (fun j => (hG _ hcW hWU j).mono_measure (Measure.restrict_mono_set _ subset_closure))
    ((hV _ hcW hWU).mono_measure (Measure.restrict_mono_set _ subset_closure))
    ((hF _ hcW hWU).mono_measure (Measure.restrict_mono_set _ subset_closure))
    (Correctors.hasWeakGradient_mono hsub hre)
    (Correctors.hasWeakGradient_mono hsub him)
    (Correctors.hasWeakDivergence_mono hsub hdivre)
    (Correctors.hasWeakDivergence_mono hsub hdivim) ⟨hφ.1, hφ.2.1, hφW⟩
  have hz {x : Vec d} (hx : x ∉ W) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφW h))
  have hDz {x : Vec d} (hx : x ∉ W) (j : Fin d) : coordinateDerivative j φ x = 0 := by
    have hxφ : x ∉ tsupport φ := fun h => hx (hφW h)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxφ,
      ContinuousLinearMap.zero_apply]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [hz hx, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hz hx, Complex.ofReal_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp only [hz hx, hDz hx, zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero, Finset.sum_const_zero, add_zero, zero_mul])] at he
  exact he

end EinsteinFull
