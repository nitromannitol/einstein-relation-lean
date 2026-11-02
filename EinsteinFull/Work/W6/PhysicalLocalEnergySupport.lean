import EinsteinFull.Calculus.PhysicalH1WeightedIntegrationSupport
import EinsteinFull.Calculus.PhysicalGaugeCoercivitySupport
import EinsteinFull.Calculus.PhysicalCoefficientSupport

/-! Physical cutoff testing on the actual completed complex H1 domain.

All integrals are spatial Lebesgue integrals. The first-order force is kept
separate from the unforced physical bilinear form, as in the forward equation
`u_t = (1/2) div (a Du) + ζ (a e_i) · Du`. No time regularity or local
time-slice estimate is asserted here.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Conjugation preserves the physical H1 graph, including both weak components. -/
theorem physicalH1Graph_star {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    IsPhysicalH1Graph volume (Or.inl rfl) (star u) (fun j => star (G j)) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (star u) (fun j => star (G j)) _ _ (Lp.coeFn_star u) (fun j => Lp.coeFn_star (G j))]
  constructor
  · simpa only [Pi.star_apply, Complex.star_def, Complex.conj_re] using hu.1
  · intro j
    have h := hu.2 j
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Pi.star_apply, Pi.neg_apply, Complex.star_def, Complex.conj_im] using! h.1.neg
    · simpa only [Pi.star_apply, Pi.neg_apply, Complex.star_def, Complex.conj_im] using! h.2.1.neg
    · intro ψ hψ
      simpa only [Pi.star_apply, Complex.star_def, Complex.conj_im, neg_mul, integral_neg, neg_neg]
        using congrArg Neg.neg (h.2.2 ψ hψ)

/-- The actual cutoff-squared conjugate is an admissible test in the full H1 domain. -/
theorem physicalH1Graph_cutoff_test {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume)
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) ^ 2 * star (u x)) ∧
      ∀ j, (J j : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (φ x : ℂ) ^ 2 * star (G j x) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x)) := by
  have hder (j : Fin d) (x : Vec d) :
      coordinateDerivative j (fun y => φ y * φ y) x =
        2 * φ x * coordinateDerivative j φ x := by
    rw [coordinateDerivative_mul j φ φ x
      (hφ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    ring
  have hsq : MemLp (fun x => ((φ x * φ x : ℝ) : ℂ)) ∞ volume := by
    simpa only [Complex.ofReal_mul] using! hφb.mul (r := ∞) hφb
  have hDsq (j : Fin d) : MemLp
      (fun x => (coordinateDerivative j (fun y => φ y * φ y) x : ℂ)) ∞ volume := by
    simp_rw [hder, Complex.ofReal_mul, Complex.ofReal_ofNat]
    exact (hφb.const_mul 2).fun_mul (r := ∞) (hDφ j)
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth
    (fun x => φ x * φ x) (hφ.mul hφ) hsq hDsq (star u)
    (fun j => star (G j)) (physicalH1Graph_star u G hu)
  refine ⟨w, J, hw, ?_, ?_⟩
  · filter_upwards [hwr, Lp.coeFn_star u] with x hx hs
    rw [hx, hs, Complex.ofReal_mul, pow_two]
    rfl
  · intro j
    filter_upwards [hJr j, Lp.coeFn_star u, Lp.coeFn_star (G j)] with x hx hs hgs
    rw [hx, hs, hgs, hder]
    simp only [Pi.star_apply, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring

private theorem cutoff_young (t b x y : ℝ) (ht : 0 < t) :
    b * y * x ≤ x ^ 2 / (4 * t) + t * b ^ 2 * y ^ 2 := by
  have h : 0 ≤ (x - 2 * t * b * y) ^ 2 / (4 * t) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have he : (x - 2 * t * b * y) ^ 2 / (4 * t) =
      x ^ 2 / (4 * t) + t * b ^ 2 * y ^ 2 - b * y * x := by
    field_simp
    ring
  rw [he] at h
  linarith only [h]

/-- Entrywise Young absorption of a genuine anisotropic complex matrix pairing.
The norms of the coordinate vectors are explicit Euclidean sums of squares. -/
theorem physicalMatrixPairing_young {d : ℕ} (A : Mat d) (B t : ℝ)
    (ht : 0 < t) (hA : ∀ j k, |A j k| ≤ B) (P Q : Fin d → ℂ) :
    ‖∑ j : Fin d, ∑ k : Fin d, P j * (A j k : ℂ) * Q k‖ ≤
      ((d : ℝ) / (4 * t)) * (∑ k, ‖Q k‖ ^ 2) +
        ((d : ℝ) * t * B ^ 2) * (∑ j, ‖P j‖ ^ 2) := by
  have hp (j k : Fin d) : ‖P j * (A j k : ℂ) * Q k‖ ≤
      ‖Q k‖ ^ 2 / (4 * t) + t * B ^ 2 * ‖P j‖ ^ 2 := by
    calc
      _ = ‖P j‖ * ‖(A j k : ℂ)‖ * ‖Q k‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖P j‖ * B * ‖Q k‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hA j k) (norm_nonneg _)
      _ = B * ‖P j‖ * ‖Q k‖ := by ring
      _ ≤ _ := cutoff_young t B ‖Q k‖ ‖P j‖ ht
  calc
    _ ≤ ∑ j : Fin d, ∑ k : Fin d, ‖P j * (A j k : ℂ) * Q k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin d, ∑ k : Fin d,
        (‖Q k‖ ^ 2 / (4 * t) + t * B ^ 2 * ‖P j‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hp j k
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      ring

/-- Young absorption of the actual force column, with arbitrary complex force. -/
theorem physicalForceColumn_young {d : ℕ} (A : Mat d) (i : Fin d) (B t : ℝ)
    (ht : 0 < t) (hA : ∀ j, |A j i| ≤ B) (z : ℂ) (Q : Fin d → ℂ) :
    ‖z * (∑ j, (A j i : ℂ) * Q j)‖ ≤
      (1 / (4 * t)) * (∑ j, ‖Q j‖ ^ 2) +
        ((d : ℝ) * t * B ^ 2) * ‖z‖ ^ 2 := by
  have hp (j : Fin d) : ‖z * ((A j i : ℂ) * Q j)‖ ≤
      ‖Q j‖ ^ 2 / (4 * t) + t * B ^ 2 * ‖z‖ ^ 2 := by
    calc
      _ = ‖z‖ * ‖(A j i : ℂ)‖ * ‖Q j‖ := by simp only [norm_mul]; ring
      _ ≤ ‖z‖ * B * ‖Q j‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hA j) (norm_nonneg _)
      _ = B * ‖z‖ * ‖Q j‖ := by ring
      _ ≤ _ := cutoff_young t B ‖Q j‖ ‖z‖ ht
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ j, ‖z * ((A j i : ℂ) * Q j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖Q j‖ ^ 2 / (4 * t) + t * B ^ 2 * ‖z‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hp j
    _ = _ := by
      simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Exact cutoff expansion of the physical principal form and forward drift.
The same complex force appears in the drift; no conjugate force is introduced. -/
theorem physicalLocalEnergy_integrand {d : ℕ} (A : Mat d) (i : Fin d)
    (φ : ℝ) (Dφ : Vec d) (ζ u : ℂ) (G : Fin d → ℂ) :
    (1 / 2 : ℂ) * (∑ j : Fin d, ∑ k : Fin d,
      ((φ : ℂ) ^ 2 * star (G j) + 2 * (φ : ℂ) * (Dφ j : ℂ) * star u) *
        (A j k : ℂ) * G k) -
      ζ * (φ : ℂ) ^ 2 * star u * (∑ j, (A j i : ℂ) * G j) =
    (1 / 2 : ℂ) * (∑ j : Fin d, ∑ k : Fin d,
      star ((φ : ℂ) * G j) * (A j k : ℂ) * ((φ : ℂ) * G k)) +
      (∑ j : Fin d, ∑ k : Fin d,
        ((Dφ j : ℂ) * star u) * (A j k : ℂ) * ((φ : ℂ) * G k)) -
      (ζ * (φ : ℂ) * star u) * (∑ j, (A j i : ℂ) * ((φ : ℂ) * G j)) := by
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- Physical cutoff and complex-force cross terms cost only quadratic force
and cutoff-gradient mass. The constant depends just on dimension and ellipticity. -/
theorem physicalLocalEnergy_pointwise {d : ℕ} (A : Mat d) (i : Fin d)
    (κ B : ℝ) (hκ : 0 < κ)
    (hlower : ∀ ξ : Vec d, κ * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (hA : ∀ j k, |A j k| ≤ B)
    (φ : ℝ) (Dφ : Vec d) (ζ u : ℂ) (G : Fin d → ℂ) :
    (κ / 4) * φ ^ 2 * (∑ j, ‖G j‖ ^ 2) ≤
      ((1 / 2 : ℂ) * (∑ j : Fin d, ∑ k : Fin d,
        ((φ : ℂ) ^ 2 * star (G j) + 2 * (φ : ℂ) * (Dφ j : ℂ) * star u) *
          (A j k : ℂ) * G k) -
        ζ * (φ : ℂ) ^ 2 * star u * (∑ j, (A j i : ℂ) * G j)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        (‖ζ‖ ^ 2 * φ ^ 2 + (∑ j, (Dφ j) ^ 2)) * ‖u‖ ^ 2 := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  let Q (j : Fin d) := (φ : ℂ) * G j
  let P (j : Fin d) := (Dφ j : ℂ) * star u
  let E : ℂ := ∑ j : Fin d, ∑ k : Fin d, star (Q j) * (A j k : ℂ) * Q k
  let R : ℂ := ∑ j : Fin d, ∑ k : Fin d, P j * (A j k : ℂ) * Q k
  let F : ℂ := (ζ * (φ : ℂ) * star u) * (∑ j, (A j i : ℂ) * Q j)
  have hQ : (∑ j, ‖Q j‖ ^ 2) = φ ^ 2 * (∑ j, ‖G j‖ ^ 2) := by
    simp only [Q, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, Finset.mul_sum]
  have hP : (∑ j, ‖P j‖ ^ 2) = (∑ j, (Dφ j) ^ 2) * ‖u‖ ^ 2 := by
    simp only [P, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, Finset.sum_mul]
  have hz : ‖ζ * (φ : ℂ) * star u‖ ^ 2 = ‖ζ‖ ^ 2 * φ ^ 2 * ‖u‖ ^ 2 := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have he : κ * (φ ^ 2 * (∑ j, ‖G j‖ ^ 2)) ≤ E.re := by
    simpa only [hQ] using complex_quadratic_lowerBound A κ hlower Q
  have hr := physicalMatrixPairing_young A B (2 * (d : ℝ) / κ)
    (by positivity) hA P Q
  have hf := physicalForceColumn_young A i B (2 / κ)
    (by positivity) (fun j => hA j i) (ζ * (φ : ℂ) * star u) Q
  have hc1 : (d : ℝ) / (4 * (2 * (d : ℝ) / κ)) = κ / 8 := by
    field_simp
    ring
  have hc2 : 1 / (4 * (2 / κ)) = κ / 8 := by field_simp; ring
  rw [hQ, hP, hc1] at hr
  rw [hQ, hz, hc2] at hf
  have hcr : (d : ℝ) * (2 * (d : ℝ) / κ) * B ^ 2 ≤
      2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ := by
    apply (le_div_iff₀ hκ).mpr
    field_simp
    nlinarith only [mul_nonneg hd.le (sq_nonneg B)]
  have hcf : (d : ℝ) * (2 / κ) * B ^ 2 ≤
      2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ := by
    apply (le_div_iff₀ hκ).mpr
    field_simp
    nlinarith only [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg B)]
  have hr' : ‖R‖ ≤ (κ / 8) * (φ ^ 2 * (∑ j, ‖G j‖ ^ 2)) +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        ((∑ j, (Dφ j) ^ 2) * ‖u‖ ^ 2) :=
    hr.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcr (show 0 ≤ (∑ j, (Dφ j) ^ 2) * ‖u‖ ^ 2 by positivity)))
  have hf' : ‖F‖ ≤ (κ / 8) * (φ ^ 2 * (∑ j, ‖G j‖ ^ 2)) +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        (‖ζ‖ ^ 2 * φ ^ 2 * ‖u‖ ^ 2) :=
    hf.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcf (show 0 ≤ ‖ζ‖ ^ 2 * φ ^ 2 * ‖u‖ ^ 2 by positivity)))
  rw [physicalLocalEnergy_integrand]
  change (κ / 4) * φ ^ 2 * (∑ j, ‖G j‖ ^ 2) ≤
    ((1 / 2 : ℂ) * E + R - F).re + _
  have hR : -‖R‖ ≤ R.re := (abs_le.mp (Complex.abs_re_le_norm R)).1
  have hF : F.re ≤ ‖F‖ := Complex.re_le_norm F
  have hre : ((1 / 2 : ℂ) * E + R - F).re = (1 / 2 : ℝ) * E.re + R.re - F.re := by
    simp [Complex.mul_re]
  rw [hre]
  nlinarith only [he, hr', hf', hR, hF]

private theorem integrable_cutoff_sq {d : ℕ} (φ : Vec d → ℝ)
    (hφ : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    Integrable (fun x => φ x ^ 2 * ‖u x‖ ^ 2) volume := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs] using
    (hφ.fun_mul (Lp.memLp u)).norm.integrable_sq

/-- Both Euclidean gradient energy and the quadratic cutoff/force mass are integrable. -/
theorem physicalLocalEnergy_integrable {d : ℕ} (φ : Vec d → ℝ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume)
    (ζ : ℂ) (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Integrable (fun x => φ x ^ 2 * (∑ j, ‖G j x‖ ^ 2)) volume ∧
      Integrable (fun x => (‖ζ‖ ^ 2 * φ x ^ 2 +
        (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) volume := by
  constructor
  · simpa only [Finset.mul_sum] using
      (integrable_finset_sum Finset.univ fun j _ => integrable_cutoff_sq φ hφb (G j))
  · have h1 := (integrable_cutoff_sq φ hφb u).const_mul (‖ζ‖ ^ 2)
    have h2 := integrable_finset_sum Finset.univ fun j _ =>
      integrable_cutoff_sq (coordinateDerivative j φ) (hDφ j) u
    convert h1.add h2 using 1
    funext x
    change (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) * ‖u x‖ ^ 2 =
      ‖ζ‖ ^ 2 * (φ x ^ 2 * ‖u x‖ ^ 2) + ∑ j, (coordinateDerivative j φ x) ^ 2 * ‖u x‖ ^ 2
    rw [add_mul, Finset.sum_mul]
    ring

/-- Testing the literal physical form with a cutoff-squared conjugate gives
the actual complex divergence-form energy integral. All equalities of L2
representatives are used almost everywhere. -/
theorem physicalLocalEnergy_form_identity {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (φ : Vec d → ℝ)
    (u w : Lp ℂ 2 (volume : Measure (Vec d)))
    (G J : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hwr : (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) ^ 2 * star (u x)))
    (hJr : ∀ j, (J j : Vec d → ℂ) =ᵐ[volume] (fun x =>
      (φ x : ℂ) ^ 2 * star (G j x) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x))) :
    let I := fun x => (1 / 2 : ℂ) * (∑ j : Fin d, ∑ k : Fin d,
      ((φ x : ℂ) ^ 2 * star (G j x) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x)) *
          (a x j k : ℂ) * G k x) -
      ζ * (φ x : ℂ) ^ 2 * star (u x) * (∑ j, (a x j i : ℂ) * G j x)
    Integrable I volume ∧
      physicalBilinearForm volume a ha i 0 0 w J u G -
        ζ * (∫ x, w x * (∑ j, (a x j i : ℂ) * G j x)) = ∫ x, I x := by
  intro I
  let T := fun x => ∑ j : Fin d, ∑ k : Fin d, J j x * (a x j k : ℂ) * G k x
  let D := fun x => w x * (∑ j, (a x j i : ℂ) * G j x)
  have hT : Integrable T volume := by
    simpa only [zero_mul, sub_zero] using
      (physicalBilinearForm_integrable volume a ha i 0 w u J G).2
  have hD : Integrable D volume := by
    have h := integrable_finset_sum Finset.univ fun j _ =>
      ((Lp.memLp w).mul' (r := 2) (ha j i)).integrable_mul (Lp.memLp (G j))
    convert h using 1
    funext x
    simp only [D, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [Pi.mul_apply]
    ring
  have hrep : (fun x => (1 / 2 : ℂ) * T x - ζ * D x) =ᵐ[volume] I := by
    filter_upwards [hwr, ae_all_iff.mpr hJr] with x hwx hJx
    dsimp only [T, D, I]
    simp_rw [hJx]
    rw [hwx]
    ring
  have hI := (hT.const_mul (1 / 2 : ℂ)).sub (hD.const_mul ζ)
  refine ⟨hI.congr hrep, ?_⟩
  have hB : physicalBilinearForm volume a ha i 0 0 w J u G =
      (1 / 2 : ℂ) * (∫ x, T x) := by
    simp only [physicalBilinearForm, Complex.ofReal_zero, zero_mul, zero_add, sub_zero, T]
  rw [hB]
  change (1 / 2 : ℂ) * (∫ x, T x) - ζ * (∫ x, D x) = _
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hT.const_mul (1 / 2 : ℂ)) (hD.const_mul ζ)]
  exact integral_congr_ae hrep

/-- The physical cutoff energy inequality on the literal bilinear form.
Ellipticity and entry bounds may hold on one common full-measure set. -/
theorem physicalLocalEnergy_form_lowerBound {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (κ B : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᵐ x ∂volume, ∀ ξ : Vec d,
      κ * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ))
    (hA : ∀ᵐ x ∂volume, ∀ j k, |a x j k| ≤ B)
    (ζ : ℂ) (φ : Vec d → ℝ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume)
    (u w : Lp ℂ 2 (volume : Measure (Vec d)))
    (G J : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hwr : (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) ^ 2 * star (u x)))
    (hJr : ∀ j, (J j : Vec d → ℂ) =ᵐ[volume] (fun x =>
      (φ x : ℂ) ^ 2 * star (G j x) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (u x))) :
    (κ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j x‖ ^ 2)) ≤
      (physicalBilinearForm volume a ha i 0 0 w J u G -
        ζ * (∫ x, w x * (∑ j, (a x j i : ℂ) * G j x))).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
          (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) := by
  obtain ⟨hI, hId⟩ := physicalLocalEnergy_form_identity a ha i ζ φ u w G J hwr hJr
  obtain ⟨hE, hM⟩ := physicalLocalEnergy_integrable φ hφb hDφ ζ u G
  have hIre := hI.re
  simp only [RCLike.re_eq_complex_re] at hIre
  have hIr := integral_re hI
  simp only [RCLike.re_eq_complex_re] at hIr
  rw [hId, ← hIr, ← integral_const_mul, ← integral_const_mul,
    ← integral_add hIre (hM.const_mul _)]
  apply integral_mono_ae (hE.const_mul _) (hIre.add (hM.const_mul _))
  filter_upwards [hlower, hA] with x hlx hAx
  simpa only [mul_assoc] using! physicalLocalEnergy_pointwise
    (a x) i κ B hκ hlx hAx (φ x) (fun j => coordinateDerivative j φ x)
      ζ (u x) (fun j => G j x)

/-- A local physical weak equation can be tested by the constructed cutoff.
`V` is the given physical time-derivative term and `F` the source. This is a
spatial estimate at one time; it does not construct a time derivative. -/
theorem physicalLocalEnergy_weakEquation {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (κ B : ℝ) (hκ : 0 < κ)
    (hlower : ∀ᵐ x ∂volume, ∀ ξ : Vec d,
      κ * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ))
    (hA : ∀ᵐ x ∂volume, ∀ j k, |a x j k| ≤ B)
    (ζ : ℂ) (U : Set (Vec d)) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume)
    (hφU : Function.support φ ⊆ U)
    (u V F : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hweak : ∀ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J →
      (∀ᵐ x ∂volume, x ∉ U → w x = 0) →
      (∫ x, w x * V x) + physicalBilinearForm volume a ha i 0 0 w J u G -
        ζ * (∫ x, w x * (∑ j, (a x j i : ℂ) * G j x)) = ∫ x, w x * F x) :
    (κ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j x‖ ^ 2)) ≤
      (∫ x, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * B ^ 2 / κ) *
        (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
          (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) := by
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_cutoff_test φ hφ hφb hDφ u G hu
  have hwU : ∀ᵐ x ∂volume, x ∉ U → w x = 0 := by
    filter_upwards [hwr] with x hx hxU
    have hz : φ x = 0 := by
      by_contra hn
      exact hxU (hφU hn)
    simp only [hx, hz, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  have heq := hweak w J hw hwU
  have hFV : (∫ x, w x * (F x - V x)) =
      (∫ x, w x * F x) - (∫ x, w x * V x) := by
    simp_rw [mul_sub]
    exact integral_sub ((Lp.memLp w).integrable_mul (Lp.memLp F))
      ((Lp.memLp w).integrable_mul (Lp.memLp V))
  have hpair : (∫ x, w x * (F x - V x)) =
      ∫ x, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x) := by
    apply integral_congr_ae
    filter_upwards [hwr] with x hx
    rw [hx]
  have hform : physicalBilinearForm volume a ha i 0 0 w J u G -
      ζ * (∫ x, w x * (∑ j, (a x j i : ℂ) * G j x)) =
      ∫ x, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x) := by
    rw [← hpair, hFV]
    linear_combination heq
  have hbound := physicalLocalEnergy_form_lowerBound a ha i κ B hκ hlower hA
    ζ φ hφb hDφ u w G J hwr hJr
  rw [hform] at hbound
  exact hbound

/-- Smooth compact cutoffs supply their own bounded multiplier and derivative witnesses. -/
theorem physicalLocalEnergy_cutoff_bounds {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) ∞ volume ∧
      ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume := by
  refine ⟨(hφ.continuous.memLp_top_of_hasCompactSupport hc volume).ofReal, ?_⟩
  intro j
  have hD : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).continuous
  exact (hD.memLp_top_of_hasCompactSupport (hc.fderiv_apply ℝ (unitVector j)) volume).ofReal

/-- Direct consumer on the uniformly elliptic physical coefficient field and
the frozen physical forms. Smooth compact cutoffs supply all multiplication
witnesses; the cutoff support supplies the local test-domain witness. -/
theorem physicalLocalEnergy_compactCutoff {d : ℕ}
    (a : Vec d → Mat d) (Λ : ℝ) (hΛ : 0 < Λ) (hEll : IsElliptic Λ a)
    (hc : ∀ j k, Continuous (fun x => a x j k)) (i : Fin d) (ζ : ℂ)
    (U : Set (Vec d)) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : Function.support φ ⊆ U)
    (u V F : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hweak : ∀ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J →
      (∀ᵐ x ∂volume, x ∉ U → w x = 0) →
      (∫ x, w x * V x) + physicalBilinearForm volume a
        (memLp_complex_elliptic_entry volume a Λ hΛ hEll hc) i 0 0 w J u G -
        ζ * (∫ x, w x * (∑ j, (a x j i : ℂ) * G j x)) = ∫ x, w x * F x) :
    (Λ⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j x‖ ^ 2)) ≤
      (∫ x, (φ x : ℂ) ^ 2 * star (u x) * (F x - V x)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * Λ ^ 3) *
        (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
          (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖u x‖ ^ 2) := by
  obtain ⟨hφb, hDφ⟩ := physicalLocalEnergy_cutoff_bounds φ hφ hφc
  have hlower : ∀ᵐ x ∂volume, ∀ ξ : Vec d,
      Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ) :=
    Filter.Eventually.of_forall fun x ξ => ((hEll x).2 ξ).1
  have hA : ∀ᵐ x ∂volume, ∀ j k, |a x j k| ≤ Λ :=
    Filter.Eventually.of_forall fun x j k => Correctors.IsElliptic.entry_abs_le hΛ hEll x j k
  have hbound := physicalLocalEnergy_weakEquation a
    (memLp_complex_elliptic_entry volume a Λ hΛ hEll hc) i Λ⁻¹ Λ
    (inv_pos.mpr hΛ) hlower hA ζ U φ hφ hφb hDφ hφU u V F G hu hweak
  have hconst : 2 * (d : ℝ) * ((d : ℝ) + 1) * Λ ^ 2 / Λ⁻¹ =
      2 * (d : ℝ) * ((d : ℝ) + 1) * Λ ^ 3 := by
    rw [div_inv_eq_mul]
    ring
  rw [hconst] at hbound
  exact hbound

end EinsteinFull
