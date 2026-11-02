import EinsteinFull.Calculus.PhysicalH1WeightedIntegrationSupport
import EinsteinFull.Calculus.PhysicalFormPolynomialSupport
import EinsteinRelation.Environment.EuclideanLipschitz

/-! Explicit complex-force coefficients of the actual physical gauge form.

The smooth coefficient bounds follow from operator Lipschitz regularity via the
pinned EinsteinRelation Euclidean-coordinate adapter. Weighted whole-space H1
integration by parts identifies the linear coefficient with half the column
divergence. No additional analytic input is assumed.
-/

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Smooth Lipschitz scalar fields have bounded actual coordinate derivatives. -/
theorem memLp_complex_coordinateDerivative {d : ℕ} {φ : Vec d → ℝ} {L : ℝ≥0}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hL : LipschitzWith L φ) (j : Fin d) :
    MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume := by
  have hD : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).continuous
  apply memLp_top_of_bound (Complex.continuous_ofReal.comp hD).aestronglyMeasurable (L : ℝ)
  apply Filter.Eventually.of_forall
  intro x
  change ‖(coordinateDerivative j φ x : ℂ)‖ ≤ (L : ℝ)
  rw [Complex.norm_real]
  unfold coordinateDerivative
  calc
    ‖fderiv ℝ φ x (unitVector j)‖ ≤ ‖fderiv ℝ φ x‖ * ‖unitVector j‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L : ℝ) * ‖unitVector j‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _)
    _ = L := by simp only [unitVector, Pi.norm_single, norm_one, mul_one]

/-- All actual coefficient derivatives are bounded for a smooth operator-Lipschitz matrix. -/
theorem memLp_complex_coefficientDerivative {d : ℕ} (a : Vec d → Mat d) (B : ℝ)
    (hB : 0 ≤ B) (ha : IsOperatorLipschitz B a)
    (haSmooth : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (j k l : Fin d) :
    MemLp (fun x => (coordinateDerivative l (fun y => a y j k) x : ℂ)) ∞ volume :=
  memLp_complex_coordinateDerivative (haSmooth j k)
    (lipschitzWith_of_euclidean_bound B hB (ha.entry_bound j k)) l

/-- The literal shifted-gradient integrand has the column cross term for symmetric coefficients. -/
theorem physicalFormIntegrand_expansion {d : ℕ} (A : Mat d) (hA : A.transpose = A)
    (i : Fin d) (u v : ℂ) (G H : Fin d → ℂ) (ζ : ℂ) :
    (∑ j : Fin d, ∑ k : Fin d,
      (G j - ζ * (unitVector i j : ℂ) * u) * (A j k : ℂ) *
        (H k - ζ * (unitVector i k : ℂ) * v)) =
    (∑ j : Fin d, ∑ k : Fin d, G j * (A j k : ℂ) * H k) -
      ζ * (∑ j : Fin d, (G j * (A j i : ℂ) * v + u * (A j i : ℂ) * H j)) +
      ζ ^ 2 * ((A i i : ℂ) * u * v) := by
  have hsym (j k : Fin d) : A j k = A k j := by
    exact (congrFun (congrFun hA k) j)
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [unitVector, Pi.single_apply, apply_ite Complex.ofReal, Complex.ofReal_one,
    Complex.ofReal_zero, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp_rw [hsym i]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

/-- Integration of the literal symmetric shifted-gradient expansion. -/
theorem physicalBilinearForm_cross_expansion {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ x, (a x).transpose = a x) (i : Fin d) (s : ℝ)
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (ζ : ℂ) :
    physicalBilinearForm volume a ha i s ζ u G v H =
      physicalBilinearForm volume a ha i s 0 u G v H -
      (ζ / 2) * (∫ x, ∑ j : Fin d,
        (G j x * (a x j i : ℂ) * v x + u x * (a x j i : ℂ) * H j x)) +
      (ζ ^ 2 / 2) * (∫ x, (a x i i : ℂ) * u x * v x) := by
  let E (z : ℂ) (x : Vec d) := ∑ j : Fin d, ∑ k : Fin d,
    (G j x - z * (unitVector i j : ℂ) * u x) * (a x j k : ℂ) *
      (H k x - z * (unitVector i k : ℂ) * v x)
  let L (x : Vec d) := ∑ j : Fin d,
    (G j x * (a x j i : ℂ) * v x + u x * (a x j i : ℂ) * H j x)
  let Q (x : Vec d) := (a x i i : ℂ) * u x * v x
  have hL : Integrable L volume := by
    apply integrable_finset_sum
    intro j _
    exact ((Lp.memLp (G j)).fun_mul (r := 2) (ha j i) |>.integrable_mul (Lp.memLp v)).add
      ((Lp.memLp u).fun_mul (r := 2) (ha j i) |>.integrable_mul (Lp.memLp (H j)))
  have hQ : Integrable Q volume :=
    (ha i i).fun_mul (r := 2) (Lp.memLp u) |>.integrable_mul (Lp.memLp v)
  have hE : Integrable (E 0) volume :=
    (physicalBilinearForm_integrable volume a ha i 0 u v G H).2
  have hpoint (x : Vec d) : E ζ x = E 0 x - ζ * L x + ζ ^ 2 * Q x := by
    simpa only [E, L, Q, zero_mul, sub_zero] using
      physicalFormIntegrand_expansion (a x) (hsym x) i (u x) (v x)
        (fun j => G j x) (fun j => H j x) ζ
  have hInt : (∫ x, E ζ x) = (∫ x, E 0 x) - ζ * (∫ x, L x) +
      ζ ^ 2 * (∫ x, Q x) := by
    calc
      (∫ x, E ζ x) = ∫ x, E 0 x - ζ * L x + ζ ^ 2 * Q x :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by
        rw [integral_add (f := fun x => E 0 x - ζ * L x)
          (g := fun x => ζ ^ 2 * Q x) (hE.sub (hL.const_mul ζ)) (hQ.const_mul (ζ ^ 2)),
          integral_sub (f := fun x => E 0 x) (g := fun x => ζ * L x)
            hE (hL.const_mul ζ), integral_const_mul, integral_const_mul]
  change (s : ℂ) * (∫ x, u x * v x) + (1 / 2 : ℂ) * (∫ x, E ζ x) =
    ((s : ℂ) * (∫ x, u x * v x) + (1 / 2 : ℂ) * (∫ x, E 0 x)) -
      (ζ / 2) * (∫ x, L x) + (ζ ^ 2 / 2) * (∫ x, Q x)
  rw [hInt]
  ring

/-- The actual linear force coefficient is half the column divergence. -/
theorem physicalBilinearForm_expansion {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hsym : ∀ x, (a x).transpose = a x)
    (haSmooth : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hDa : ∀ j k l, MemLp
      (fun x => (coordinateDerivative l (fun y => a y j k) x : ℂ)) ∞ volume)
    (i : Fin d) (s : ℝ)
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) (ζ : ℂ) :
    physicalBilinearForm volume a ha i s ζ u G v H =
      physicalBilinearForm volume a ha i s 0 u G v H +
      ζ * (∫ x, (((1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => a y j i) x : ℝ) : ℂ) * u x * v x) +
      (ζ ^ 2 / 2) * (∫ x, (a x i i : ℂ) * u x * v x) := by
  have h1 (j : Fin d) : Integrable (fun x => G j x * (a x j i : ℂ) * v x) volume :=
    (Lp.memLp (G j)).fun_mul (r := 2) (ha j i) |>.integrable_mul (Lp.memLp v)
  have h2 (j : Fin d) : Integrable (fun x => u x * (a x j i : ℂ) * H j x) volume :=
    (Lp.memLp u).fun_mul (r := 2) (ha j i) |>.integrable_mul (Lp.memLp (H j))
  have hD (j : Fin d) : Integrable (fun x =>
      (coordinateDerivative j (fun y => a y j i) x : ℂ) * u x * v x) volume :=
    (hDa j i j).fun_mul (r := 2) (Lp.memLp u) |>.integrable_mul (Lp.memLp v)
  have hcross : (∫ x, ∑ j : Fin d,
      (G j x * (a x j i : ℂ) * v x + u x * (a x j i : ℂ) * H j x)) =
      -(∫ x, ∑ j : Fin d,
        (coordinateDerivative j (fun y => a y j i) x : ℂ) * u x * v x) := by
    rw [integral_finset_sum Finset.univ
      (f := fun j x => G j x * (a x j i : ℂ) * v x + u x * (a x j i : ℂ) * H j x)
      (fun j _ => (h1 j).add (h2 j)),
      integral_finset_sum Finset.univ
        (f := fun j x => (coordinateDerivative j (fun y => a y j i) x : ℂ) * u x * v x)
        (fun j _ => hD j), ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_add (h1 j) (h2 j)]
    exact physicalH1Graph_integral_weighted_gradient (fun x => a x j i)
      (haSmooth j i) (ha j i) (hDa j i) u v G H hu hv j
  have hhalf : (∫ x, (((1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => a y j i) x : ℝ) : ℂ) * u x * v x) =
      (1 / 2 : ℂ) * (∫ x, ∑ j : Fin d,
        (coordinateDerivative j (fun y => a y j i) x : ℂ) * u x * v x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.sum_mul, mul_assoc]
  rw [physicalBilinearForm_cross_expansion a ha hsym i s u v G H ζ, hcross, hhalf]
  ring

end EinsteinFull
