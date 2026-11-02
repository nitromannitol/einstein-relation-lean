import EinsteinFull.Calculus.PhysicalH1IntegrationSupport
import Mathlib.MeasureTheory.Function.L2Space

/-! Coercivity of the actual physical gauge form on its full H1 domain.

Real ellipticity controls both complex components. The global cross term is
zero by the proved whole-space H1 identity; no compact-support restriction or
additional regularity assumption is used.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Real quadratic lower bounds extend to complex vectors with their Euclidean squared norm. -/
theorem complex_quadratic_lowerBound {d : ℕ} (A : Mat d) (c : ℝ)
    (ha : ∀ ξ : Vec d, c * euclideanSq ξ ≤ dot ξ (A.mulVec ξ))
    (z : Fin d → ℂ) :
    c * (∑ j, ‖z j‖ ^ 2) ≤ (∑ j : Fin d, ∑ k : Fin d,
      star (z j) * (A j k : ℂ) * z k).re := by
  have hr := ha (fun j => (z j).re)
  have hi := ha (fun j => (z j).im)
  have hE : (∑ j : Fin d, ∑ k : Fin d, star (z j) * (A j k : ℂ) * z k).re =
      dot (fun j => (z j).re) (A.mulVec (fun j => (z j).re)) +
      dot (fun j => (z j).im) (A.mulVec (fun j => (z j).im)) := by
    change Complex.reCLM (∑ j : Fin d, ∑ k : Fin d, star (z j) * (A j k : ℂ) * z k) = _
    simp only [map_sum]
    simp only [Complex.reCLM_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      mul_zero, sub_zero, zero_add, neg_mul, sub_neg_eq_add]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hN : (∑ j, ‖z j‖ ^ 2) =
      euclideanSq (fun j => (z j).re) + euclideanSq (fun j => (z j).im) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, euclideanSq, dot,
      Finset.sum_add_distrib]
  rw [hE, hN, mul_add]
  exact add_le_add hr hi

/-- The actual L2 norm squared is the integral of the squared pointwise norm. -/
theorem physicalL2_norm_sq {d : ℕ} (m : Measure (Vec d)) (u : Lp ℂ 2 m) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- A real constant shift has exactly its mass contribution on the full H1 domain. -/
theorem physicalH1Graph_integral_shiftedGradient_sq {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) (j : Fin d) (c : ℝ) :
    (∫ x, ‖G j x - (c : ℂ) * u x‖ ^ 2) = ‖G j‖ ^ 2 + c ^ 2 * ‖u‖ ^ 2 := by
  have hpoint (x : Vec d) : ‖G j x - (c : ℂ) * u x‖ ^ 2 =
      ‖G j x‖ ^ 2 + c ^ 2 * ‖u x‖ ^ 2 - 2 * c * (star (u x) * G j x).re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hG : Integrable (fun x => ‖G j x‖ ^ 2) volume := (Lp.memLp (G j)).norm.integrable_sq
  have hU : Integrable (fun x => c ^ 2 * ‖u x‖ ^ 2) volume :=
    ((Lp.memLp u).norm.integrable_sq).const_mul _
  have hcross : Integrable (fun x => 2 * c * (star (u x) * G j x).re) volume :=
    (((Lp.memLp u).star.integrable_mul (Lp.memLp (G j))).re).const_mul _
  have hGU : Integrable (fun x => ‖G j x‖ ^ 2 + c ^ 2 * ‖u x‖ ^ 2) volume := hG.add hU
  simp_rw [hpoint]
  rw [integral_sub hGU hcross, integral_add hG hU,
    integral_const_mul, integral_const_mul,
    physicalH1Graph_integral_re_star_mul_gradient_zero u G hu j,
    mul_zero, sub_zero, ← physicalL2_norm_sq, ← physicalL2_norm_sq]

/-- The gauge energy satisfies the lower bound on the full physical H1 domain. -/
theorem physicalBilinearForm_coercive {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k : Fin d, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (lam s a_minus : ℝ)
    (hlower : ∀ x ξ : Vec d, a_minus * euclideanSq ξ ≤ dot ξ ((a x).mulVec ξ))
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    (s + a_minus * lam ^ 2 / 2) * ‖u‖ ^ 2 +
      (a_minus / 2) * (∑ j : Fin d, ‖G j‖ ^ 2) ≤
    (physicalBilinearForm volume a ha i s (lam : ℂ)
      (star u) (fun j => star (G j)) u G).re := by
  classical
  let S (j : Fin d) (x : Vec d) := G j x - (lam : ℂ) * (unitVector i j : ℂ) * u x
  let Q (x : Vec d) := ∑ j : Fin d, ∑ k : Fin d,
    star (S j x) * (a x j k : ℂ) * S k x
  have hS (j : Fin d) : MemLp (S j) 2 volume :=
    (Lp.memLp (G j)).sub ((Lp.memLp u).const_mul _)
  have hN : Integrable (fun x => ∑ j : Fin d, ‖S j x‖ ^ 2) volume :=
    integrable_finset_sum Finset.univ fun j _ => (hS j).norm.integrable_sq
  have hgrad : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
      (star (G j) : Lp ℂ 2 volume) x = star (G j x) :=
    ae_all_iff.mpr fun j => Lp.coeFn_star (G j)
  have hQae : (fun x => ∑ j : Fin d, ∑ k : Fin d,
      ((star (G j) : Lp ℂ 2 volume) x - (lam : ℂ) * (unitVector i j : ℂ) *
        (star u : Lp ℂ 2 volume) x) * (a x j k : ℂ) *
      (G k x - (lam : ℂ) * (unitVector i k : ℂ) * u x)) =ᵐ[volume] Q := by
    filter_upwards [Lp.coeFn_star u, hgrad] with x hx hGx
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    change (star u : Lp ℂ 2 volume) x = star (u x) at hx
    rw [hx, hGx j]
    simp only [S, Complex.star_def, map_sub, map_mul, Complex.conj_ofReal]
  have hQ : Integrable Q volume :=
    (physicalBilinearForm_integrable volume a ha i (lam : ℂ) (star u) u
      (fun j => star (G j)) G).2.congr hQae
  have hmass : (∫ x, (star u : Lp ℂ 2 volume) x * u x).re = ‖u‖ ^ 2 := by
    have hae : (fun x => (star u : Lp ℂ 2 volume) x * u x) =ᵐ[volume]
        fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
      filter_upwards [Lp.coeFn_star u] with x hx
      rw [hx]
      exact Complex.normSq_eq_conj_mul_self.symm.trans
        (congrArg (fun r : ℝ => (r : ℂ)) (Complex.normSq_eq_norm_sq (u x)))
    rw [integral_congr_ae hae, integral_complex_ofReal, Complex.ofReal_re,
      ← physicalL2_norm_sq]
  have hform : (physicalBilinearForm volume a ha i s (lam : ℂ)
      (star u) (fun j => star (G j)) u G).re = s * ‖u‖ ^ 2 + (1 / 2 : ℝ) * ∫ x, (Q x).re := by
    unfold physicalBilinearForm
    rw [integral_congr_ae hQae]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hmass]
    have hQr : (∫ x, (Q x).re) = (∫ x, Q x).re := integral_re hQ
    rw [hQr]
    norm_num
  have hbound : a_minus * (∫ x, ∑ j : Fin d, ‖S j x‖ ^ 2) ≤ ∫ x, (Q x).re := by
    rw [← integral_const_mul]
    apply integral_mono (hN.const_mul _) hQ.re
    intro x
    exact complex_quadratic_lowerBound (a x) a_minus (hlower x) (fun j => S j x)
  have hnorm : (∫ x, ∑ j : Fin d, ‖S j x‖ ^ 2) =
      (∑ j : Fin d, ‖G j‖ ^ 2) + lam ^ 2 * ‖u‖ ^ 2 := by
    rw [integral_finset_sum _ (fun j _ => (hS j).norm.integrable_sq)]
    have hterm (j : Fin d) : (∫ x, ‖S j x‖ ^ 2) =
        ‖G j‖ ^ 2 + (lam * unitVector i j) ^ 2 * ‖u‖ ^ 2 := by
      simpa only [S, Complex.ofReal_mul] using
        physicalH1Graph_integral_shiftedGradient_sq u G hu j (lam * unitVector i j)
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, unitVector, Pi.single_apply, mul_ite, mul_one,
      mul_zero, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hnorm] at hbound
  rw [hform]
  linarith only [hbound]

end EinsteinFull
