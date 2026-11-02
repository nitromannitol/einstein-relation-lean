import EinsteinFull.Blueprint.Foundation.node_p_u3A_gauge_u23_holomorphic

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem integral_norm_product_le {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ‖u x‖ * ‖v x‖) ≤ ‖u‖ * ‖v‖ := by
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using Lp.memLp u) (by simpa using Lp.memLp v)
  have hr (w : Lp ℂ 2 (volume : Measure (Vec d))) :
      (∫ x, ‖w x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖w‖ := by
    simp_rw [Real.rpow_two]
    have hn : ‖w‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 := by
      calc
        ‖w‖ ^ 2 = inner ℝ w w := (real_inner_self_eq_norm_sq w).symm
        _ = ∫ x, inner ℝ (w x) (w x) := L2.inner_def w w
        _ = _ := by simp only [real_inner_self_eq_norm_sq]
    rw [← Real.sqrt_eq_rpow, ← hn, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hr] using hh

private theorem coefficient_product_bound {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ)
    (a : Vec d → Mat d) (ha : IsElliptic Λ a)
    (hcoef : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (j k : Fin d) (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x, (a x j k : ℂ) * u x * v x‖ ≤ Λ * ‖u‖ * ‖v‖ := by
  have hi := (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm
  calc
    _ ≤ ∫ x, ‖(a x j k : ℂ) * u x * v x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, Λ * (‖u x‖ * ‖v x‖) := by
      apply integral_mono_ae
        (by
          simpa only [Pi.mul_apply, mul_comm (u _)] using
            (((hcoef j k).mul' (r := 2) (Lp.memLp u)).integrable_mul (Lp.memLp v)).norm)
        (hi.const_mul Λ)
      exact Filter.Eventually.of_forall fun x => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Pi.mul_apply]
        have hb := Correctors.IsElliptic.entry_abs_le hΛ ha x j k
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb
          (mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x)))
    _ = Λ * (∫ x, ‖u x‖ * ‖v x‖) := integral_const_mul _ _
    _ ≤ Λ * (‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (integral_norm_product_le u v) hΛ.le
    _ = _ := by ring

private theorem coordinate_norm_le_gradient_norm {d : ℕ}
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (j : Fin d) :
    ‖G j‖ ≤ Real.sqrt (∑ k, ‖G k‖ ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun k _ => sq_nonneg ‖G k‖) (Finset.mem_univ j)

/-- Entire physical form with structural bounds, reduced along its sole graph edge.
The graph contract retains the closed-form premise; the adopted coefficient
calculus proves this analytic node independently of closedness. -/
@[nolint unusedArguments]
theorem node_p_u3A_gauge_u23_holomorphic_of_deps
    (_hdeps : node_p_u3A_gauge_u23_closed_u2D_formStmt) :
    node_p_u3A_gauge_u23_holomorphicStmt := by
  intro d _hd Λ hΛ
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  refine ⟨(d : ℝ) * Λ + Λ, by positivity, ?_⟩
  intro i B hB a ha haLip haSmooth
  dsimp only
  intro s _hs u v G H hu hv
  let L : ℂ := ∫ x : Vec d,
    (((1 / 2 : ℝ) * ∑ j : Fin d,
      coordinateDerivative j (fun y => a y j i) x : ℝ) : ℂ) * u x * v x
  let Q : ℂ := (1 / 2 : ℂ) * ∫ x : Vec d, (a x i i : ℂ) * u x * v x
  let ha' := fun j k => memLp_complex_elliptic_entry volume a Λ
    (lt_of_lt_of_le zero_lt_one hΛ) ha (fun j k => (haSmooth j k).continuous) j k
  have hexp (ζ : ℂ) : physicalBilinearForm volume a ha' i s ζ u G v H =
      physicalBilinearForm volume a ha' i s 0 u G v H + ζ * L + ζ ^ 2 * Q := by
    have he := physicalBilinearForm_expansion a ha' (fun x => (ha x).1) haSmooth
      (memLp_complex_coefficientDerivative a B hB haLip haSmooth) i s u v G H hu hv ζ
    dsimp only [L, Q]
    rw [he]
    ring
  let X : ℂ := ∫ x, ∑ j : Fin d,
    (G j x * (a x j i : ℂ) * v x + u x * (a x j i : ℂ) * H j x)
  have hlin : L = -(1 / 2 : ℂ) * X := by
    have he := hexp 1
    have hc := physicalBilinearForm_cross_expansion a ha' (fun x => (ha x).1)
      i s u v G H 1
    change _ = _ - (1 / 2 : ℂ) * X + (1 ^ 2 / 2) * _ at hc
    dsimp only [Q] at he
    linear_combination hc - he
  have hX : ‖X‖ ≤ (d : ℝ) * Λ *
      (‖u‖ * Real.sqrt (∑ j, ‖H j‖ ^ 2) + ‖v‖ * Real.sqrt (∑ j, ‖G j‖ ^ 2)) := by
    have hi₁ (j : Fin d) : Integrable (fun x => G j x * (a x j i : ℂ) * v x) :=
      ((Lp.memLp (G j)).fun_mul (r := 2) (ha' j i)).integrable_mul (Lp.memLp v)
    have hi₂ (j : Fin d) : Integrable (fun x => u x * (a x j i : ℂ) * H j x) :=
      ((Lp.memLp u).fun_mul (r := 2) (ha' j i)).integrable_mul (Lp.memLp (H j))
    dsimp only [X]
    rw [integral_finset_sum Finset.univ
      (f := fun j x => G j x * (a x j i : ℂ) * v x + u x * (a x j i : ℂ) * H j x)
      (fun j _ => (hi₁ j).add (hi₂ j))]
    calc
      _ ≤ ∑ j : Fin d, ‖∫ x, G j x * (a x j i : ℂ) * v x +
          u x * (a x j i : ℂ) * H j x‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, Λ *
          (‖u‖ * Real.sqrt (∑ j, ‖H j‖ ^ 2) + ‖v‖ * Real.sqrt (∑ j, ‖G j‖ ^ 2)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [integral_add (hi₁ j) (hi₂ j)]
        have h₁ := coefficient_product_bound Λ (lt_of_lt_of_le zero_lt_one hΛ) a ha ha' j i (G j) v
        have h₂ := coefficient_product_bound Λ (lt_of_lt_of_le zero_lt_one hΛ) a ha ha' j i u (H j)
        simp_rw [mul_comm (a _ j i : ℂ)] at h₁ h₂
        calc
          _ ≤ ‖∫ x, G j x * (a x j i : ℂ) * v x‖ +
            ‖∫ x, u x * (a x j i : ℂ) * H j x‖ := norm_add_le _ _
          _ ≤ Λ * ‖G j‖ * ‖v‖ + Λ * ‖u‖ * ‖H j‖ := add_le_add h₁ h₂
          _ ≤ _ := by
            have hg := mul_le_mul_of_nonneg_right
              (coordinate_norm_le_gradient_norm G j) (mul_nonneg hΛ0 (norm_nonneg v))
            have hh := mul_le_mul_of_nonneg_left
              (coordinate_norm_le_gradient_norm H j) (mul_nonneg hΛ0 (norm_nonneg u))
            nlinarith only [hg, hh]
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  refine ⟨physicalBilinearForm_differentiable volume a ha' i s u v G H, ?_⟩
  intro ζ
  refine ⟨hexp ζ, ?_, ?_⟩
  · change ‖ζ * L‖ ≤ _
    rw [norm_mul, hlin, norm_mul]
    norm_num only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
    have hnon : 0 ≤ ‖u‖ * Real.sqrt (∑ j, ‖H j‖ ^ 2) +
        ‖v‖ * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by positivity
    have hb := mul_le_mul_of_nonneg_left hX (norm_nonneg ζ)
    have hdΛ : 0 ≤ (d : ℝ) * Λ := by positivity
    nlinarith [mul_nonneg (norm_nonneg ζ) hnon, mul_nonneg hΛ0 hnon]
  · change ‖ζ ^ 2 * Q‖ ≤ _
    dsimp only [Q]
    rw [norm_mul, norm_mul, norm_pow]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    have hb := mul_le_mul_of_nonneg_left
      (coefficient_product_bound Λ (lt_of_lt_of_le zero_lt_one hΛ) a ha ha' i i u v)
      (sq_nonneg ‖ζ‖)
    have hmore : 0 ≤ (d : ℝ) * Λ * ‖ζ‖ ^ 2 * ‖u‖ * ‖v‖ := by positivity
    have hbase : 0 ≤ Λ * ‖ζ‖ ^ 2 * ‖u‖ * ‖v‖ := by positivity
    nlinarith only [hb, hmore, hbase]

end EinsteinFull.Blueprint
