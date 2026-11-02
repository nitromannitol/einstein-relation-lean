import EinsteinFull.Calculus.S5EnergySupport
import EinsteinFull.Blueprint.Foundation.Proofs.W1CenteredSource

/-! Cutoff coercivity for the complex forward equation. The cutoff may vanish.
These estimates retain Euclidean gradient energy; they do not assert the
space-time energy identity or an interior time-slice estimate. -/

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private lemma cutoff_young (L x y : ℝ) (hL : 0 < L) :
    x * y ≤ L⁻¹ / 8 * x ^ 2 + 2 * L * y ^ 2 := by
  have hs := mul_nonneg (inv_pos.mpr hL).le (sq_nonneg (x - 4 * L * y))
  have he : L⁻¹ * (x - 4 * L * y) ^ 2 =
      L⁻¹ * x ^ 2 - 8 * x * y + 16 * L * y ^ 2 := by
    field_simp
    ring
  rw [he] at hs
  linarith only [hs]

/-- Pointwise cutoff testing retains a quarter of the principal coercivity.
The two errors are the literal cutoff-gradient and complex-force contributions.
No bound of the gradient of the cutoff by the cutoff itself is required. -/
theorem complexForced_cutoff_coercive {d : ℕ} {A : Fin d → Fin d → ℝ} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (X : Fin d → ℂ) (u : ℂ)
    (D : Fin d → ℝ) (η : ℝ) (i : Fin d) (ζ : ℂ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
        (((η ^ 2 : ℝ) : ℂ) * star (X j) +
          star u * ((2 * η * D j : ℝ) : ℂ))) +
      ζ * ((∑ j, (A j i : ℂ) * X j) * (((η ^ 2 : ℝ) : ℂ) * star u))).re ≤
    -(Λ⁻¹ / 4) * η ^ 2 * (∑ j, ‖X j‖ ^ 2) +
      8 * Λ ^ 3 * (s5Nrm D ^ 2 + ‖ζ‖ ^ 2 * η ^ 2) * ‖u‖ ^ 2 := by
  let T := ∑ j, ∑ k, (A j k : ℂ) * X k * star (X j)
  let B := ∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k
  let F := ∑ j, (A j i : ℂ) * X j
  have hL : 0 < Λ := lt_of_lt_of_le zero_lt_one hA.one_le
  have hT : Λ⁻¹ * s5CNrm X ^ 2 ≤ T.re := by
    rw [s5CNrm, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    exact s5_coercive hA X
  have hB : ‖B‖ ≤ 2 * Λ * s5Nrm D * s5CNrm X := s5_cbil_norm_le hA D X
  have hF : ‖F‖ ≤ 2 * Λ * s5CNrm X := s5_row_norm_le hA i X
  have hc' : -η * (star u * B).re ≤
      |η| * ‖u‖ * (2 * Λ * s5Nrm D * s5CNrm X) := by
    calc
      _ ≤ |η| * |(star u * B).re| := by
        simpa only [abs_mul, abs_neg, neg_mul] using neg_le_abs (η * (star u * B).re)
      _ ≤ |η| * (‖u‖ * (2 * Λ * s5Nrm D * s5CNrm X)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (Complex.abs_re_le_norm _).trans (by
          rw [norm_mul, norm_star]
          exact mul_le_mul_of_nonneg_left hB (norm_nonneg _))
      _ = _ := by ring
  have hf : (ζ * (F * (((η ^ 2 : ℝ) : ℂ) * star u))).re ≤
      ‖ζ‖ * (2 * Λ * s5CNrm X) * η ^ 2 * ‖u‖ := by
    calc
      _ ≤ ‖ζ * (F * (((η ^ 2 : ℝ) : ℂ) * star u))‖ := Complex.re_le_norm _
      _ = ‖ζ‖ * ‖F‖ * η ^ 2 * ‖u‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_star, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η)]
        ring
      _ ≤ _ := by gcongr
  have hy₁ := cutoff_young Λ (|η| * s5CNrm X) (2 * Λ * s5Nrm D * ‖u‖) hL
  have hy₂ := cutoff_young Λ (|η| * s5CNrm X) (2 * Λ * ‖ζ‖ * |η| * ‖u‖) hL
  have hp := mul_le_mul_of_nonneg_left hT (sq_nonneg η)
  have he : (∑ j, ∑ k, (A j k : ℂ) * X k *
        (((η ^ 2 : ℝ) : ℂ) * star (X j) + star u * ((2 * η * D j : ℝ) : ℂ))) =
      ((η ^ 2 : ℝ) : ℂ) * T + (2 * η : ℂ) * (star u * B) := by
    simp only [T, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  have hn : ∑ j, ‖X j‖ ^ 2 = s5CNrm X ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
  rw [hn]
  change (-(1 / 2 : ℂ) * (((η ^ 2 : ℝ) : ℂ) * T +
    (2 * η : ℂ) * (star u * B)) + ζ * (F * (((η ^ 2 : ℝ) : ℂ) * star u))).re ≤ _
  have hr : (-(1 / 2 : ℂ) * (((η ^ 2 : ℝ) : ℂ) * T +
      (2 * η : ℂ) * (star u * B))).re =
      -(1 / 2 : ℝ) * η ^ 2 * T.re - η * (star u * B).re := by
    have hc : (-(1 / 2 : ℂ)) = (((-(1 / 2 : ℝ)) : ℝ) : ℂ) := by norm_num
    have hη : (2 * (η : ℂ)) = ((2 * η : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.re_ofReal_mul, Complex.add_re, hη,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  rw [Complex.add_re, hr]
  ring_nf at hy₁ hy₂
  simp only [sq_abs] at hy₁ hy₂
  nlinarith only [hp, hc', hf, hy₁, hy₂]

/-- The actual corrected orbit has the forced gradient coercivity, with its
ordinary positive-time derivative produced internally. This is a stationary
energy bound, and does not provide a local space-time Caccioppoli estimate. -/
theorem complexForced_correctedOrbit_coercive
    {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t : ℝ} (ht : 0 < t) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∀ r : ℝ, 0 < r → ∃ (V : Lp ℂ 2 (reducedLaw Q))
      (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasDerivAt w V r ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (w r) G ∧
      ((Real.exp (2 * Λ) * Λ)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) ≤
        -(inner ℂ (w r) V).re + complexForceShift d Λ ζ * ‖w r‖ ^ 2 := by
  intro w r hr
  obtain ⟨V, hd, hg⟩ := Blueprint.centered_source_corrected_equation hP f ht r hr
  obtain ⟨G, hG, hb⟩ := hg.forced_coercive
  exact ⟨V, G, hd, hG, hb⟩


/-- Coordinate Cauchy--Schwarz for complex bilinear pairings. -/
theorem complex_coordinate_pairing_norm_le {d : ℕ} (X Y : Fin d → ℂ) :
    ‖∑ j, X j * Y j‖ ≤ s5CNrm X * s5CNrm Y := by
  calc
    _ ≤ ∑ j, ‖X j * Y j‖ := norm_sum_le _ _
    _ = ∑ j, ‖X j‖ * ‖Y j‖ := by simp only [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

private theorem output_mixed_young (ε x y : ℝ) (hε : 0 < ε) :
    x * y ≤ ε * x ^ 2 + y ^ 2 / (4 * ε) := by
  have h := div_nonneg (sq_nonneg (2 * ε * x - y)) (by positivity : 0 ≤ 4 * ε)
  have he : (2 * ε * x - y) ^ 2 / (4 * ε) =
      ε * x ^ 2 - x * y + y ^ 2 / (4 * ε) := by
    field_simp
    ring
  rw [he] at h
  linarith

/-- Testing by the generator output retains half of its squared mass.
The coefficient of its gradient energy can be chosen arbitrarily small. -/
theorem complexFlux_cutoff_output_young {d : ℕ}
    (F Y : Fin d → ℂ) (D : Fin d → ℝ) (v b ζ : ℂ) (η ε : ℝ) (hε : 0 < ε) :
    (ζ * ((η : ℂ) ^ 2 * star v * b) -
      ∑ j, F j * ((η : ℂ) ^ 2 * star (Y j) +
        2 * (η : ℂ) * (D j : ℂ) * star v)).re ≤
      (1 / 2 : ℝ) * η ^ 2 * ‖v‖ ^ 2 +
      ε * η ^ 2 * (∑ j, ‖Y j‖ ^ 2) +
      (η ^ 2 / (4 * ε) + 4 * (∑ j, D j ^ 2)) * (∑ j, ‖F j‖ ^ 2) +
      ‖ζ‖ ^ 2 * η ^ 2 * ‖b‖ ^ 2 := by
  let B := ∑ j, F j * star (Y j)
  let E := ∑ j, (D j : ℂ) * F j
  have hB : ‖B‖ ≤ s5CNrm F * s5CNrm Y := by
    simpa only [s5CNrm, norm_star] using
      complex_coordinate_pairing_norm_le F (fun j => star (Y j))
  have hE : ‖E‖ ≤ s5Nrm D * s5CNrm F := by
    simpa only [s5CNrm, Complex.norm_real, Real.norm_eq_abs, sq_abs, s5Nrm] using
      complex_coordinate_pairing_norm_le (fun j => (D j : ℂ)) F
  have halg : (∑ j, F j * ((η : ℂ) ^ 2 * star (Y j) +
      2 * (η : ℂ) * (D j : ℂ) * star v)) =
      (η : ℂ) ^ 2 * B + 2 * (η : ℂ) * star v * E := by
    simp only [B, E, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp : (-(η : ℂ) ^ 2 * B).re ≤ η ^ 2 * (s5CNrm F * s5CNrm Y) := by
    calc
      _ ≤ ‖-(η : ℂ) ^ 2 * B‖ := Complex.re_le_norm _
      _ = η ^ 2 * ‖B‖ := by simp only [norm_mul, norm_neg, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (sq_nonneg η)
  have hc : (-(2 * (η : ℂ) * star v * E)).re ≤
      2 * |η| * ‖v‖ * (s5Nrm D * s5CNrm F) := by
    calc
      _ ≤ ‖-(2 * (η : ℂ) * star v * E)‖ := Complex.re_le_norm _
      _ = 2 * |η| * ‖v‖ * ‖E‖ := by
        norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)
  have hd : (ζ * ((η : ℂ) ^ 2 * star v * b)).re ≤
      ‖ζ‖ * η ^ 2 * ‖v‖ * ‖b‖ := by
    calc
      _ ≤ ‖ζ * ((η : ℂ) ^ 2 * star v * b)‖ := Complex.re_le_norm _
      _ = _ := by simp only [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, norm_star]; ring
  have hyP := mul_le_mul_of_nonneg_left
    (output_mixed_young ε (s5CNrm Y) (s5CNrm F) hε) (sq_nonneg η)
  have hyC := output_mixed_young (1 / 4) (|η| * ‖v‖)
    (2 * s5Nrm D * s5CNrm F) (by norm_num)
  have hyD := output_mixed_young (1 / 4) (|η| * ‖v‖)
    (‖ζ‖ * |η| * ‖b‖) (by norm_num)
  have hFn : s5CNrm F ^ 2 = ∑ j, ‖F j‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hYn : s5CNrm Y ^ 2 = ∑ j, ‖Y j‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hDn : s5Nrm D ^ 2 = ∑ j, D j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  rw [halg]
  have hr : (ζ * ((η : ℂ) ^ 2 * star v * b) -
      ((η : ℂ) ^ 2 * B + 2 * (η : ℂ) * star v * E)).re =
      (ζ * ((η : ℂ) ^ 2 * star v * b)).re +
      (-(η : ℂ) ^ 2 * B).re + (-(2 * (η : ℂ) * star v * E)).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, neg_mul]
    ring
  rw [hr]
  simp only [mul_pow, sq_abs, hFn, hYn, hDn] at hyP hyC hyD
  norm_num at hyC hyD
  have heD : |η| * ‖v‖ * (‖ζ‖ * |η| * ‖b‖) = ‖ζ‖ * η ^ 2 * ‖v‖ * ‖b‖ := by
    calc
      _ = ‖ζ‖ * |η| ^ 2 * ‖v‖ * ‖b‖ := by ring
      _ = _ := by rw [sq_abs]
  rw [heD] at hyD
  simp only [div_eq_mul_inv] at hyP ⊢
  nlinarith only [hp, hc, hd, hyP, hyC, hyD]


/-- A uniformly bounded row controls the squared complex linear form. -/
theorem complex_coordinate_row_sq_le {d : ℕ} (A : Fin d → ℝ) (X : Fin d → ℂ)
    {L : ℝ} (hA : ∀ j, |A j| ≤ L) :
    ‖∑ j, (A j : ℂ) * X j‖ ^ 2 ≤ (d : ℝ) * L ^ 2 * (∑ j, ‖X j‖ ^ 2) := by
  have hs : (∑ j, |A j| ^ 2) ≤ (d : ℝ) * L ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, L ^ 2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (abs_nonneg _) (hA j) 2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ‖∑ j, (A j : ℂ) * X j‖ ≤ ∑ j, |A j| * ‖X j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      (norm_sum_le Finset.univ (fun j => (A j : ℂ) * X j))
  calc
    _ ≤ (∑ j, |A j| * ‖X j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (∑ j, |A j| ^ 2) * (∑ j, ‖X j‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- Squared physical flux bound, with explicit dimension and entry constants. -/
theorem complex_matrix_halfFlux_sq_le {d : ℕ} (A : Fin d → Fin d → ℝ)
    (X : Fin d → ℂ) {L : ℝ} (hA : ∀ j k, |A j k| ≤ L) :
    (∑ j, ‖(1 / 2 : ℂ) * ∑ k, (A j k : ℂ) * X k‖ ^ 2) ≤
      ((d : ℝ) ^ 2 * L ^ 2 / 4) * (∑ k, ‖X k‖ ^ 2) := by
  calc
    _ = ∑ j, (1 / 4 : ℝ) * ‖∑ k, (A j k : ℂ) * X k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, mul_pow]
      norm_num
    _ ≤ ∑ j : Fin d, (1 / 4 : ℝ) *
        ((d : ℝ) * L ^ 2 * (∑ k, ‖X k‖ ^ 2)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (complex_coordinate_row_sq_le (A j) X (hA j)) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring


/-- Quantitative mixed testing for the literal matrix flux and drift.
Only the original and output gradient energies occur on the right. -/
theorem complexMatrix_cutoff_output_young {d : ℕ}
    (A : Fin d → Fin d → ℝ) (X Y : Fin d → ℂ) (D : Fin d → ℝ)
    (v ζ : ℂ) (η ε : ℝ) (i : Fin d) {L : ℝ}
    (hA : ∀ j k, |A j k| ≤ L) (hε : 0 < ε) :
    (ζ * ((η : ℂ) ^ 2 * star v * (∑ j, (A j i : ℂ) * X j)) -
      ∑ j, ((1 / 2 : ℂ) * ∑ k, (A j k : ℂ) * X k) *
        ((η : ℂ) ^ 2 * star (Y j) + 2 * (η : ℂ) * (D j : ℂ) * star v)).re ≤
      (1 / 2 : ℝ) * η ^ 2 * ‖v‖ ^ 2 + ε * η ^ 2 * (∑ j, ‖Y j‖ ^ 2) +
      (((η ^ 2 / (4 * ε) + 4 * (∑ j, D j ^ 2)) * ((d : ℝ) ^ 2 * L ^ 2 / 4)) +
        ‖ζ‖ ^ 2 * η ^ 2 * ((d : ℝ) * L ^ 2)) * (∑ j, ‖X j‖ ^ 2) := by
  have hy := complexFlux_cutoff_output_young
    (fun j => (1 / 2 : ℂ) * ∑ k, (A j k : ℂ) * X k) Y D v
    (∑ j, (A j i : ℂ) * X j) ζ η ε hε
  have hF := mul_le_mul_of_nonneg_left (complex_matrix_halfFlux_sq_le A X hA)
    (by positivity : 0 ≤ η ^ 2 / (4 * ε) + 4 * (∑ j, D j ^ 2))
  have hb := mul_le_mul_of_nonneg_left
    (complex_coordinate_row_sq_le (fun j => A j i) X (fun j => hA j i))
    (by positivity : 0 ≤ ‖ζ‖ ^ 2 * η ^ 2)
  nlinarith only [hy, hF, hb]


/-- Absorb a nested-cylinder recurrence with fourth-power dyadic gap loss.
The uniform finite bound is only used to eliminate the outer-mass tail. -/
theorem nested_cylinder_fourth_power_absorption {F : ℕ → ℝ} {θ C M : ℝ}
    (hθ : 0 ≤ θ) (hsmall : θ < 1 / 16) (hC : 0 ≤ C)
    (hfinite : ∀ n, F n ≤ M)
    (hstep : ∀ n, F n ≤ θ * F (n + 1) + C * 16 ^ n) :
    F 0 ≤ C / (1 - 16 * θ) := by
  have hden : 0 < 1 - 16 * θ := by linarith
  have hiter : ∀ k n : ℕ,
      F n ≤ θ ^ k * M + C * 16 ^ n / (1 - 16 * θ) := by
    intro k
    induction k with
    | zero =>
        intro n
        simp only [pow_zero, one_mul]
        exact (hfinite n).trans (le_add_of_nonneg_right (by positivity))
    | succ k ih =>
        intro n
        have hh := (hstep n).trans
          (add_le_add (mul_le_mul_of_nonneg_left (ih (n + 1)) hθ) le_rfl)
        have he : θ * (θ ^ k * M + C * 16 ^ (n + 1) / (1 - 16 * θ)) +
            C * 16 ^ n = θ ^ (k + 1) * M + C * 16 ^ n / (1 - 16 * θ) := by
          have hcancel := mul_inv_cancel₀ hden.ne'
          rw [pow_succ, pow_succ]
          simp only [div_eq_mul_inv]
          linear_combination -(C * 16 ^ n) * hcancel
        exact he ▸ hh
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ
    (show θ < 1 by linarith)).mul_const M
  have ht' := ht.add_const (C / (1 - 16 * θ))
  simp only [zero_mul, zero_add] at ht'
  apply ge_of_tendsto ht'
  exact Filter.Eventually.of_forall (fun k => by simpa only [pow_zero, mul_one] using hiter k 0)

end EinsteinFull
