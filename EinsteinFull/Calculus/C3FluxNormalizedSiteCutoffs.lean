import EinsteinFull.Calculus.C3FluxGeneralTestTransfer

open scoped BigOperators
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Normalize a site-weighted multiplier before constructing its Gaussian
recovery cutoffs. The positive site envelope is restored after recovery. -/
lemma c3_normalized_multiplier_bound {d : ℕ} (f : Vec d → ℂ)
    (W A : ℝ) (hW : 0 < W) (hbound : ∀ y, ‖f y‖ ≤ A * W) :
    ∀ y, ‖f y / (W : ℂ)‖ ≤ A := by
  intro y
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW]
  exact (div_le_iff₀ hW).2 (hbound y)

/-- Dividing a smooth complex multiplier by its positive site envelope
scales the Euclidean length of its coordinate derivatives by the same factor. -/
lemma c3_normalized_multiplier_coordinate_length {d : ℕ} (f : Vec d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (W : ℝ) (hW : 0 < W) (x : Vec d) :
    Real.sqrt (∑ k : Fin d,
      ‖fderiv ℝ (fun y => f y / (W : ℂ)) x (unitVector k)‖ ^ 2) =
      Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) / W := by
  have hderiv (k : Fin d) :
      fderiv ℝ (fun y => f y / (W : ℂ)) x (unitVector k) =
        fderiv ℝ f x (unitVector k) / (W : ℂ) := by
    have h := fderiv_const_mul ((hf.differentiable (by norm_num)) x) (W : ℂ)⁻¹
    have hh := congrArg (fun L : Vec d →L[ℝ] ℂ => L (unitVector k)) h
    simpa only [div_eq_mul_inv, smul_apply, smul_eq_mul, mul_comm] using hh
  calc
    _ = Real.sqrt ((∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) / W ^ 2) := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [hderiv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hW, div_pow]
    _ = _ := by
      rw [Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
        Real.sqrt_sq_eq_abs, abs_of_pos hW]

/-- The four split-scale recovery cutoffs retain the site weight by normalizing
both the multiplier and its first derivative before applying the construction. -/
theorem c3_weighted_normalized_recovery_cutoffs_split
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r W A B : ℝ) (hr : 0 < r), 0 < W → 0 ≤ A → 0 ≤ B →
        ∀ f : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} →
        (∀ x, ‖f x‖ ≤ A * W) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤
          (B / r) * W) →
      let g := fun x : Vec d => f x / (W : ℂ)
      let s := r ^ 2
      let v := r • unitVector j
      let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
      let h := fun w : Vec d => g (w + v) /
        (slope v * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
      let δ : Bool → Vec d → ℂ := fun b w => if b then
        slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
      let M : Bool → ℝ := fun b => 2 * C * (1 + A + B) * (if b then r ^ d else r ^ (d + 1))
      let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
        (if q then (δ b w).im else (δ b w).re) / M b
      ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
        Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
        (∀ w, |θ b q w| ≤ 1 / 2) ∧
        (∀ w, Real.sqrt (∑ k : Fin d,
          (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤ 1 / (2 * r)) ∧
        ∀ y, HasSum (fun z : Fin d → ℤ =>
          θ b q (y - fun k => r * (z k : ℝ))) 0 := by
  obtain ⟨C, hC, hcutoffs⟩ := c3_gaussian_recovery_normalized_real_coboundaries_split_scale d hd D
  refine ⟨C, hC, ?_⟩
  intro Q i j r W A B hr hW hA hB f hf hc hs hval hgrad
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x / (W : ℂ)) := hf.div_const _
  have hsupport : Function.support (fun x => f x / (W : ℂ)) ⊆ Function.support f := by
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, ne_eq, not_not] at hx ⊢
    simp [hx]
  have hcompact : HasCompactSupport (fun x => f x / (W : ℂ)) :=
    HasCompactSupport.of_support_subset_isCompact hc.isCompact (hsupport.trans subset_closure)
  have hggrad (x : Vec d) :
      Real.sqrt (∑ k : Fin d,
        ‖fderiv ℝ (fun y => f y / (W : ℂ)) x (unitVector k)‖ ^ 2) ≤ B / r := by
    rw [c3_normalized_multiplier_coordinate_length f hf W hW x]
    exact (div_le_iff₀ hW).2 (hgrad x)
  exact hcutoffs Q i j r hr A B hA hB (fun x => f x / (W : ℂ)) hg hcompact
    (hsupport.trans hs) (c3_normalized_multiplier_bound f W A hW hval) hggrad



/-- The site-normalized recovery differences yield admissible partition
cutoffs for each real and imaginary component. -/
theorem c3_weighted_recovery_admissible_partitions_split
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r W A B : ℝ) (hr : 0 < r), 0 < W → 0 ≤ A → 0 ≤ B →
        ∀ f : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} →
        (∀ x, ‖f x‖ ≤ A * W) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤
          (B / r) * W) →
      let g := fun x : Vec d => f x / (W : ℂ)
      let s := r ^ 2
      let v := r • unitVector j
      let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
      let h := fun w : Vec d => g (w + v) /
        (slope v * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
      let δ : Bool → Vec d → ℂ := fun b w => if b then
        slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
      let M : Bool → ℝ := fun b => 2 * C * (1 + A + B) * (if b then r ^ d else r ^ (d + 1))
      let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
        (fluxPartitionCutoff r w + fluxPartitionCutoff r (w - v)) / 2 +
          (if q then (δ b w).im else (δ b w).re) / M b
      ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
        Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
        (∀ w, |θ b q w| ≤ 1) ∧
        (∀ w, Real.sqrt (∑ k : Fin d, (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤
          (2 * Real.sqrt (d : ℝ) + 2) / r) ∧
        ∀ y, HasSum (fun z : Fin d → ℤ => θ b q (y - fun k => r * (z k : ℝ))) 1 := by
  obtain ⟨C, hC, hcutoffs⟩ := c3_weighted_normalized_recovery_cutoffs_split d hd D
  refine ⟨C, hC, ?_⟩
  intro Q i j r W A B hr hW hA hB f hf hc hs hval hgrad
  have h := hcutoffs Q i j r W A B hr hW hA hB f hf hc hs hval hgrad
  dsimp only at h ⊢
  intro b q
  obtain ⟨hsmooth, hcompact, hsupport, hv, hg, hz⟩ := h b q
  exact c3_flux_averaged_partition_perturbation_admissible r hr j _ hsmooth hcompact hsupport hv hg hz



end EinsteinFull.Blueprint
