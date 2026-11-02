import EinsteinFull.Calculus.ComplexGeneratorOperatorSupport

/-!
# Actual stationary force drift and full generator domains

The coefficient column at the origin acts on the Euclidean L2 gradient product.
Its bounded complex linear realization has the actual almost-everywhere flux
representative. Changing the complex force adds precisely this L2 drift to the
full weak generator; in particular all forced domains equal the unforced domain.
-/

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Multiplication on L2 by an actual reduced coefficient entry. -/
def complexCoefficientMul {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j k : Fin d) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ)))

/-- This multiplier retains the actual anisotropic entry, almost everywhere. -/
theorem complexCoefficientMul_coe {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (j k : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    complexCoefficientMul Q j k f =ᵐ[reducedLaw Q] fun ω => (ω.1 0 j k : ℂ) * f ω := by
  have hc := (memLp_reduced_coefficient_complex Q j k).coeFn_toLp
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ))) f
  filter_upwards [hc, hm] with ω ha hb
  simpa only [complexCoefficientMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', ha] using hb

/-- A structural bound for the actual coefficient multiplier. -/
theorem norm_complexCoefficientMul_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j k : Fin d) :
    ‖complexCoefficientMul Q j k‖ ≤ Real.exp (2 * Λ₀) * Λ₀ := by
  have hK : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have he := Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [complexCoefficientMul_coe Q j k f, he] with ω hf hω
  rw [hf, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (hω 0).1
  · intro ξ
    exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
      ((hω 0).2 ξ).1
  · exact fun ξ => ((hω 0).2 ξ).2

/-- The actual column drift, on the Euclidean product of coordinate L2 spaces. -/
def complexForceDrift {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  ∑ j, (complexCoefficientMul Q j i).comp
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j)

/-- The bounded drift agrees with the coefficient-column flux in the frozen graph. -/
theorem complexForceDrift_coe {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    complexForceDrift Q i G =ᵐ[reducedLaw Q]
      fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω := by
  simp only [complexForceDrift, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  have hs : ∀ s : Finset (Fin d),
      (∑ j ∈ s, complexCoefficientMul Q j i (G j) : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
        fun ω => ∑ j ∈ s, (complexCoefficientMul Q j i (G j)) ω := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using! (Lp.coeFn_zero ℂ 2 (reducedLaw Q))
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (complexCoefficientMul Q j i (G j))
        (∑ k ∈ s, complexCoefficientMul Q k i (G k)), ih] with ω ha hb
      simpa only [Pi.add_apply, hb] using ha
  filter_upwards [hs Finset.univ, ae_all_iff.mpr fun j => complexCoefficientMul_coe Q j i (G j)]
    with ω hsum hω
  simpa only [hω] using hsum

/-- A structural drift bound in the Euclidean L2 product norm. -/
theorem norm_complexForceDrift_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    ‖complexForceDrift Q i G‖ ≤ (d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) * ‖G‖ := by
  simp only [complexForceDrift, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  calc
    _ ≤ ∑ j, ‖complexCoefficientMul Q j i (G j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, (Real.exp (2 * Λ₀) * Λ₀) * ‖G‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (norm_complexCoefficientMul_le Q j i) (PiLp.norm_apply_le G j)
          (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le
            (zero_le_one.trans Q.ellipticity_parameter)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

/-- The same bound written explicitly with the Euclidean gradient energy. -/
theorem norm_complexForceDrift_sq_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    ‖complexForceDrift Q i G‖ ^ 2 ≤
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2 * (∑ j, ‖G j‖ ^ 2) := by
  have h := norm_complexForceDrift_apply_le Q i G
  have hs := sq_le_sq₀ (norm_nonneg (complexForceDrift Q i G))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)))
      (norm_nonneg G)) |>.mpr h
  simpa only [mul_pow, PiLp.norm_sq_eq_of_L2] using hs

/-- Bilinear testing of the drift uses exactly the frozen coefficient-column flux. -/
theorem integral_complexForceDrift_mul {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (v : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, (complexForceDrift Q i G) ω * v ω ∂reducedLaw Q) =
      ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω ∂reducedLaw Q := by
  apply integral_congr_ae
  filter_upwards [complexForceDrift_coe Q i G] with ω hω
  rw [hω]

private theorem integral_pair_add_smul {d : ℕ} (μ : Measure (FieldPair d))
    (g b v : Lp ℂ 2 μ) (c : ℂ) :
    (∫ ω, (g + c • b : Lp ℂ 2 μ) ω * v ω ∂μ) =
      (∫ ω, g ω * v ω ∂μ) + c * ∫ ω, b ω * v ω ∂μ := by
  have hg : Integrable (fun ω => g ω * v ω) μ :=
    (Lp.memLp g).integrable_mul (Lp.memLp v)
  have hb : Integrable (fun ω => b ω * v ω) μ :=
    (Lp.memLp b).integrable_mul (Lp.memLp v)
  rw [← integral_const_mul, ← integral_add hg (hb.const_mul c)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add g (c • b), Lp.coeFn_smul c b] with ω ha hb
  simp only [ha, hb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Changing the complex force adds its actual L2 drift, on the full weak domain. -/
theorem IsComplexGeneratorPair.change_force {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (η : ℂ) {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    IsComplexGeneratorPair Q i η f
      (g + (η - ζ) • complexForceDrift Q i (WithLp.toLp 2 G)) := by
  obtain ⟨H, hH, hw⟩ := hfg
  have he : H = G := hH.unique hG
  subst H
  refine ⟨G, hG, fun v Gv hv => ?_⟩
  rw [integral_pair_add_smul, integral_complexForceDrift_mul, hw v Gv hv]
  change _ = -(1 / 2 : ℂ) * _ + η * _
  ring

/-- Every complex force has exactly the same full L2 generator domain. -/
theorem complexGenerator_domain_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ η : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∃ g, IsComplexGeneratorPair Q i ζ f g) ↔
      ∃ g, IsComplexGeneratorPair Q i η f g := by
  have transfer (ζ η : ℂ) (h : ∃ g, IsComplexGeneratorPair Q i ζ f g) :
      ∃ g, IsComplexGeneratorPair Q i η f g := by
    obtain ⟨g, hg⟩ := h
    have hg_copy := hg
    obtain ⟨G, hG, _⟩ := hg_copy
    exact ⟨_, hg.change_force η hG⟩
  exact ⟨transfer ζ η, transfer η ζ⟩

/-- The full actual forced generator domain is dense, without an adjoint premise. -/
theorem dense_complexGenerator_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    Dense {f : Lp ℂ 2 (reducedLaw Q) | ∃ g, IsComplexGeneratorPair Q i ζ f g} := by
  apply (dense_unforced_complexGenerator_domain Q i).mono
  intro f hf
  exact (complexGenerator_domain_iff Q i 0 ζ f).mp hf

end EinsteinFull
