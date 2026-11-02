import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Calculus.PhysicalGaugeCoercivitySupport
import EinsteinFull.Calculus.S5SemigroupSupport
import EinsteinFull.Calculus.S5WeightSupport
import EinsteinFull.Calculus.S5WeightGradSupport
import EinsteinFull.Calculus.S5PointwiseSupport

/-!
# Weighted energy inequality on the physical generator graph

For a smooth bounded weight `φ` with `|∇φ| ≤ q |φ|`, every pair in the physical forward or
transpose generator graph satisfies `Re ⟪φ f, φ g⟫ ≤ κ ‖φ f‖²`, `κ = 5 Λ³ (q² + |ζ|²)`.
The test function is `φ² f̄`, whose `H¹` graph is obtained from the conjugate graph and the
smooth product rule.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5Energy

variable {d : ℕ}

theorem s5Bil_eq_dot (M : Mat d) (ξ : Vec d) :
    s5Bil (fun j k => M j k) ξ ξ = dot ξ (M.mulVec ξ) := by
  simp only [s5Bil, dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem s5Elliptic_of_isElliptic {a : Vec d → Mat d} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (h : IsElliptic Λ a) (x : Vec d) : S5Elliptic (fun j k => a x j k) Λ where
  one_le := hΛ
  symm j k := by
    have := congrFun (congrFun (h x).1 j) k
    rw [Matrix.transpose_apply] at this
    exact this.symm
  lower ξ := by
    have h1 := ((h x).2 ξ).1
    have e : euclideanSq ξ = ∑ j, ξ j ^ 2 := by
      unfold euclideanSq dot
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at h1
    rw [s5Bil_eq_dot]
    exact h1
  upper ξ := by
    have h1 := ((h x).2 ξ).2
    have e : euclideanSq ξ = ∑ j, ξ j ^ 2 := by
      unfold euclideanSq dot
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at h1
    rw [s5Bil_eq_dot]
    exact h1

theorem S5Elliptic.entry_abs_le {A : Fin d → Fin d → ℝ} {Λ : ℝ} (h : S5Elliptic A Λ)
    (j k : Fin d) : |A j k| ≤ Λ := by
  have h1 := s5Bil_abs_le h (Pi.single j (1 : ℝ) : Fin d → ℝ) (Pi.single k (1 : ℝ) : Fin d → ℝ)
  have e : s5Bil A (Pi.single j (1 : ℝ) : Fin d → ℝ) (Pi.single k (1 : ℝ) : Fin d → ℝ) =
      A j k := by
    simp [s5Bil, Pi.single_apply]
  rw [e, s5Nrm_single, s5Nrm_single] at h1
  simpa using h1

theorem s5_integrable_coef {c : Vec d → ℂ} (hc : Measurable c) {K : ℝ}
    (hK : ∀ x, ‖c x‖ ≤ K) (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    Integrable (fun x => c x * u x * v x) volume := by
  have hcu : MemLp (fun x => c x * u x) 2 volume :=
    (Lp.memLp u).of_le_mul (c := K)
      (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))
  exact hcu.integrable_mul (Lp.memLp v)

/-- Pointwise forward inequality for the actual weak-form integrand. -/
theorem s5_pt_forward {A : Fin d → Fin d → ℝ} {Λ : ℝ} (h : S5Elliptic A Λ)
    (X : Fin d → ℂ) (u : ℂ) (D : Fin d → ℝ) (ρ q : ℝ) (i : Fin d) (ζ : ℂ)
    (hρ : 0 ≤ ρ) (hD : s5Nrm D ≤ 2 * q * ρ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) +
      ζ * ((∑ j, (A j i : ℂ) * X j) * ((ρ : ℂ) * (starRingEnd ℂ) u))).re ≤
    (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hsplit : (∑ j, ∑ k, (A j k : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) =
      (ρ : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)) +
        (starRingEnd ℂ) u * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, ← mul_assoc (∑ j, (A j i : ℂ) * X j)]
  have hm : ∑ j, ‖X j‖ ^ 2 = s5CNrm X ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
  have h1 : Λ⁻¹ * s5CNrm X ^ 2 ≤
      (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)).re := by
    rw [← hm]
    exact s5_coercive h X
  exact s5_alg_forward h.one_le hρ (s5CNrm_nonneg X) hD _ _ _ u ζ h1
    (s5_cbil_norm_le h D X) (s5_row_norm_le h i X)

/-- Pointwise transpose inequality for the actual weak-form integrand. -/
theorem s5_pt_transpose {A : Fin d → Fin d → ℝ} {Λ : ℝ} (h : S5Elliptic A Λ)
    (X : Fin d → ℂ) (u : ℂ) (D : Fin d → ℝ) (ρ q : ℝ) (i : Fin d) (ζ : ℂ)
    (hρ : 0 ≤ ρ) (hD : s5Nrm D ≤ 2 * q * ρ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A k j : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) +
      ζ * (u * ∑ j, (A j i : ℂ) *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ)))).re ≤
    (5 * Λ ^ 3 * (q ^ 2 + ‖ζ‖ ^ 2)) * (ρ * ‖u‖ ^ 2) := by
  have hs : ∀ j k, (A k j : ℂ) = (A j k : ℂ) := fun j k => by rw [h.symm k j]
  have hsplit : (∑ j, ∑ k, (A k j : ℂ) * X k *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) =
      (ρ : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)) +
        (starRingEnd ℂ) u * (∑ j, ∑ k, (D j : ℂ) * (A j k : ℂ) * X k) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs j k]; ring
  have hsplit2 : (∑ j, (A j i : ℂ) *
        ((ρ : ℂ) * (starRingEnd ℂ) (X j) + (starRingEnd ℂ) u * (D j : ℂ))) =
      (ρ : ℂ) * (∑ j, (A j i : ℂ) * (starRingEnd ℂ) (X j)) +
        (starRingEnd ℂ) u * (∑ j, (D j : ℂ) * (A j i : ℂ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hsplit2]
  have hm : ∑ j, ‖X j‖ ^ 2 = s5CNrm X ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)).symm
  have h1 : Λ⁻¹ * s5CNrm X ^ 2 ≤
      (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)).re := by
    rw [← hm]
    exact s5_coercive h X
  have h4 : ‖∑ j, (A j i : ℂ) * (starRingEnd ℂ) (X j)‖ ≤ 2 * Λ * s5CNrm X := by
    have := s5_row_norm_le h i (fun j => (starRingEnd ℂ) (X j))
    rwa [s5CNrm_conj] at this
  have h5 : ‖∑ j, (D j : ℂ) * (A j i : ℂ)‖ ≤ Λ * s5Nrm D := by
    have e : (∑ j, (D j : ℂ) * (A j i : ℂ)) = ((∑ j, D j * A j i : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact s5_row_real_le h i D
  exact s5_alg_transpose h.one_le hρ (s5CNrm_nonneg X) hD _ _ _ _ u ζ h1
    (s5_cbil_norm_le h D X) h4 h5

/-- Bounding the real part of an integral by a pointwise bound against `κ ‖M f‖²`. -/
theorem s5_re_integral_le {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (T : Vec d → ℂ) (κ : ℝ)
    (hT : Integrable T volume)
    (hb : ∀ᵐ x ∂volume, (T x).re ≤ κ *
      ‖(s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f : Lp ℂ 2 volume) x‖ ^ 2) :
    (∫ x, T x).re ≤ κ * ‖s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f‖ ^ 2 := by
  set F := s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f with hF
  have h1 : (∫ x, T x).re = ∫ x, (T x).re := by
    have := Complex.reCLM.integral_comp_comm hT
    simp only [Complex.reCLM_apply] at this
    exact this.symm
  have hFi : Integrable (fun x => ‖(F : Vec d → ℂ) x‖ ^ 2) volume :=
    (Lp.memLp F).norm.integrable_sq
  have h2 : (∫ x, (T x).re) ≤ ∫ x, κ * ‖(F : Vec d → ℂ) x‖ ^ 2 :=
    integral_mono_ae (hT.re) (hFi.const_mul κ) hb
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [integral_const_mul, ← physicalL2_norm_sq]

/-- Identification of the weighted inner product with the weak-form pairing. -/
theorem s5_inner_eq {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (f g w : Lp ℂ 2 (volume : Measure (Vec d)))
    (hw : (w : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((φ x * φ x : ℝ) : ℂ) * (starRingEnd ℂ) (f x)) :
    inner ℂ (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f)
        (s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound g) = ∫ x, g x * w x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound f,
    s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound g, hw] with x h1 h2 h3
  rw [RCLike.inner_apply, h1, h2, h3]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem s5_norm_sq_pt {φ : Vec d → ℝ} {B q : ℝ} (hφ : S5Weight φ B q)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∀ᵐ x ∂volume, ‖(s5Mul volume hφ.measurable hφ.B_nonneg hφ.bound f :
        Lp ℂ 2 volume) x‖ ^ 2 = (φ x * φ x) * ‖f x‖ ^ 2 := by
  filter_upwards [s5Mul_coe volume hφ.measurable hφ.B_nonneg hφ.bound f] with x h1
  rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end S5Energy

end EinsteinFull
