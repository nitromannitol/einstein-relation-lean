import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds_u23_derivatives
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma cutoff_norm_le_euclidean {d : ℕ} (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
  exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    (fun i => Regeneration.coordinate_abs_le_euclideanNorm v i)

/-- A single reference bump, with every derivative bounded before any spatial
center or scale is selected. The plateau includes the closed Euclidean ball. -/
theorem exists_cutoff_reference (d : ℕ) :
    ∃ (ψ : Vec d → ℝ) (K : ℕ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ k, 0 < K k) ∧
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ x, euclideanNorm x ≤ 1 → ψ x = 1) ∧
      (∀ x, 2 ≤ euclideanNorm x → ψ x = 0) ∧
      ∀ k x, ‖iteratedFDeriv ℝ k ψ x‖ ≤ K k := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨1, 3 / 2, by norm_num, by norm_num⟩
  let ψ : Vec d → ℝ := b ∘ J
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := b.contDiff.comp J.contDiff
  have hc : HasCompactSupport ψ := b.hasCompactSupport.comp_homeomorph J.toHomeomorph
  have hb (k : ℕ) : ∃ N : ℝ, ∀ x, ‖iteratedFDeriv ℝ k ψ x‖ ≤ N :=
    (hc.iteratedFDeriv k).exists_bound_of_continuous
      (hs.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  choose N hN using hb
  refine ⟨ψ, fun k => max (N k) 0 + 1, hs, fun k => by positivity,
    fun x => ⟨b.nonneg, b.le_one⟩, ?_, ?_, fun k x => (hN k x).trans ?_⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, J,
      PiLp.continuousLinearEquiv_symm_apply, ← TimeChange.euclideanNorm_eq_norm_toLp] using hx
  · intro x hx
    apply b.zero_of_le_dist
    have h : (3 / 2 : ℝ) ≤ euclideanNorm x := by linarith
    simpa only [dist_eq_norm, sub_zero, J,
      PiLp.continuousLinearEquiv_symm_apply, ← TimeChange.euclideanNorm_eq_norm_toLp] using h
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)

/-- The literal translated, rescaled bump has the exact inverse-radius power
at every derivative order, measured on Euclidean directions. -/
theorem cutoff_rescaled_derivative_bound {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {K : ℕ → ℝ}
    (hK : ∀ k, 0 ≤ K k) (hb : ∀ k x, ‖iteratedFDeriv ℝ k ψ x‖ ≤ K k)
    (z : Vec d) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) (x : Vec d)
    (v : Fin k → Vec d) :
    |iteratedFDeriv ℝ k (fun y => ψ (ρ⁻¹ • (y - z))) x v| ≤
      K k * ρ ^ (-(k : ℤ)) * ∏ j, euclideanNorm (v j) := by
  let L : Vec d →L[ℝ] Vec d := ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec d)
  have he : iteratedFDeriv ℝ k (fun y => ψ (ρ⁻¹ • (y - z))) x v =
      iteratedFDeriv ℝ k ψ (ρ⁻¹ • (x - z)) (fun j => ρ⁻¹ • v j) := by
    change iteratedFDeriv ℝ k (fun y => (ψ ∘ L) (y - z)) x v = _
    rw [iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hψ (x - z)
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
    rfl
  rw [he]
  calc
    |iteratedFDeriv ℝ k ψ (ρ⁻¹ • (x - z)) (fun j => ρ⁻¹ • v j)| ≤
        K k * ∏ j, ‖ρ⁻¹ • v j‖ :=
      ((iteratedFDeriv ℝ k ψ _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb k _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    _ ≤ K k * ∏ j, (ρ⁻¹ * euclideanNorm (v j)) := by
      apply mul_le_mul_of_nonneg_left _ (hK k)
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
      exact mul_le_mul_of_nonneg_left (cutoff_norm_le_euclidean _) (inv_nonneg.mpr hρ.le)
    _ = K k * ρ ^ (-(k : ℤ)) * ∏ j, euclideanNorm (v j) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        zpow_neg, zpow_natCast, inv_pow, mul_assoc]

/-- The deterministic cutoff family required by the cutoff-environment node,
including its uniform all-order Euclidean derivative estimates. -/
theorem exists_cutoff_family (d : ℕ) :
    ∃ (K : ℕ → ℝ) (χ : Vec d → ℝ → Vec d → ℝ),
      (∀ k, 0 < K k) ∧ ∀ z ρ, 1 ≤ ρ →
        ContDiff ℝ (⊤ : ℕ∞) (χ z ρ) ∧
        (∀ x, 0 ≤ χ z ρ x ∧ χ z ρ x ≤ 1) ∧
        (∀ x, euclideanNorm (x - z) ≤ ρ → χ z ρ x = 1) ∧
        (∀ x, 2 * ρ ≤ euclideanNorm (x - z) → χ z ρ x = 0) ∧
        ∀ k : ℕ, 1 ≤ k → ∀ x v,
          |iteratedFDeriv ℝ k (χ z ρ) x v| ≤
            K k * ρ ^ (-(k : ℤ)) * ∏ j, euclideanNorm (v j) := by
  obtain ⟨ψ, K, hs, hK, hb, h1, h0, hD⟩ := exists_cutoff_reference d
  refine ⟨K, fun z ρ x => ψ (ρ⁻¹ • (x - z)), hK, ?_⟩
  intro z ρ hρ
  have hp : 0 < ρ := zero_lt_one.trans_le hρ
  refine ⟨hs.comp (by fun_prop),
    fun x => hb _, ?_, ?_, fun k _ x v =>
      cutoff_rescaled_derivative_bound hs (fun k => (hK k).le) hD z hp k x v⟩
  · intro x hx
    apply h1
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hp)]
    exact (inv_mul_le_iff₀ hp).mpr (by simpa only [mul_one] using hx)
  · intro x hx
    apply h0
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hp)]
    exact (le_inv_mul_iff₀ hp).mpr (by simpa only [mul_comm] using hx)

private lemma euclidean_unit {d : ℕ} (j : Fin d) :
    euclideanNorm (unitVector j) = 1 := by
  change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private lemma matrix_unit_entry {d : ℕ} (A : Mat d) (j i : Fin d) :
    (A.mulVec (unitVector j)) i = A i j := by
  change dotProduct (fun k => A i k) (Pi.single j 1) = _
  rw [dotProduct_single, mul_one]

private lemma scalar_derivative_bound {d k : ℕ} {f : Vec d → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x v, |iteratedFDeriv ℝ k f x v| ≤ C * ∏ j, euclideanNorm (v j))
    (x : Vec d) : ‖iteratedFDeriv ℝ k f x‖ ≤ C * ((d : ℝ) + 1) ^ k := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖iteratedFDeriv ℝ k f x v‖ ≤ C * ∏ j, euclideanNorm (v j) := h x v
    _ ≤ C * ∏ j, (((d : ℝ) + 1) * ‖v j‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ =>
        euclideanNorm_le_dimension_mul_norm (v j))
    _ = (C * ((d : ℝ) + 1) ^ k) * ∏ j, ‖v j‖ := by
      rw [Finset.prod_mul_distrib]; simp [mul_assoc]

private lemma entry_derivative_bound {d k : ℕ} {ω : FieldPair d} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x v ξ, euclideanNorm (Matrix.mulVec (fun i j =>
      iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) ξ) ≤
        C * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ)
    (x : Vec d) (i j : Fin d) :
    ‖iteratedFDeriv ℝ k (fun y => ω.1 y i j) x‖ ≤ C * ((d : ℝ) + 1) ^ k := by
  apply scalar_derivative_bound hC
  intro x v
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) (unitVector j)) i
  have hb := h x v (unitVector j)
  rw [euclidean_unit, mul_one] at hb
  refine le_trans (le_of_eq ?_) (hc.trans hb)
  congr 1
  exact (matrix_unit_entry
    (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) j i).symm

private lemma euclidean_matrix_bound {d : ℕ} (A : Mat d) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) (ξ : Vec d) :
    euclideanNorm (A.mulVec ξ) ≤ ((d : ℝ) + 1) * (d * C) * euclideanNorm ξ := by
  apply (euclideanNorm_le_dimension_mul_norm _).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) (Real.sqrt_nonneg _)) |>.mpr
  intro i
  calc
    ‖(A.mulVec ξ) i‖ ≤ ∑ j, |A i j| * |ξ j| := by
      simpa only [Matrix.mulVec, dotProduct, Real.norm_eq_abs, abs_mul] using
        (norm_sum_le (s := Finset.univ) (f := fun j => A i j * ξ j))
    _ ≤ ∑ _ : Fin d, C * euclideanNorm ξ := Finset.sum_le_sum fun j _ =>
      mul_le_mul (hA i j) (Regeneration.coordinate_abs_le_euclideanNorm ξ j)
        (abs_nonneg _) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact (mul_assoc (d : ℝ) C (euclideanNorm ξ)).symm

private lemma multilinear_euclidean_bound {d k : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec d) ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hL : ‖L‖ ≤ C) (v : Fin k → Vec d) :
    |L v| ≤ C * ∏ j, euclideanNorm (v j) := by
  exact (L.le_opNorm v).trans (mul_le_mul hL
    (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => cutoff_norm_le_euclidean _))
    (Finset.prod_nonneg fun j _ => norm_nonneg _) hC)

private lemma derivative_const_le {d n : ℕ} {c : ℝ} (hc : |c| ≤ 1) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (fun _ : Vec d => c) x‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hc
  · rw [iteratedFDeriv_const_of_ne hn]
    norm_num

private lemma derivative_add_le {d n : ℕ} {f g : Vec d → ℝ} {A B : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hA : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ A)
    (hB : ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ B) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (fun y => f y + g y) x‖ ≤ A + B := by
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast
    (le_top : (n : ℕ∞) ≤ ⊤))) (hg.contDiffAt.of_le (by exact_mod_cast
    (le_top : (n : ℕ∞) ≤ ⊤)))]
  exact (norm_add_le _ _).trans (add_le_add (hA x) (hB x))

private lemma derivative_mul_le {d n : ℕ} {f g : Vec d → ℝ} {A B : ℕ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hA0 : ∀ i, 0 ≤ A i)
    (hA : ∀ i x, ‖iteratedFDeriv ℝ i f x‖ ≤ A i)
    (hB : ∀ i x, ‖iteratedFDeriv ℝ i g x‖ ≤ B i) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A j * B (n - j) := by
  apply (norm_iteratedFDeriv_mul_le hf hg x
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).trans
  exact Finset.sum_le_sum fun j _ => mul_le_mul
    (mul_le_mul_of_nonneg_left (hA j x) (Nat.cast_nonneg _))
    (hB (n - j) x) (norm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (hA0 j))

private def cutoffProductBound (H F : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * H j * F (n - j)) +
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (1 + H j)

private lemma cutoffProductBound_nonneg {H F : ℕ → ℝ}
    (hH : ∀ n, 0 ≤ H n) (hF : ∀ n, 0 ≤ F n) (n : ℕ) :
    0 ≤ cutoffProductBound H F n := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hH j)) (hF _)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg zero_le_one (hH j))

private lemma cutoff_scalar_derivative {d : ℕ} {χ f : Vec d → ℝ} {H F : ℕ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hH0 : ∀ n, 0 ≤ H n)
    (hH : ∀ n x, ‖iteratedFDeriv ℝ n χ x‖ ≤ H n)
    (hF : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ F n)
    {c : ℝ} (hc : |c| ≤ 1) (n : ℕ) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (fun y => χ y * f y + (1 - χ y) * c) x‖ ≤
      cutoffProductBound H F n := by
  have hsub : ∀ n x, ‖iteratedFDeriv ℝ n (fun y => 1 - χ y) x‖ ≤ 1 + H n := by
    intro n x
    have he : (fun y => 1 - χ y) = (fun y => 1 + (-1 : ℝ) • χ y) := by
      funext y; simp only [smul_eq_mul]; ring
    rw [he]
    refine derivative_add_le (f := fun _ => (1 : ℝ)) (g := fun y => (-1 : ℝ) • χ y)
      contDiff_const (by fun_prop) (fun x => derivative_const_le (by norm_num) x) ?_ x
    intro y
    rw [iteratedFDeriv_const_smul_apply' (hχ.contDiffAt.of_le (by exact_mod_cast
      (le_top : (n : ℕ∞) ≤ ⊤))), norm_smul]
    simpa only [Real.norm_eq_abs, abs_neg, abs_one, one_mul] using hH n y
  refine derivative_add_le (f := fun y => χ y * f y) (g := fun y => (1 - χ y) * c)
    (by fun_prop) (by fun_prop) ?_ ?_ x
  · exact fun y => derivative_mul_le hχ hf hH0 hH hF y
  · intro y
    simpa only [mul_one] using derivative_mul_le (f := fun y => 1 - χ y) (g := fun _ => c)
      (by fun_prop) contDiff_const (fun n => add_nonneg zero_le_one (hH0 n)) hsub
      (fun _ x => derivative_const_le hc x) (n := n) y

/-- The actual continuous coefficient/clock pair obtained by convex cutoff. -/
def cutoffFieldPair {d : ℕ} (ω : FieldPair d) (χ : Vec d → ℝ) (hχ : Continuous χ) :
    FieldPair d :=
  (⟨fun x => χ x • ω.1 x + (1 - χ x) • (1 : Mat d),
      (hχ.smul ω.1.continuous).add ((continuous_const.sub hχ).smul continuous_const)⟩,
   ⟨fun x => χ x * ω.2 x + (1 - χ x),
      (hχ.mul ω.2.continuous).add (continuous_const.sub hχ)⟩)

/-- Convex cutoff preserves the full anisotropic quadratic-form ellipticity
and both clock bounds with the original ellipticity constant. -/
theorem cutoffFieldPair_elliptic {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsElliptic Λ ω.1)
    (hμ : ∀ x, Λ⁻¹ ≤ ω.2 x ∧ ω.2 x ≤ Λ)
    {χ : Vec d → ℝ} (hc : Continuous χ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    IsElliptic Λ (cutoffFieldPair ω χ hc).1 ∧
      ∀ x, Λ⁻¹ ≤ (cutoffFieldPair ω χ hc).2 x ∧
        (cutoffFieldPair ω χ hc).2 x ≤ Λ := by
  have hi : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
  have hconv {t a b : ℝ} (ht : 0 ≤ t ∧ t ≤ 1)
      (ha : Λ⁻¹ * b ≤ a ∧ a ≤ Λ * b) (hb : 0 ≤ b) :
      Λ⁻¹ * b ≤ t * a + (1 - t) * b ∧
        t * a + (1 - t) * b ≤ Λ * b := by
    constructor
    · have h1 := mul_le_mul_of_nonneg_left ha.1 ht.1
      have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi hb)
        (sub_nonneg.mpr ht.2)
      nlinarith only [h1, h2]
    · have h1 := mul_le_mul_of_nonneg_left ha.2 ht.1
      have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΛ hb)
        (sub_nonneg.mpr ht.2)
      nlinarith only [h1, h2]
  constructor
  · intro x
    refine ⟨?_, fun ξ => ?_⟩
    · change (χ x • ω.1 x + (1 - χ x) • (1 : Mat d)).transpose = _
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
        (hω x).1, Matrix.transpose_one]
      rfl
    · have he : dot ξ ((cutoffFieldPair ω χ hc).1 x |>.mulVec ξ) =
          χ x * dot ξ ((ω.1 x).mulVec ξ) + (1 - χ x) * euclideanSq ξ := by
        change dot ξ ((χ x • ω.1 x + (1 - χ x) • (1 : Mat d)).mulVec ξ) = _
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        change dotProduct ξ (χ x • (ω.1 x).mulVec ξ + (1 - χ x) • ξ) = _
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
        rfl
      rw [he]
      exact hconv (hχ x) ((hω x).2 ξ) (by
        change 0 ≤ ∑ j, ξ j * ξ j
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg (ξ j))
  · intro x
    simpa only [cutoffFieldPair, ContinuousMap.coe_mk, mul_one] using
      hconv (hχ x) (by simpa only [mul_one] using hμ x) zero_le_one

private def cutoffInputBound (d : ℕ) (Λ : ℝ) (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then Λ else M k * ((d : ℝ) + 1) ^ k

private lemma cutoffInputBound_nonneg {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (hM : ∀ k, 1 ≤ k → 0 < M k) (k : ℕ) :
    0 ≤ cutoffInputBound d Λ M k := by
  unfold cutoffInputBound
  split_ifs with hk
  · exact zero_le_one.trans hΛ
  · exact mul_nonneg (hM k (by omega)).le (by positivity)

private lemma cutoff_input_derivatives {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (ω : FieldPair d) (he : IsElliptic Λ ω.1)
    (hm : ∀ x, Λ⁻¹ ≤ ω.2 x ∧ ω.2 x ≤ Λ) (hs : IsSmoothWithBounds M ω)
    (k : ℕ) (x : Vec d) :
    ‖iteratedFDeriv ℝ k (fun y => ω.2 y) x‖ ≤ cutoffInputBound d Λ M k ∧
    ∀ i j, ‖iteratedFDeriv ℝ k (fun y => ω.1 y i j) x‖ ≤ cutoffInputBound d Λ M k := by
  by_cases hk : k = 0
  · subst k
    simp only [cutoffInputBound, ite_true, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    refine ⟨?_, fun i j => ?_⟩
    · apply abs_le.mpr
      exact ⟨(by linarith [inv_nonneg.mpr (zero_le_one.trans hΛ), (hm x).1]), (hm x).2⟩
    · have hb := Correctors.isElliptic_mulVec_euclideanNorm_le
        (zero_lt_one.trans_le hΛ) he x (unitVector j)
      have hc := Regeneration.coordinate_abs_le_euclideanNorm ((ω.1 x).mulVec (unitVector j)) i
      rw [euclidean_unit, mul_one] at hb
      rw [matrix_unit_entry] at hc
      exact hc.trans hb
  · obtain ⟨A, B, hA, hB, hAB, ha, hb⟩ := hs.2 k (by omega)
    rw [cutoffInputBound, if_neg hk]
    constructor
    · exact (scalar_derivative_bound hB hb x).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · intro i j
      exact (entry_derivative_bound hA ha x i j).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

private lemma cutoff_smooth_bounds {d : ℕ} {Λ : ℝ} {M H : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (hM : ∀ k, 1 ≤ k → 0 < M k) (hH : ∀ k, 0 ≤ H k)
    (ω : FieldPair d) (he : IsElliptic Λ ω.1)
    (hm : ∀ x, Λ⁻¹ ≤ ω.2 x ∧ ω.2 x ≤ Λ) (hs : IsSmoothWithBounds M ω)
    {χ : Vec d → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hD : ∀ k x, ‖iteratedFDeriv ℝ k χ x‖ ≤ H k) :
    IsSmoothWithBounds (fun k =>
      (((d : ℝ) + 1) * d + 1) * cutoffProductBound H (cutoffInputBound d Λ M) k + 1)
      (cutoffFieldPair ω χ hc.continuous) := by
  let F := cutoffInputBound d Λ M
  let E := cutoffProductBound H F
  have hE (k : ℕ) : 0 ≤ E k :=
    cutoffProductBound_nonneg hH (cutoffInputBound_nonneg hΛ hM) k
  have hentry (i j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (cutoffFieldPair ω χ hc.continuous).1 y i j) := by
    have h1 := hs.1.1 i j
    show ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * ω.1 y i j + (1 - χ y) * (1 : Mat d) i j)
    fun_prop
  have hclock : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (cutoffFieldPair ω χ hc.continuous).2 y) := by
    have h1 := hs.1.2
    show ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * ω.2 y + (1 - χ y))
    fun_prop
  have hentryD (k : ℕ) (x : Vec d) (i j : Fin d) :
      ‖iteratedFDeriv ℝ k (fun y => (cutoffFieldPair ω χ hc.continuous).1 y i j) x‖ ≤ E k := by
    apply cutoff_scalar_derivative hc (hs.1.1 i j) hH hD
      (fun n y => (cutoff_input_derivatives hΛ ω he hm hs n y).2 i j)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hclockD (k : ℕ) (x : Vec d) :
      ‖iteratedFDeriv ℝ k (fun y => (cutoffFieldPair ω χ hc.continuous).2 y) x‖ ≤ E k := by
    have h := cutoff_scalar_derivative hc hs.1.2 hH hD
      (fun n y => (cutoff_input_derivatives hΛ ω he hm hs n y).1)
      (c := 1) (by norm_num) k x
    simp only [mul_one] at h
    exact h
  refine ⟨⟨hentry, hclock⟩, fun k _ =>
    ⟨((d : ℝ) + 1) * (d * E k), E k,
      mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hE k)), hE k, ?_, ?_, ?_⟩⟩
  · dsimp [E, F]
    nlinarith only []
  · intro x v ξ
    have hv : 0 ≤ ∏ j, euclideanNorm (v j) :=
      Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
    have hentryB (i j : Fin d) :
        |iteratedFDeriv ℝ k (fun y => (cutoffFieldPair ω χ hc.continuous).1 y i j) x v| ≤
          E k * ∏ j, euclideanNorm (v j) :=
      multilinear_euclidean_bound _ (hE k) (hentryD k x i j) v
    have h := euclidean_matrix_bound
      (fun i j => iteratedFDeriv ℝ k (fun y => (cutoffFieldPair ω χ hc.continuous).1 y i j) x v)
      (mul_nonneg (hE k) hv) hentryB ξ
    simpa only [mul_assoc] using h
  · intro x v
    exact multilinear_euclidean_bound _ (hE k) (hclockD k x) v

/-- Reduction of the cutoff-environment contract from exactly the reduced
ellipticity and reduced derivative contracts, in graph dependency order. -/
theorem node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment_of_deps
    (hbounds : node_eq_u2E_reduced_u2D_boundsStmt)
    (hderivatives : node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt) :
    node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt := by
  intro d D
  obtain ⟨Λ, A, B, hΛ, _hA, _hB, _hAB, hb⟩ := hbounds D.ellipticity D.one_le_ellipticity
  obtain ⟨M, hM, hd⟩ := hderivatives d D
  obtain ⟨K, χ, hK, hχ⟩ := exists_cutoff_family d
  let H : ℕ → ℝ := fun n => if n = 0 then 1 else K n * ((d : ℝ) + 1) ^ n
  have hH (n : ℕ) : 0 ≤ H n := by
    dsimp [H]
    split_ifs
    · exact zero_le_one
    · exact mul_nonneg (hK n).le (by positivity)
  let F := cutoffInputBound d Λ M
  let E := cutoffProductBound H F
  have hE (n : ℕ) : 0 ≤ E n :=
    cutoffProductBound_nonneg hH (cutoffInputBound_nonneg hΛ hM) n
  refine ⟨Λ, (fun n => (((d : ℝ) + 1) * d + 1) * E n + 1), K, hΛ,
    (fun n _ => ⟨by have := hE n; positivity, hK n⟩), χ, hχ, ?_⟩
  intro Q hQ
  filter_upwards [(hb d D.dependenceRange Q).2.2, hd Q hQ] with ω hω hs
  intro z ρ hρ
  obtain ⟨hc, hχb, h1, h0, hχD⟩ := hχ z ρ hρ
  refine ⟨cutoffFieldPair ω (χ z ρ) hc.continuous,
    fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change χ z ρ x • ω.1 x + (1 - χ z ρ x) • (1 : Mat d) = ω.1 x ∧
      χ z ρ x * ω.2 x + (1 - χ z ρ x) = ω.2 x
    rw [h1 x hx]
    simp only [sub_self, one_smul, zero_smul, add_zero, one_mul]
    trivial
  · intro x hx
    change χ z ρ x • ω.1 x + (1 - χ z ρ x) • (1 : Mat d) = (1 : Mat d) ∧
      χ z ρ x * ω.2 x + (1 - χ z ρ x) = 1
    rw [h0 x hx]
    simp only [sub_zero, zero_smul, one_smul, zero_add, zero_mul]
    trivial
  · exact (cutoffFieldPair_elliptic hΛ ω hω.1 hω.2.1 hc.continuous hχb).1
  · exact (cutoffFieldPair_elliptic hΛ ω hω.1 hω.2.1 hc.continuous hχb).2
  · apply cutoff_smooth_bounds hΛ hM hH ω hω.1 hω.2.1 hs hc
    intro n x
    by_cases hn : n = 0
    · subst n
      simp only [H, ite_true, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (abs_of_nonneg (hχb x).1).trans_le (hχb x).2
    · change ‖iteratedFDeriv ℝ n (χ z ρ) x‖ ≤ H n
      simp only [H, if_neg hn]
      apply scalar_derivative_bound (hK n).le _ x
      intro y v
      have hp : 0 ≤ ∏ j, euclideanNorm (v j) :=
        Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
      exact (hχD n (by omega) y v).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (hK n).le
            (zpow_le_one_of_nonpos₀ hρ (by omega))) hp)

end EinsteinFull.Blueprint
