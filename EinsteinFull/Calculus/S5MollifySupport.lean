import EinsteinFull.Calculus.S5WeightGradSupport
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Smooth approximation of Euclidean-Lipschitz functions

A function `ψ` with `|ψ x - ψ y| ≤ |x - y|` (Euclidean) is uniformly approximated by smooth
functions with the same Lipschitz bound, hence with Euclidean gradient of norm at most one,
by convolution with a normalized smooth bump.
-/

open MeasureTheory Filter Topology
open scoped Convolution

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5Mollify

variable {d : ℕ}

theorem euclideanNorm_eq_s5Nrm (v : Vec d) : euclideanNorm v = s5Nrm v := by
  unfold euclideanNorm euclideanSq dot s5Nrm
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem s5_euclid_le_sqrt (t : Vec d) : euclideanNorm t ≤ Real.sqrt d * ‖t‖ := by
  rw [euclideanNorm_eq_s5Nrm]
  unfold s5Nrm
  have h1 : ∑ j, t j ^ 2 ≤ (d : ℝ) * ‖t‖ ^ 2 := by
    calc ∑ j, t j ^ 2 ≤ ∑ _j : Fin d, ‖t‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := norm_le_pi_norm t j
          rw [Real.norm_eq_abs] at this
          exact sq_le_sq' (by linarith [neg_abs_le (t j)]) (by linarith [le_abs_self (t j)])
      _ = (d : ℝ) * ‖t‖ ^ 2 := by simp
  calc Real.sqrt (∑ j, t j ^ 2) ≤ Real.sqrt ((d : ℝ) * ‖t‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt d * ‖t‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg t)]

/-- A differentiable Euclidean-`1`-Lipschitz function has Euclidean gradient of norm `≤ 1`. -/
theorem s5_grad_le_one {f : Vec d → ℝ} {x : Vec d} (hf : DifferentiableAt ℝ f x)
    (hL : ∀ y z, |f y - f z| ≤ euclideanNorm (y - z)) :
    s5Nrm (fun j => coordinateDerivative j f x) ≤ 1 := by
  set ξ : Vec d := fun j => coordinateDerivative j f x with hξ
  set D := fderiv ℝ f x with hD
  have hDξ : D ξ = ∑ j, ξ j * ξ j := by
    have h1 := LinearMap.pi_apply_eq_sum_univ D.toLinearMap ξ
    have h2 : ∀ j, D.toLinearMap (fun k => if j = k then (1 : ℝ) else 0) = ξ j := by
      intro j
      have e : (fun k : Fin d => if j = k then (1 : ℝ) else 0) = unitVector j := by
        funext k
        simp [unitVector, Pi.single_apply, eq_comm]
      rw [e]
      rfl
    simp only [h2, smul_eq_mul] at h1
    exact h1
  have hline : HasDerivAt (fun h : ℝ => f (x + h • ξ)) (D ξ) 0 := by
    have h1 : HasDerivAt (fun h : ℝ => x + h • ξ) ξ 0 :=
      (((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add x).congr_deriv (one_smul ℝ ξ)
    have e : x + (0 : ℝ) • ξ = x := by simp
    have h2 : HasFDerivAt f D (x + (0 : ℝ) • ξ) := by
      rw [e]
      exact hf.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hlip : ∀ᶠ h in 𝓝 (0 : ℝ), ‖f (x + h • ξ) - f (x + (0 : ℝ) • ξ)‖ ≤
      s5Nrm ξ * ‖h - 0‖ := by
    refine Filter.Eventually.of_forall fun h => ?_
    have h3 := hL (x + h • ξ) (x + (0 : ℝ) • ξ)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero]
    have e : (x + h • ξ) - (x + (0 : ℝ) • ξ) = fun j => h * ξ j := by
      funext j
      simp
    rw [e, euclideanNorm_eq_s5Nrm, s5Nrm_smul] at h3
    linarith
  have h4 := hline.le_of_lip' (s5Nrm_nonneg ξ) hlip
  rw [Real.norm_eq_abs] at h4
  have h5 : s5Nrm ξ ^ 2 = D ξ := by
    rw [s5Nrm_sq, hDξ]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h6 : D ξ ≤ s5Nrm ξ := (le_abs_self _).trans h4
  by_contra hlt
  push_neg at hlt
  nlinarith [s5Nrm_nonneg ξ]

theorem s5_exists_smooth_lipschitz (ψ : Vec d → ℝ)
    (hψ : ∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ' : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧
      (∀ x, s5Nrm (fun j => coordinateDerivative j ψ' x) ≤ 1) ∧ ∀ x, |ψ' x - ψ x| ≤ ε := by
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hψc : Continuous ψ := by
    have hl : LipschitzWith ⟨Real.sqrt d, hsd⟩ ψ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm]
      exact (hψ x y).trans (s5_euclid_le_sqrt _)
    exact hl.continuous
  set δ : ℝ := ε / (Real.sqrt d + 1) with hδ
  have hδpos : 0 < δ := div_pos hε (by linarith)
  let b : ContDiffBump (0 : Vec d) :=
    { rIn := δ / 2, rOut := δ, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let ρ : Vec d → ℝ := b.normed volume
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => b.nonneg_normed t
  have hρint : ∫ t, ρ t = 1 := b.integral_normed
  have hρi : Integrable ρ volume := b.integrable_normed
  let ψ' : Vec d → ℝ := fun x => ∫ t, ψ (x - t) * ρ t
  have hconv : ψ' = fun x => (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x := by
    funext x
    rw [convolution_lsmul_swap]
    simp only [smul_eq_mul, ψ']
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ' := by
    rw [hconv]
    exact b.hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hψc.locallyIntegrable b.contDiff_normed
  have hint1 : ∀ x, Integrable (fun t => ψ (x - t) * ρ t) volume := fun x =>
    ((hψc.comp (continuous_const.sub continuous_id)).mul b.continuous_normed).integrable_of_hasCompactSupport
      (b.hasCompactSupport_normed.mul_left (f := fun t => ψ (x - t)))
  have hlipψ : ∀ x y, |ψ' x - ψ' y| ≤ euclideanNorm (x - y) := by
    intro x y
    have e : ψ' x - ψ' y = ∫ t, (ψ (x - t) - ψ (y - t)) * ρ t := by
      simp only [ψ']
      rw [← integral_sub (hint1 x) (hint1 y)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    rw [e, ← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le (μ := volume)
      (f := fun t => (ψ (x - t) - ψ (y - t)) * ρ t)
      (g := fun t => euclideanNorm (x - y) * ρ t) (hρi.const_mul _)
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [sub_sub_sub_cancel_right] using hψ (x - t) (y - t)) (hρ0 t))
    rw [integral_const_mul, hρint, mul_one] at h
    exact h
  refine ⟨ψ', hsmooth, fun x => ?_, fun x => ?_⟩
  · exact s5_grad_le_one ((hsmooth.differentiable (by simp)).differentiableAt) hlipψ
  · have e : ψ' x - ψ x = ∫ t, (ψ (x - t) - ψ x) * ρ t := by
      have e1 : ψ x = ∫ t, ψ x * ρ t := by rw [integral_const_mul, hρint, mul_one]
      conv_lhs => rw [e1]
      simp only [ψ']
      rw [← integral_sub (hint1 x) (hρi.const_mul (ψ x))]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
    rw [e, ← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le (μ := volume)
      (f := fun t => (ψ (x - t) - ψ x) * ρ t)
      (g := fun t => ε * ρ t) (hρi.const_mul _)
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
        by_cases ht : ρ t = 0
        · rw [ht]
          simp
        · have hmem : t ∈ Function.support (b.normed (volume : Measure (Vec d))) := ht
          rw [b.support_normed_eq] at hmem
          have hn : ‖t‖ < δ := by
            have := mem_ball_zero_iff.mp hmem
            exact this
          have h1 : |ψ (x - t) - ψ x| ≤ ε := by
            rw [abs_sub_comm]
            refine (hψ x (x - t)).trans ?_
            rw [sub_sub_cancel]
            refine (s5_euclid_le_sqrt t).trans ?_
            have h2 : Real.sqrt d * ‖t‖ ≤ Real.sqrt d * δ :=
              mul_le_mul_of_nonneg_left hn.le hsd
            refine h2.trans ?_
            rw [hδ, ← mul_div_assoc, div_le_iff₀ (by linarith)]
            nlinarith
          exact mul_le_mul_of_nonneg_right h1 (hρ0 t))
    rw [integral_const_mul, hρint, mul_one] at h
    exact h

end S5Mollify

end EinsteinFull
