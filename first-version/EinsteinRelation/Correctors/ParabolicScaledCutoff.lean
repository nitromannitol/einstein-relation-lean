import EinsteinRelation.Correctors.ParabolicReferenceCutoff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.ConstMulAction

/-! # Parabolic rescaling of the compact cylinder cutoff

Source: `paper/main.tex:798–806,832–840`. The time scale is the square
of the spatial scale. The derivative bound therefore costs exactly the
inverse square of the radius, with no assumption on a solution.
-/

namespace EinsteinRelation.Correctors
open External.AKM

private theorem norm_unitVector_le_one {d : ℕ} (j : Fin d) : ‖unitVector j‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  simp only [unitVector, Pi.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- A compact cutoff at the parabolic scale, with its actual derivative
bound and its inner-cylinder normalization. The constant precedes the radius.
Source: `paper/main.tex:798–806,832–840`. -/
theorem exists_parabolic_scaled_cutoff (d : ℕ) (K : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r →
      ∃ ζ : ℝ × Vec d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
        tsupport ζ ⊆ Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r) ∧
        (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧
        (∀ z ∈ Set.Icc (2*r^2) (3*r^2) ×ˢ originBall d r, ζ z = 1) ∧
        ∀ z, 2 * ζ z * fderiv ℝ ζ z (1, 0) +
          4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ B / r^2 := by
  obtain ⟨φ, M, hM, hφ, hφc, hφs, hφ01, hφ1, hD⟩ := exists_parabolic_reference_cutoff d
  refine ⟨2*M + 4*K^2*(d : ℝ)*M^2, by positivity, ?_⟩
  intro r hr
  let S : (ℝ × Vec d) →L[ℝ] (ℝ × Vec d) :=
    (((r^2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Vec d)).prod
      (r⁻¹ • ContinuousLinearMap.snd ℝ ℝ (Vec d)))
  let H : (ℝ × Vec d) ≃ₜ (ℝ × Vec d) :=
    (Homeomorph.smulOfNeZero (r^2)⁻¹ (inv_ne_zero (pow_ne_zero 2 hr.ne'))).prodCongr
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hHS : (H : (ℝ × Vec d) → (ℝ × Vec d)) = S := rfl
  let ζ : ℝ × Vec d → ℝ := φ ∘ S
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := hφ.comp S.contDiff
  have hζc : HasCompactSupport ζ := by
    simpa only [hHS] using hφc.comp_homeomorph H
  have hscale (z : ℝ × Vec d) : S z = ((r^2)⁻¹ * z.1, r⁻¹ • z.2) := rfl
  have hnorm (x : Vec d) : euclideanNorm (r⁻¹ • x) = euclideanNorm x / r := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    ring
  have hderiv (z v : ℝ × Vec d) :
      fderiv ℝ ζ z v = fderiv ℝ φ (S z) (S v) := by
    rw [show ζ = φ ∘ S from rfl,
      fderiv_comp z (hφ.differentiable (by norm_num)).differentiableAt S.differentiableAt,
      S.fderiv]
    rfl
  refine ⟨ζ, hζ, hζc, ?_, (fun z => hφ01 (S z)), ?_, ?_⟩
  · intro z hz
    have hsup : tsupport ζ = H ⁻¹' tsupport φ := by
      simpa only [hHS] using tsupport_comp_eq_preimage φ H
    have hz' := hφs ((Set.ext_iff.mp hsup z).mp hz)
    rw [hHS, hscale] at hz'
    refine ⟨?_, ?_⟩
    · constructor
      · have ht := (lt_inv_mul_iff₀ (sq_pos_of_pos hr)).mp hz'.1.1
        simpa only [one_mul, mul_one] using ht
      · have ht := (inv_mul_lt_iff₀ (sq_pos_of_pos hr)).mp hz'.1.2
        simpa only [mul_comm] using ht
    · change euclideanNorm z.2 < 2*r
      have hx : euclideanNorm (r⁻¹ • z.2) < 2 := hz'.2
      rw [hnorm] at hx
      exact (div_lt_iff₀ hr).mp hx
  · intro z hz
    apply hφ1
    rw [hscale]
    refine ⟨?_, ?_⟩
    · constructor
      · exact (le_inv_mul_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using hz.1.1)
      · exact (inv_mul_le_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using hz.1.2)
    · change euclideanNorm (r⁻¹ • z.2) < 1
      rw [hnorm, div_lt_one hr]
      exact hz.2
  · intro z
    have ht : |fderiv ℝ ζ z (1, 0)| ≤ M / r^2 := by
      rw [hderiv]
      have h := (fderiv ℝ φ (S z)).le_opNorm (S (1, 0))
      have hn : ‖S (1, 0)‖ = (r^2)⁻¹ := by
        simp only [hscale, mul_one, smul_zero, Prod.norm_def, norm_zero,
          Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr)),
          max_eq_left (inv_nonneg.mpr (sq_nonneg r))]
      rw [hn, Real.norm_eq_abs] at h
      exact h.trans (by simpa only [div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_right (hD (S z)) (inv_nonneg.mpr (sq_nonneg r))))
    have hx (j : Fin d) : |fderiv ℝ ζ z (0, unitVector j)| ≤ M/r := by
      rw [hderiv]
      have h := (fderiv ℝ φ (S z)).le_opNorm (S (0, unitVector j))
      have hn : ‖S (0, unitVector j)‖ ≤ r⁻¹ := by
        simp only [hscale, mul_zero, Prod.norm_def, norm_zero, norm_smul,
          Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        exact max_le (inv_nonneg.mpr hr.le) (by simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (norm_unitVector_le_one j) (inv_nonneg.mpr hr.le)))
      exact (show |fderiv ℝ φ (S z) (S (0, unitVector j))| ≤ _ from h).trans
        (by simpa only [div_eq_mul_inv] using
          mul_le_mul (hD (S z)) hn (norm_nonneg _) hM.le)
    have hxs : euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ (d : ℝ)*(M/r)^2 := by
      unfold euclideanSq dot
      calc
        _ ≤ ∑ j : Fin d, (M/r)^2 := Finset.sum_le_sum fun j _ => by
          have hj := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hM.le hr.le)).mpr (hx j)
          rw [sq_abs] at hj
          simpa only [pow_two] using hj
        _ = _ := by simp
    have htime : 2*ζ z*fderiv ℝ ζ z (1,0) ≤ 2*(M/r^2) := by
      have hζ01 := hφ01 (S z)
      calc
        _ ≤ 2*ζ z*|fderiv ℝ ζ z (1,0)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg zero_le_two hζ01.1)
        _ ≤ 2*1*(M/r^2) := mul_le_mul
          (mul_le_mul_of_nonneg_left hζ01.2 zero_le_two) ht (abs_nonneg _)
          (by norm_num)
        _ = _ := by ring
    calc
      _ ≤ 2*(M/r^2) + 4*K^2*((d : ℝ)*(M/r)^2) :=
        add_le_add htime (mul_le_mul_of_nonneg_left hxs (by positivity))
      _ = _ := by field_simp

end EinsteinRelation.Correctors
