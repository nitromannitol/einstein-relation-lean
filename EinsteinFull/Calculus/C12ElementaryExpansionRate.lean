import EinsteinFull.Blueprint.G4.Proofs.C8ElementaryRate
import EinsteinFull.Calculus.S4DivisionPure

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.TimeChange

private theorem elementaryRate_polynomial {d : ℕ} (b : Fin (d + 1) → Vec d)
    (lam : ℝ) :
    (∑ j : Fin (d + 1), lam ^ (j.val + 1) • b j) =
      lam • (b 0 + ∑ j : Fin d, lam ^ (j.val + 1) • b j.succ) := by
  rw [Fin.sum_univ_succ, smul_add, Finset.smul_sum]
  congr 1
  · simp only [Fin.val_zero, zero_add, pow_one]
  · apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, Fin.val_succ, pow_succ, mul_comm]

private theorem elementaryRate_tail {d : ℕ} (b : Fin (d + 1) → Vec d)
    {lam C : ℝ} (hsmall : |lam| ≤ 1)
    (hb : (∑ j, euclideanNorm (b j)) ≤ C) :
    euclideanNorm (∑ j : Fin d, lam ^ (j.val + 1) • b j.succ) ≤ C * |lam| := by
  have hsum : (∑ j : Fin d, euclideanNorm (b j.succ)) ≤ C := by
    rw [Fin.sum_univ_succ] at hb
    exact (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans hb
  calc
    euclideanNorm (∑ j : Fin d, lam ^ (j.val + 1) • b j.succ) ≤
        ∑ j : Fin d, euclideanNorm (lam ^ (j.val + 1) • b j.succ) :=
      euclideanNorm_sum_le _ _
    _ ≤ ∑ j : Fin d, |lam| * euclideanNorm (b j.succ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [euclideanNorm_smul, abs_pow]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using
          pow_le_pow_of_le_one (abs_nonneg lam) hsmall (Nat.le_add_left 1 j.val))
        (Real.sqrt_nonneg _)
    _ = |lam| * ∑ j : Fin d, euclideanNorm (b j.succ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ |lam| * C := mul_le_mul_of_nonneg_left hsum (abs_nonneg lam)
    _ = C * |lam| := mul_comm _ _

/-- Pure specialization of the vector expansion, before any choice of physical
velocities. Both signs of the force use the same coefficient bound. -/
theorem elementaryRate_of_vector_expansion {d : ℕ} (hd : 2 ≤ d)
    (b : Fin (d + 1) → Vec d) (c velocity : Vec d) {C lam : ℝ}
    (hC : 0 ≤ C) (hlam : 0 < |lam|) (hsmall : |lam| ≤ Real.exp (-1))
    (hcoeff : (∑ j, euclideanNorm (b j)) + euclideanNorm c ≤ C)
    (hrem : euclideanNorm (velocity - (∑ j, lam ^ (j.val + 1) • b j) -
        criticalVelocityTerm d lam (abs_pos.mp hlam) • c) ≤
      C * |lam| ^ (d + 1) * expansionModulus |lam| hlam hsmall) :
    euclideanNorm (lam⁻¹ • velocity - b 0) ≤ (4 * C) * |lam| := by
  have hn : lam ≠ 0 := abs_pos.mp hlam
  have hs1 : |lam| ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hb : (∑ j, euclideanNorm (b j)) ≤ C :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hcoeff
  have hc : euclideanNorm c ≤ C :=
    (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)).trans hcoeff
  let tail : Vec d := ∑ j : Fin d, lam ^ (j.val + 1) • b j.succ
  let err : Vec d := velocity - (∑ j, lam ^ (j.val + 1) • b j) -
    criticalVelocityTerm d lam hn • c
  have herr : euclideanNorm (lam⁻¹ • err) ≤ C * |lam| := by
    rw [euclideanNorm_smul, abs_inv]
    calc
      |lam|⁻¹ * euclideanNorm err ≤
          |lam|⁻¹ * (C * |lam| ^ (d + 1) * expansionModulus |lam| hlam hsmall) :=
        mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr hlam.le)
      _ ≤ |lam|⁻¹ * (C * |lam| ^ (d + 1) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (elementaryRate_modulus_le_one hlam hsmall)
            (mul_nonneg hC (pow_nonneg hlam.le _))) (inv_nonneg.mpr hlam.le)
      _ = C * |lam| ^ d := by rw [pow_succ]; field_simp
      _ ≤ C * |lam| := mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_of_le_one hlam.le hs1 (by omega : 1 ≤ d)) hC
  have htail : euclideanNorm tail ≤ C * |lam| := elementaryRate_tail b hs1 hb
  have hcrit : euclideanNorm (criticalKernelTerm d lam hn • c) ≤ 2 * C * |lam| := by
    rw [euclideanNorm_smul]
    calc
      |criticalKernelTerm d lam hn| * euclideanNorm c ≤ (2 * |lam|) * C :=
        mul_le_mul (elementaryRate_critical_bound hd hn hs1) hc (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) hlam.le)
      _ = 2 * C * |lam| := by ring
  have hid : lam⁻¹ • velocity - b 0 =
      (lam⁻¹ • err + tail) + criticalKernelTerm d lam hn • c := by
    dsimp only [err, tail]
    rw [elementaryRate_polynomial, criticalVelocityTerm,
      smul_sub, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul,
      smul_smul, inv_mul_cancel_left₀ hn]
    module
  rw [hid]
  exact (euclideanNorm_add_le _ _).trans
    ((add_le_add ((euclideanNorm_add_le _ _).trans (add_le_add herr htail)) hcrit).trans
      (le_of_eq (by ring)))

/-- Conditional algebraic consumer of the exact signed velocity-extension
interface assigned to c5. This does not discharge that physical input. -/
theorem elementary_rate_of_expansion_and_velocity_extension
    (hSignedPhysicalFamilyVelocityExtension :
      ∀ {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
        (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        HasSmoothBounds D Q → ∀ X : DiffusionFamily d,
        IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q X →
        ∀ (lam : ℝ), lam ≠ 0 → ∀ v : Vec d,
        HasQuenchedVelocity Q.measure (originLaw (X lam)) v →
        ∃ velocity : ℝ → Vec d, velocity lam = v ∧
          ∀ l : ℝ, l ≠ 0 → HasQuenchedVelocity Q.measure (originLaw (X l)) (velocity l))
    (h0 : node_t_u3A_expansionStmt) : node_t_u2E_main_u23_elementary_u2D_rateStmt := by
  intro d hd D
  obtain ⟨C, lamStar, hC, hstar, hstar1, hexp⟩ := h0 d hd D
  refine ⟨4 * C + 2, lamStar, by positivity, hstar, hstar1, ?_, ?_⟩
  · intro s hs hss
    exact (elementaryRate_log_bound hd hs
      (hss.trans (hstar1.trans (Real.exp_le_one_iff.mpr (by norm_num))))).trans
      (mul_le_mul_of_nonneg_right (by linarith) hs.le)
  · intro Q hQ X hX covariance hcov lam hlam hsmall v hv
    obtain ⟨velocity, hvelocity, hvel⟩ :=
      hSignedPhysicalFamilyVelocityExtension hd D Q hQ X hX lam (abs_pos.mp hlam) v hv
    obtain ⟨b, c, hcoeff, hfamily⟩ := hexp Q hQ
    obtain ⟨hb, hrem⟩ := hfamily X hX covariance hcov
    have hrate := elementaryRate_of_vector_expansion hd b c (velocity lam) hC hlam
      (hsmall.trans hstar1) hcoeff (hrem velocity hvel lam hlam hsmall)
    rw [hvelocity] at hrate
    have hb0 : b 0 = covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)) := by
      simpa only [Fin.mk_zero] using hb
    rw [hb0] at hrate
    exact hrate.trans (mul_le_mul_of_nonneg_right (by linarith) hlam.le)

end EinsteinFull.Blueprint
