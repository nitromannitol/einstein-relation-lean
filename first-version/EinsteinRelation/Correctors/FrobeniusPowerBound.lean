import EinsteinRelation.Environment.MatrixNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.MeanInequalities

/-! Entrywise assembly of the flux moment in `paper/main.tex:714-716`. -/
namespace EinsteinRelation.Correctors

/-- The tensor moment reduces to finitely many scalar entry moments. -/
theorem frobeniusNorm_rpow_le_sum {d : ℕ} (hd : 0 < d)
    (A : Mat d) (m : ℝ) (hm : 2 ≤ m) :
    frobeniusNorm A ^ m ≤ (d : ℝ) ^ (m - 2) *
      ∑ j : Fin d, ∑ k : Fin d, |A j k| ^ m := by
  have hm_div_two : 1 ≤ m / 2 := by linarith
  have h_sq_nonneg : 0 ≤ frobeniusSq A := frobeniusSq_nonneg A
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact mod_cast hd.le
  rw [frobeniusNorm, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul h_sq_nonneg (1 / 2 : ℝ) m]
  have h_exp : (1 / 2 : ℝ) * m = m / 2 := by ring
  rw [h_exp]
  rw [frobeniusSq]
  -- (∑ i, ∑ j, A i j * A i j) ^ (m / 2) ≤ ...
  -- Flatten the double sum: ∑ i, ∑ j, f i j = ∑ p : Fin d × Fin d, f p.1 p.2
  rw [← Finset.sum_product']
  -- (∑ p : Fin d × Fin d, (A p.1 p.2) * (A p.1 p.2)) ^ (m / 2)
  simp_rw [← pow_two]
  -- Apply the power mean inequality
  refine (Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
    (f := fun (p : Fin d × Fin d) => (A p.1 p.2) ^ 2) hm_div_two (fun i _ => pow_two_nonneg _)).trans ?_
  -- Now: (#s : ℝ) ^ (m/2 - 1) * ∑ p, ((A p.1 p.2)^2)^(m/2) ≤ (d : ℝ)^(m-2) * ∑ j, ∑ k, |A j k|^m
  -- Compute the cardinality
  have h_card : (Finset.card (Finset.univ : Finset (Fin d × Fin d)) : ℝ) = (d : ℝ) * (d : ℝ) := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [h_card]
  -- ((d : ℝ) * (d : ℝ)) ^ (m/2 - 1) * ∑ p, ((A p.1 p.2)^2)^(m/2)
  -- Show: ((d : ℝ) * (d : ℝ)) ^ (m/2 - 1) = (d : ℝ) ^ (m - 2)
  have h_pow : ((d : ℝ) * (d : ℝ)) ^ (m / 2 - 1) = (d : ℝ) ^ (m - 2) := by
    calc
      ((d : ℝ) * (d : ℝ)) ^ (m / 2 - 1) = ((d : ℝ) ^ 2) ^ (m / 2 - 1) := by simp [sq]
      _ = ((d : ℝ) ^ (2 : ℝ)) ^ (m / 2 - 1) := by norm_num
      _ = (d : ℝ) ^ ((2 : ℝ) * (m / 2 - 1)) := by rw [← Real.rpow_mul hd_nonneg (2 : ℝ) (m / 2 - 1)]
      _ = (d : ℝ) ^ (m - 2) := by ring
  rw [h_pow]
  -- Now: (d : ℝ)^(m-2) * ∑ p, ((A p.1 p.2)^2)^(m/2) ≤ (d : ℝ)^(m-2) * ∑ j, ∑ k, |A j k|^m
  -- It suffices to show: ∑ p, ((A p.1 p.2)^2)^(m/2) ≤ ∑ j, ∑ k, |A j k|^m
  -- Flatten the RHS double sum
  rw [← Finset.sum_product']
  -- ∑ p, ((A p.1 p.2)^2)^(m/2) ≤ ∑ p, |A p.1 p.2|^m
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _ => ?_)) (by
    -- (d : ℝ)^(m-2) ≥ 0 because d ≥ 0 and exponent m-2 is real
    exact Real.rpow_nonneg hd_nonneg _)
  -- Show: ((A p.1 p.2)^2)^(m/2) ≤ |A p.1 p.2|^m
  have h_entry_eq : ((A p.1 p.2) ^ 2) ^ (m / 2) = |A p.1 p.2| ^ m := by
    calc
      ((A p.1 p.2) ^ 2) ^ (m / 2) = (|A p.1 p.2| ^ 2) ^ (m / 2) := by simp [sq_abs]
      _ = (|A p.1 p.2| ^ (2 : ℝ)) ^ (m / 2) := by norm_num
      _ = |A p.1 p.2| ^ ((2 : ℝ) * (m / 2)) := by
        rw [← Real.rpow_mul (abs_nonneg _) (2 : ℝ) (m / 2)]
      _ = |A p.1 p.2| ^ m := by ring
  exact le_of_eq h_entry_eq

end EinsteinRelation.Correctors
