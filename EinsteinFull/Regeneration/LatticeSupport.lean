import EinsteinFull.Frozen.RegenerationConditionedLawProbability
import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.LatticeConvolutionPower
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import EinsteinRelation.Regeneration.TrialBounds

open MeasureTheory
open scoped BigOperators NNReal ENNReal

/-! Elementary support facts for the actual regeneration lattice distribution.
The first lemma uses only the pathwise lower bound in the trial recursion;
the convolution lemmas apply to every sequence with zero mass at zero. -/

namespace EinsteinFull

open EinsteinRelation

theorem regenerationLatticeMass_zero {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (h₀ : 0 < lam) (hl : 0 < l)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) :
    regenerationLatticeMass hd Q lam l K hK hD 0 = 0 := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have ht (z : Regeneration.CoupledSample d) :
      (0 : ℝ≥0∞) < regenerationTime hd lam l 1 z := by
    have h := Regeneration.nat_two_step_le_regenerationTime
      (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) h₀ (div_pos hl h₀)
      z (Regeneration.Renewal.forceCoord hd) 1
    have htwo : (0 : ℝ≥0∞) < 2 := by norm_num
    have hp : (0 : ℝ≥0∞) < 2 * (Regeneration.Renewal.regenDelta lam : ℝ≥0∞) :=
      ENNReal.mul_pos_iff.mpr ⟨htwo, ENNReal.coe_pos.mpr hΔ⟩
    exact lt_of_lt_of_le (by simpa using hp) h
  unfold regenerationLatticeMass
  simp only [Nat.cast_zero]
  have he : {ωz : FieldPair d × Regeneration.CoupledSample d |
      regenerationTime hd lam l 1 ωz.2 =
        (((0 : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = ∅ := by
    ext ωz
    simp only [zero_mul, ENNReal.coe_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    exact ne_of_gt (ht ωz.2)
  rw [he]
  simp

theorem convolutionPower_eq_zero (p : ℕ → ℝ) (hp : p 0 = 0) (j : ℕ) :
    ∀ n : ℕ, n < j → latticeConvolutionPower p j n = 0 := by
  induction j with
  | zero => intro n hn; omega
  | succ j ih =>
    intro n hn
    rw [latticeConvolutionPower]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    by_cases hk0 : k = 0
    · simp only [hk0, hp, zero_mul]
    · rw [ih (n - k) (by omega), mul_zero]

theorem tsum_convolutionPower (p : ℕ → ℝ) (hp : p 0 = 0) (n : ℕ) :
    (∑' j : ℕ, latticeConvolutionPower p j n) =
      ∑ j ∈ Finset.range (n + 1), latticeConvolutionPower p j n := by
  apply tsum_eq_sum
  intro j hj
  apply convolutionPower_eq_zero p hp j n
  have hj' : ¬j < n + 1 := by simpa only [Finset.mem_range] using hj
  omega

end EinsteinFull
