import EinsteinFull.External.Draft.DFGWInvarianceV2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Covariance matrix of a square-integrable increment

A square-integrable vector has an integrable coordinate covariance matrix whose quadratic
form is the second moment of every scalar projection.
-/

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The matrix of second moments of a random vector. -/
noncomputable def secondMomentMatrix (P : Measure Ω) (Z : Ω → Vec d) : Mat d :=
  fun i j => ∫ ω, Z ω i * Z ω j ∂P

/-- Every entry of the second-moment matrix is defined by an integrable product. -/
theorem integrable_secondMoment_entry (P : Measure Ω) (Z : Ω → Vec d) (hZ : MemLp Z 2 P)
    (i j : Fin d) : Integrable (fun ω => Z ω i * Z ω j) P := by
  have hi : MemLp (fun ω => Z ω i) 2 P := (memLp_pi_iff.mp hZ) i
  have hj : MemLp (fun ω => Z ω j) 2 P := (memLp_pi_iff.mp hZ) j
  have h := hi.integrable_mul hj
  exact h.congr (ae_of_all P fun ω => by rfl)

/-- The second-moment matrix is symmetric. -/
theorem secondMomentMatrix_transpose (P : Measure Ω) (Z : Ω → Vec d) :
    (secondMomentMatrix P Z).transpose = secondMomentMatrix P Z := by
  ext i j
  simp only [secondMomentMatrix, Matrix.transpose_apply, mul_comm]

/-- The quadratic form of the second-moment matrix is the projected second moment. -/
theorem secondMomentMatrix_quadratic (P : Measure Ω) (Z : Ω → Vec d) (hZ : MemLp Z 2 P)
    (e : Vec d) : dot e ((secondMomentMatrix P Z).mulVec e) =
      ∫ ω, dot e (Z ω) ^ 2 ∂P := by
  have hint (i j : Fin d) : Integrable (fun ω => (e i * e j) * (Z ω i * Z ω j)) P :=
    (integrable_secondMoment_entry P Z hZ i j).const_mul _
  calc
    dot e ((secondMomentMatrix P Z).mulVec e) =
        ∑ i, ∑ j, (e i * e j) * ∫ ω, Z ω i * Z ω j ∂P := by
      simp only [dot, Matrix.mulVec, dotProduct, secondMomentMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, ∫ ω, (e i * e j) * (Z ω i * Z ω j) ∂P := by
      simp only [integral_const_mul]
    _ = ∫ ω, ∑ i, ∑ j, (e i * e j) * (Z ω i * Z ω j) ∂P := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact hint i j
      · intro i hi
        apply integrable_finsetSum
        intro j hj
        exact hint i j
    _ = ∫ ω, dot e (Z ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      simp only [dot, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Every scalar projection of the random vector has an integrable square. -/
theorem integrable_dot_sq (P : Measure Ω) (Z : Ω → Vec d) (hZ : MemLp Z 2 P)
    (e : Vec d) : Integrable (fun ω => dot e (Z ω) ^ 2) P := by
  have hdot : MemLp (fun ω => dot e (Z ω)) 2 P := by
    unfold dot
    apply memLp_finsetSum
    intro i hi
    exact ((memLp_pi_iff.mp hZ) i).const_mul (e i)
  have h := hdot.integrable_mul hdot
  exact h.congr (ae_of_all P fun ω => by simp only [Pi.mul_apply, pow_two])

/-- The quadratic form of the second-moment matrix is nonnegative. -/
theorem secondMomentMatrix_nonneg (P : Measure Ω) (Z : Ω → Vec d) (hZ : MemLp Z 2 P)
    (e : Vec d) : 0 ≤ dot e ((secondMomentMatrix P Z).mulVec e) := by
  rw [secondMomentMatrix_quadratic P Z hZ]
  exact integral_nonneg fun ω => sq_nonneg _

end EinsteinFull.External.DFGW
