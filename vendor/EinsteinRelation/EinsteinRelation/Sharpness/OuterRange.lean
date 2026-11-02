import EinsteinRelation.Sharpness.NoiseLocality
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Euclidean finite-range geometry for the outer neighborhoods of the two-stage
field `ζ * tanh(K * W)`, `paper/main.tex:1212–1216`.
This proves cross-test orthogonality of the first-stage kernel tests when the outer
points are separated in the Euclidean norm. It does not prove the full finite-range
property of `h`, independence of restricted fields, or local measurability. -/
open MeasureTheory
open EinsteinRelation.TimeChange

namespace EinsteinRelation.Sharpness

private theorem outer_euclideanNorm_neg {d : ℕ} (v : Vec d) :
    euclideanNorm (-v) = euclideanNorm v := by
  rw [← neg_one_smul ℝ v, euclideanNorm_smul]
  norm_num

/-- Outer-neighborhood orthogonality for `ζ * tanh(K * W)`. If the supports of `ζ`
and `K` lie in Euclidean radii `Rζ` and `RK`, and the outer points satisfy
`2 * (Rζ + RK) < euclideanNorm (x - z)`, then for every `y, w` in the support of `ζ`
the reflected kernel tests at `x - y` and `z - w` have zero L² inner product. -/
theorem integral_kernelTest_outer_mul_eq_zero_of_separated {d : ℕ}
    (ζ K : NoiseTest d) (Rζ RK : ℝ)
    (hζ : ∀ u : Vec d, ζ u ≠ 0 → euclideanNorm u ≤ Rζ)
    (hK : ∀ u : Vec d, K u ≠ 0 → euclideanNorm u ≤ RK)
    (x z : Vec d) (hsep : 2*(Rζ+RK) < euclideanNorm (x-z))
    (y w : Vec d) (hy : ζ y ≠ 0) (hw : ζ w ≠ 0) :
    (∫ u : Vec d, kernelTest K (x-y) u * kernelTest K (z-w) u) = 0 := by
  have hyR : euclideanNorm y ≤ Rζ := hζ y hy
  have hwR : euclideanNorm w ≤ Rζ := hζ w hw
  have hyw : euclideanNorm (y - w) ≤ euclideanNorm y + euclideanNorm w := by
    have h := euclideanNorm_add_le y (-w)
    rw [outer_euclideanNorm_neg, ← sub_eq_add_neg] at h
    exact h
  have hid : x - z = ((x - y) - (z - w)) + (y - w) := by abel
  have htri : euclideanNorm (x - z) ≤
      euclideanNorm ((x - y) - (z - w)) + euclideanNorm (y - w) := by
    rw [hid]
    exact euclideanNorm_add_le _ _
  have hsep' : 2 * RK < euclideanNorm ((x - y) - (z - w)) := by
    linarith
  have hae : (fun u : Vec d => kernelTest K (x - y) u * kernelTest K (z - w) u)
      =ᵐ[(volume : Measure (Vec d))] fun _ : Vec d => (0 : ℝ) :=
    ae_of_all volume fun u => kernelTest_mul_eq_zero_of_separated K RK hK (x - y) (z - w) hsep' u
  rw [integral_congr_ae hae, integral_zero]

end EinsteinRelation.Sharpness
