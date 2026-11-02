import EinsteinRelation.Sharpness.SeedFieldDerivatives
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-! # Common deterministic jet bound for the canonical seed

Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218. The seed
`seedField d W` has deterministic bounds on all its derivatives. For each order `0`, `1`, `2`, `3`
and each choice of coordinates, `exists_uniform_seedField_derivative_bound` supplies one constant
that is uniform in the actual sample `W` and the point `x`. The coordinate index types are finite,
so these constants can be collected into one finite sum. The resulting constant `M ≥ 1` bounds the
seed and all of its first, second and third coordinate derivatives at once, for every `W` and `x`.

No probability, smoothness, or boundedness premise is added: the only input is the producer
`exists_uniform_seedField_derivative_bound`. This common constant feeds the density Lipschitz
constant built from the second and third jets.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Source: `paper/main.tex`, proof of Proposition 7.1, Step 1, lines 1212–1218. For every dimension
there is one deterministic constant `M ≥ 1`, chosen before the sample `W` and the point `x`, which
bounds the canonical seed, its first, second and third coordinate derivatives everywhere. The
constant is a finite sum of the constants of `exists_uniform_seedField_derivative_bound` over all
coordinate choices. -/
theorem exists_uniform_seedField_third_jet_bound :
    ∀ d : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |seedField d W x| ≤ M ∧
      (∀ i : Fin d, |coordinateDerivative i (seedField d W) x| ≤ M) ∧
      (∀ i j : Fin d, |coordinateDerivative i (coordinateDerivative j (seedField d W)) x| ≤ M) ∧
      ∀ i j k : Fin d, |coordinateDerivative i (coordinateDerivative j
        (coordinateDerivative k (seedField d W))) x| ≤ M := by
  intro d
  -- One deterministic bound for the seed itself, from the empty list of coordinates.
  obtain ⟨C0, hC0, hC0'⟩ := exists_uniform_seedField_derivative_bound d []
  -- One deterministic bound for each coordinate, each pair, and each triple of coordinates.
  have h1 : ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |coordinateDerivative i (seedField d W) x| ≤ C := fun i =>
    exists_uniform_seedField_derivative_bound d [i]
  have h2 : ∀ i j : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |coordinateDerivative i (coordinateDerivative j (seedField d W)) x| ≤ C := fun i j =>
    exists_uniform_seedField_derivative_bound d [i, j]
  have h3 : ∀ i j k : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |coordinateDerivative i (coordinateDerivative j
        (coordinateDerivative k (seedField d W))) x| ≤ C := fun i j k =>
    exists_uniform_seedField_derivative_bound d [i, j, k]
  choose C1 hC1nn hC1 using h1
  choose C2 hC2nn hC2 using h2
  choose C3 hC3nn hC3 using h3
  -- The finite sums of the nonnegative constants.
  have hS1 : 0 ≤ ∑ i, C1 i := Finset.sum_nonneg fun i _ => hC1nn i
  have hS2 : 0 ≤ ∑ i, ∑ j, C2 i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC2nn i j
  have hS3 : 0 ≤ ∑ i, ∑ j, ∑ k, C3 i j k :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => hC3nn i j k
  -- Each single constant is at most the corresponding finite sum.
  have hle1 : ∀ i, C1 i ≤ ∑ i', C1 i' := fun i =>
    Finset.single_le_sum (fun i' _ => hC1nn i') (Finset.mem_univ i)
  have hle2 : ∀ i j, C2 i j ≤ ∑ i', ∑ j', C2 i' j' := fun i j => by
    have hrow : C2 i j ≤ ∑ j', C2 i j' :=
      Finset.single_le_sum (fun j' _ => hC2nn i j') (Finset.mem_univ j)
    have hcol : ∑ j', C2 i j' ≤ ∑ i', ∑ j', C2 i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', C2 i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hC2nn i' j') (Finset.mem_univ i)
    exact hrow.trans hcol
  have hle3 : ∀ i j k, C3 i j k ≤ ∑ i', ∑ j', ∑ k', C3 i' j' k' := fun i j k => by
    have hk : C3 i j k ≤ ∑ k', C3 i j k' :=
      Finset.single_le_sum (fun k' _ => hC3nn i j k') (Finset.mem_univ k)
    have hj : ∑ k', C3 i j k' ≤ ∑ j', ∑ k', C3 i j' k' :=
      Finset.single_le_sum (f := fun j' => ∑ k', C3 i j' k')
        (fun j' _ => Finset.sum_nonneg fun k' _ => hC3nn i j' k') (Finset.mem_univ j)
    have hi : ∑ j', ∑ k', C3 i j' k' ≤ ∑ i', ∑ j', ∑ k', C3 i' j' k' :=
      Finset.single_le_sum (f := fun i' => ∑ j', ∑ k', C3 i' j' k')
        (fun i' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun k' _ => hC3nn i' j' k')
        (Finset.mem_univ i)
    exact hk.trans (hj.trans hi)
  refine ⟨1 + C0 + (∑ i, C1 i) + (∑ i, ∑ j, C2 i j) + (∑ i, ∑ j, ∑ k, C3 i j k), ?_, ?_⟩
  · linarith
  · intro W x
    refine ⟨?_, fun i => ?_, fun i j => ?_, fun i j k => ?_⟩
    · have h0 : |seedField d W x| ≤ C0 := hC0' W x
      linarith
    · linarith [hC1 i W x, hle1 i]
    · linarith [hC2 i j W x, hle2 i j]
    · linarith [hC3 i j k W x, hle3 i j k]

end EinsteinRelation.Sharpness
