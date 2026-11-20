import EinsteinFull.Homogenization.SourceOptimizerGradientContraction
import Homogenization.Geometry.TriadicPartition

/-!
# Separated triadic children

Opposite children of a triadic cube are separated by their side length. This
geometry is used in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Lemma 2.13.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation

/-- At every child scale at least three, a parent cube has two children whose
points are separated by at least two. -/
theorem exists_separated_childCubes {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (n : ℕ) (hscale : Q.scale = (n : ℤ) + 2) :
    ∃ R ∈ descendantsAtDepth Q 1, ∃ S ∈ descendantsAtDepth Q 1,
      ∀ x ∈ cubeSet R, ∀ y ∈ cubeSet S, 2 ≤ EinsteinRelation.euclideanNorm (x - y) := by
  let R : TriadicCube d := ⟨Q.scale - 1, fun i => 3 * Q.index i + ((0 : Fin 3) : ℤ) - 1⟩
  let S : TriadicCube d := ⟨Q.scale - 1, fun i => 3 * Q.index i + ((2 : Fin 3) : ℤ) - 1⟩
  have hR : R ∈ descendantsAtDepth Q 1 := by
    rw [descendantsAtDepth_one]
    exact Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, rfl⟩
  have hS : S ∈ descendantsAtDepth Q 1 := by
    rw [descendantsAtDepth_one]
    exact Finset.mem_image.mpr ⟨fun _ => 2, Finset.mem_univ _, rfl⟩
  refine ⟨R, hR, S, hS, ?_⟩
  intro x hx y hy
  let i : Fin d := ⟨0, NeZero.pos d⟩
  have hsc : Q.scale - 1 = ((n + 1 : ℕ) : ℤ) := by
    rw [hscale]
    push_cast
    omega
  have hfactor : cubeScaleFactor R = (3 : ℝ) ^ (n + 1) := by
    change (3 : ℝ) ^ (Q.scale - 1) = _
    rw [hsc, zpow_natCast]
  have hfactor' : cubeScaleFactor S = (3 : ℝ) ^ (n + 1) := by
    change (3 : ℝ) ^ (Q.scale - 1) = _
    rw [hsc, zpow_natCast]
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hL : (2 : ℝ) ≤ (3 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith
  have hx' := (hx i).2
  have hy' := (hy i).1
  rw [hfactor] at hx'
  rw [hfactor'] at hy'
  have hxy : (3 : ℝ) ^ (n + 1) ≤ y i - x i := by
    norm_num [R, S] at hx' hy'
    nlinarith
  have hcoord : |(x - y) i| ≤ EinsteinRelation.euclideanNorm (x - y) := by
    unfold EinsteinRelation.euclideanNorm
    refine Real.abs_le_sqrt ?_
    unfold EinsteinRelation.euclideanSq EinsteinRelation.dot
    rw [sq]
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg ((x - y) j)) (Finset.mem_univ i)
  have h := neg_le_abs ((x - y) i)
  simp only [Pi.sub_apply] at h hcoord
  linarith

end EinsteinFull.Homogenization
