import EinsteinFull.Homogenization.SourceEnergyMeanConvergence
import EinsteinFull.Homogenization.SourceCoarseMatrixConvergence

/-!
# Mean convergence of the Dirichlet block

Polarization transfers mean convergence of the Dirichlet energy to the entries
of the coarse matrix, as in Proposition 1.7 of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Each entry of the finite-scale Dirichlet block converges in mean to the
corresponding entry of the limiting annealed matrix. -/
theorem tendsto_integral_abs_sourceCoarseMatrix_entry_sub_limit
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (i j : Fin d) :
    Tendsto (fun n : ℕ => ∫ a, |(Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).upperLeft i j -
      limitingAnnealedDirichletMatrix hK P hstat i j| ∂P) atTop (𝓝 0) := by
  let e₁ : Vec d := Pi.single i 1
  let e₂ : Vec d := Pi.single j 1
  let E := fun (n : ℕ) (e : Vec d) (a : Coefficient d K) => sourceDirichletEnergy a (sourceTriadicCube d n) e -
    ⨅ m : ℕ, ∫ b, sourceDirichletEnergy b (sourceTriadicCube d m) e ∂P
  let T := fun n e => ∫ a, |E n e a| ∂P
  have hT (e : Vec d) : Tendsto (fun n => T n e) atTop (𝓝 0) :=
    tendsto_integral_abs_sourceDirichletEnergy_sub_limit hK P hP hstat e
  have hlim := ((hT (e₁ + e₂)).add (hT e₁)).add (hT e₂)
  simp only [zero_add] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg fun _ => abs_nonneg _) ?_
  intro n
  have hE (e : Vec d) : Integrable (E n e) P :=
    (integrable_sourceDirichletEnergy hK P n e).sub (integrable_const _)
  have hmatrix : ∀ a, (Book.Ch02.coarseBlockMatrix
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk)).upperLeft i j -
      limitingAnnealedDirichletMatrix hK P hstat i j =
      E n (e₁ + e₂) a - E n e₁ a - E n e₂ a := by
    intro a
    rw [sourceCoarseMatrix_entry_eq_polar, limitingAnnealedDirichletMatrix_apply]
    dsimp only [E, e₁, e₂]
    ring
  simp_rw [hmatrix]
  change (∫ a, |E n (e₁ + e₂) a - E n e₁ a - E n e₂ a| ∂P) ≤ _
  calc
    _ ≤ ∫ a, (|E n (e₁ + e₂) a| + |E n e₁ a| + |E n e₂ a|) ∂P := by
      apply integral_mono (((hE (e₁ + e₂)).sub (hE e₁)).sub (hE e₂)).abs
        (((hE (e₁ + e₂)).abs.add (hE e₁).abs).add (hE e₂).abs)
      intro a
      change |E n (e₁ + e₂) a - E n e₁ a - E n e₂ a| ≤ _
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = T n (e₁ + e₂) + T n e₁ + T n e₂ := by
      have hs := integral_add ((hE (e₁ + e₂)).abs.add (hE e₁).abs) (hE e₂).abs
      change (∫ a, (|E n (e₁ + e₂) a| + |E n e₁ a|) + |E n e₂ a| ∂P) = _ at hs
      rw [hs]
      simp only [Pi.add_apply]
      have hs' := integral_add (hE (e₁ + e₂)).abs (hE e₁).abs
      change (∫ a, |E n (e₁ + e₂) a| + |E n e₁ a| ∂P) = _ at hs'
      rw [hs']

end EinsteinFull.Homogenization
