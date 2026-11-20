import EinsteinFull.Homogenization.SourceGradientMeanConvergence

/-!
# Response gap and mean optimizer gradient

The response decrement estimate of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*,
equation (2.44), also controls the deviation of the mean optimizer gradient
from its limit by the remaining expected response gap.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The remaining expected response gap controls the mean optimizer gradient
relative to its limiting value, for any fixed pair of loadings. -/
theorem exists_tendsto_integral_sourceGradient_with_response_gap
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (i : Fin d) :
    let F := fun (r : ℕ) (a : Coefficient d K) => Book.Ch02.averageGradient
      (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
          (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk)) p q).toSolution i
    let J := fun (r : ℕ) (a : Coefficient d K) => Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (r : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (r : ℤ))) k hk) p q
    let R := (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (-p) ∂P) +
      (⨅ n : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) - vecDot p q
    (∀ r, Integrable (F r) P ∧ Integrable (J r) P) ∧
    ∃ L : ℝ, Tendsto (fun r => ∫ a, F r a ∂P) atTop (𝓝 L) ∧
      ∀ m, (L - ∫ a, F m a ∂P) ^ 2 ≤
        (4 * d) * ((∫ a, J m a ∂P) - R) := by
  intro F J R
  obtain ⟨hF, L, hL⟩ := exists_tendsto_integral_sourceGradient hK P hstat k hk p q i
  have hJ : Tendsto (fun n => ∫ a, J n a ∂P) atTop (𝓝 R) :=
    tendsto_expected_sourceResponseJ hK P hstat k hk p q
  refine ⟨fun n => ⟨hF n, integrable_sourceResponseJ hK P n k hk p q⟩, L, hL, ?_⟩
  intro m
  have hleft := (hL.sub (tendsto_const_nhds (x := ∫ a, F m a ∂P))).pow 2
  have hright := ((tendsto_const_nhds (x := ∫ a, J m a ∂P)).sub hJ).const_mul (4 * (d : ℝ))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop m] with n hmn
  exact (sq_integral_sourceGradient_sub_le_response_decrement hK P hstat m n k hmn hk p q i).2

end EinsteinFull.Homogenization
