import EinsteinFull.External.DFGW.Trajectory
import Mathlib.Probability.Martingale.Convergence

/-! # Past filtrations on positive grids

Past coordinate sigma-algebras sampled at a positive time step increase to the entire
trajectory sigma-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The past filtration sampled on a nonnegative time grid. -/
def gridPast (t : ℝ≥0) : Filtration ℕ (Draft.dfgwTrajectoryMeasurableSpace (S := S)) where
  seq n := Draft.dfgwPast (n • t)
  mono' _ _ hij := (Draft.dfgwPast (S := S)).mono (nsmul_le_nsmul_left (show 0 ≤ t from bot_le) hij)
  le' n := (Draft.dfgwPast (S := S)).le (n • t)

/-- Every real time is bounded above by a point on a positive time grid. -/
theorem exists_le_gridTime {t : ℝ≥0} (ht : 0 < t) (u : ℝ) :
    ∃ n : ℕ, u ≤ ((n • t : ℝ≥0) : ℝ) := by
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  obtain ⟨n, hn⟩ := exists_nat_gt (u / (t : ℝ))
  refine ⟨n, ?_⟩
  have h := (div_lt_iff₀ ht').mp hn
  simpa only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast] using h.le

/-- Positive-grid past sigma-algebras generate the full coordinate sigma-algebra. -/
theorem iSup_gridPast (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
    Draft.dfgwTrajectoryMeasurableSpace (S := S)) {t : ℝ≥0} (ht : 0 < t) :
    (⨆ n, gridPast (S := S) t n) = Draft.dfgwTrajectoryMeasurableSpace (S := S) := by
  apply le_antisymm
  · exact iSup_le fun n => (gridPast (S := S) t).le n
  · apply le_trans (le_of_eq hcoord.symm)
    apply iSup₂_le
    intro u hu
    obtain ⟨n, hn⟩ := exists_le_gridTime ht u
    apply le_iSup_of_le n
    change MeasurableSpace.comap (fun η : C(ℝ, S) => η u) inferInstance ≤
      Draft.dfgwCoordSigma (Set.Iic ((n • t : ℝ≥0) : ℝ))
    exact le_iSup₂_of_le (f := fun v (_ : v ∈ Set.Iic ((n • t : ℝ≥0) : ℝ)) =>
      MeasurableSpace.comap (fun η : C(ℝ, S) => η v) inferInstance) u hn le_rfl

/-- Conditional expectations on an expanding positive grid converge almost everywhere to
an integrable trajectory observable. -/
theorem tendsto_ae_condExp_gridPast {P : Measure C(ℝ, S)} [IsProbabilityMeasure P]
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S)) {t : ℝ≥0} (ht : 0 < t)
    (f : C(ℝ, S) → ℝ) (hf : Integrable f P) (hfm : StronglyMeasurable f) :
    ∀ᵐ η ∂P, Tendsto (fun n => (P[f | gridPast t n]) η) atTop (𝓝 (f η)) := by
  apply hf.tendsto_ae_condExp
  rwa [iSup_gridPast hcoord ht]

end EinsteinFull.External.DFGW
