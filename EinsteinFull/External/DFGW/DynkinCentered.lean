import EinsteinFull.External.DFGW.ResolventMartingale

/-! # Centered Dynkin martingales

Subtracting the initial value gives a martingale whose `L²` conditional expectations are its
past values.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The Dynkin process centered at its initial value is a martingale. -/
theorem martingale_dynkin_increment (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) :
    Martingale (fun t η => dynkinProcess hP f t η - dynkinProcess hP f 0 η) Draft.dfgwPast P := by
  let : IsProbabilityMeasure P := hP.probability
  have hM := martingale_dynkinProcess hP hcoord f
  have hzero : Martingale (fun _ => dynkinProcess hP f 0) Draft.dfgwPast P :=
    martingale_const_fun Draft.dfgwPast P (hM.stronglyMeasurable 0)
      ((dynkinProcess_memLp hP f 0).integrable one_le_two)
  exact hM.sub hzero

/-- The `L²` conditional expectation of a future centered Dynkin process is its present value. -/
theorem condExpL2_dynkinIncrementLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) {s t : ℝ≥0} (hst : s ≤ t) :
    (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le s) (dynkinIncrementLp hP f t) : Lp ℝ 2 P) =
      dynkinIncrementLp hP f s := by
  let : IsProbabilityMeasure P := hP.probability
  let M : ℝ≥0 → C(ℝ, S) → ℝ := fun u η => dynkinProcess hP f u η - dynkinProcess hP f 0 η
  have hM : Martingale M Draft.dfgwPast P := martingale_dynkin_increment hP hcoord f
  have hLp (u : ℝ≥0) : MemLp (M u) 2 P :=
    (dynkinProcess_memLp hP f u).sub (dynkinProcess_memLp hP f 0)
  have hrepr (u : ℝ≥0) : dynkinIncrementLp hP f u = (hLp u).toLp (M u) := rfl
  apply Lp.ext
  rw [hrepr t]
  have hleft : (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le s) ((hLp t).toLp (M t)) : Lp ℝ 2 P) =ᵐ[P]
      P[M t | Draft.dfgwPast s] :=
    (hLp t).condExpL2_ae_eq_condExp ((Draft.dfgwPast (S := S)).le s)
  have hright : dynkinIncrementLp hP f s =ᵐ[P] M s := by
    rw [hrepr s]
    exact MemLp.coeFn_toLp (hLp s)
  exact hleft.trans ((hM.condExp_ae_eq hst).trans hright.symm)

end EinsteinFull.External.DFGW
