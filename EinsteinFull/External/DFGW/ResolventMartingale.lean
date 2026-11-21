import EinsteinFull.External.DFGW.DynkinLinearity
import EinsteinFull.External.DFGW.ResolventEnergyCauchy

/-! # Resolvent martingale approximations

Generator resolvents give square-integrable stationary-increment martingales. The distance
between two such increments is determined by the generator energy of the resolvent difference.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The initial Dynkin martingale increment, represented in trajectory `L²`. -/
noncomputable def dynkinIncrementLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) : Lp ℝ 2 P :=
  ((dynkinProcess_memLp hP f t).sub (dynkinProcess_memLp hP f 0)).toLp
    (fun η => dynkinProcess hP f t η - dynkinProcess hP f 0 η)

/-- Differences of Dynkin increments have squared `L²` norm equal to twice time times energy. -/
theorem norm_dynkinIncrementLp_sub_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f h : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    ‖dynkinIncrementLp hP f t - dynkinIncrementLp hP h t‖ ^ 2 =
      (t : ℝ) * (2 * -inner ℝ ((f - h : (transitionSemigroup hP).generatorDomain) : Lp ℝ 2 μ)
        ((transitionSemigroup hP).generator (f - h))) := by
  have heq : dynkinIncrementLp hP f t - dynkinIncrementLp hP h t =
      dynkinIncrementLp hP (f - h) t := by
    apply Lp.ext
    have ha := Lp.coeFn_sub (dynkinIncrementLp hP f t) (dynkinIncrementLp hP h t)
    have hb (v : (transitionSemigroup hP).generatorDomain) :
        dynkinIncrementLp hP v t =ᵐ[P]
          fun η => dynkinProcess hP v t η - dynkinProcess hP v 0 η :=
      MemLp.coeFn_toLp ((dynkinProcess_memLp hP v t).sub (dynkinProcess_memLp hP v 0))
    filter_upwards [ha, hb f, hb h, hb (f - h), dynkinProcess_sub_ae hP f h t,
      dynkinProcess_sub_ae hP f h 0] with η haη hfη hhη hfhη htη h0η
    simp only [Pi.sub_apply] at haη htη h0η
    rw [haη, hfη, hhη, hfhη, htη, h0η]
    ring
  rw [heq, ← real_inner_self_eq_norm_sq, L2.inner_def]
  have hm : dynkinIncrementLp hP (f - h) t =ᵐ[P]
      fun η => dynkinProcess hP (f - h) t η - dynkinProcess hP (f - h) 0 η :=
    MemLp.coeFn_toLp ((dynkinProcess_memLp hP (f - h) t).sub
      (dynkinProcess_memLp hP (f - h) 0))
  have hrep : (∫ η, inner ℝ (dynkinIncrementLp hP (f - h) t η)
      (dynkinIncrementLp hP (f - h) t η) ∂P) =
      ∫ η, (dynkinProcess hP (f - h) t η - dynkinProcess hP (f - h) 0 η) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hm] with η hη
    rw [hη]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  rw [hrep, integral_dynkin_increment_sq_eq_energy hP hcoord (f - h) t]

end EinsteinFull.External.DFGW
