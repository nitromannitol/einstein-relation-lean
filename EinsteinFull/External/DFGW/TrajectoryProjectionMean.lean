import EinsteinFull.External.DFGW.InvariantConstant

/-! # Means of shift-invariant projections

Pairing with the constant one observable identifies the mean of an invariant projection.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

omit [MeasurableSpace S] [BorelSpace S] in
/-- Pairing with the constant one `L²` observable is integration. -/
theorem inner_one_eq_integral (hPfin : P Set.univ ≠ ⊤) (f : Lp ℝ 2 P) :
    inner ℝ (indicatorConstLp 2 MeasurableSet.univ hPfin (1 : ℝ)) f = ∫ η, f η ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := hPfin) (c := (1 : ℝ))] with η hη
  simp only [Set.indicator_univ] at hη
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hη, mul_one]

/-- An invariant observable with the same pairing against one as `f` is the constant mean of `f`. -/
theorem fixed_shift_eq_mean_of_inner_one (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t)
    (p f : Lp ℝ 2 P)
    (hp : (let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
      ⟨measurable_shift _, hP.stationary _⟩
      Lp.compMeasurePreserving _ hshift p) = p)
    (hinner : inner ℝ (indicatorConstLp 2 MeasurableSet.univ hPfin (1 : ℝ)) p =
      inner ℝ (indicatorConstLp 2 MeasurableSet.univ hPfin (1 : ℝ)) f) :
    p = indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, f η ∂P) := by
  have hpmean := fixed_shift_eq_mean hP hcoord hμ hPfin ht p hp
  have heq : (∫ η, p η ∂P) = ∫ η, f η ∂P := by
    rw [← inner_one_eq_integral hPfin p, hinner, inner_one_eq_integral hPfin f]
  rw [hpmean, heq]

end EinsteinFull.External.DFGW
