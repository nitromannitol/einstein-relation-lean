import EinsteinFull.External.DFGW.PastFutureMixing
import EinsteinFull.External.DFGW.InvariantFuture
import EinsteinFull.External.DFGW.ShiftInvariance

/-! # Centered invariant trajectory observables

An invariant square-integrable trajectory observable with zero mean is zero. This follows
from past–future mixing and the past and future measurability of invariant observables.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A centered `L²` trajectory observable fixed by a positive time shift vanishes. -/
theorem centered_fixed_shift_eq_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t) (Z : Lp ℝ 2 P)
    (hmean : ∫ η, Z η ∂P = 0)
    (hinv : (let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
      ⟨measurable_shift _, hP.stationary _⟩
      Lp.compMeasurePreserving _ hshift Z) = Z) : Z = 0 := by
  let : IsProbabilityMeasure P := hP.probability
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have hrep := Lp.coeFn_compMeasurePreserving Z hshift
  have hinv' : (Z : C(ℝ, S) → ℝ) ∘ Draft.dfgwShift t =ᵐ[P] Z := by
    rw [hinv] at hrep
    exact hrep.symm
  obtain ⟨hpos, hneg⟩ := ae_grid_shift_invariant hP Z t hinv'
  have hpast := aestronglyMeasurable_past_of_grid_invariant hP hcoord ht Z
    ((Lp.memLp Z).integrable one_le_two) (Lp.stronglyMeasurable Z) hneg
  have hfuture := aestronglyMeasurable_future_of_grid_invariant hP hcoord ht Z
    ((Lp.memLp Z).integrable one_le_two) (Lp.stronglyMeasurable Z) hpos
  have hmix := tendsto_inner_past_future_zero hP hμ ht Z Z hpast hfuture hmean
  let gridMP (n : ℕ) : MeasurePreserving (Draft.dfgwShift (S := S) (n • t : ℝ≥0)) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have heq (n : ℕ) : Lp.compMeasurePreserving _ (gridMP n) Z = Z := by
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving Z _).trans (hpos n)
  have hconst : Tendsto (fun _ : ℕ => inner ℝ Z Z) atTop (𝓝 0) := by
    simpa only [heq] using hmix
  have hzero : inner ℝ Z Z = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  exact inner_self_eq_zero.mp hzero

end EinsteinFull.External.DFGW
