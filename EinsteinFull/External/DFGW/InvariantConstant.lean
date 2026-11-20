import EinsteinFull.External.DFGW.InvariantCentered

/-! # Constant invariant trajectory observables

Every square-integrable observable invariant under a positive trajectory shift is almost
surely constant, equal to its mean.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Every `L²` observable invariant under a positive trajectory shift is its mean. -/
theorem fixed_shift_eq_mean (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    {t : ℝ≥0} (ht : 0 < t) (Z : Lp ℝ 2 P)
    (hinv : (let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
      ⟨measurable_shift _, hP.stationary _⟩
      Lp.compMeasurePreserving _ hshift Z) = Z) :
    Z = indicatorConstLp 2 MeasurableSet.univ hPfin (∫ η, Z η ∂P) := by
  let : IsProbabilityMeasure P := hP.probability
  let c : ℝ := ∫ η, Z η ∂P
  let k : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ hPfin c
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  have hk : k =ᵐ[P] fun _ => c := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := hPfin) (c := c)] with η hη
    simpa only [k, Set.indicator_univ] using hη
  have hkfix : Lp.compMeasurePreserving _ hshift k = k := by
    have hkc := hshift.quasiMeasurePreserving.ae hk
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving k hshift, hkc, hk] with η ha hb hc
    simp only [Function.comp_apply] at ha hb
    rw [ha, hb, hc]
  have hkint : ∫ η, k η ∂P = c := by
    rw [integral_congr_ae hk]
    simp
  have hcenter : ∫ η, (Z - k) η ∂P = 0 := by
    rw [integral_congr_ae (Lp.coeFn_sub Z k)]
    change (∫ η, (Z η - k η) ∂P) = 0
    rw [integral_sub ((Lp.memLp Z).integrable one_le_two)
      ((Lp.memLp k).integrable one_le_two), hkint]
    exact sub_self c
  have hfix : Lp.compMeasurePreserving _ hshift (Z - k) = Z - k := by
    rw [map_sub, hinv, hkfix]
  have hzero := centered_fixed_shift_eq_zero hP hcoord hμ ht (Z - k) hcenter hfix
  exact sub_eq_zero.mp hzero

end EinsteinFull.External.DFGW
