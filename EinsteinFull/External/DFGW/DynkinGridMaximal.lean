import EinsteinFull.External.DFGW.DynkinCentered
import EinsteinFull.External.DFGW.ReversibleMaximalBound
import EinsteinFull.External.DFGW.GridPastFiltration

/-! # Maximal inequality for Dynkin observables on a grid

A reversible Markov trajectory controls maximal excursions of a generator-domain observable
on each uniform grid by the corresponding Dynkin martingale.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A reversible generator-domain observable satisfies a maximal inequality on every uniform
time grid. -/
theorem measureReal_max_dynkin_grid_le
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (u : ℝ≥0) (n : ℕ)
    (a : ℝ) (ha : 0 < a) :
    (a / 4) * P.real {η | ∃ k ≤ n, a ≤ |(f : Lp ℝ 2 μ) (η ((k • u : ℝ≥0) : ℝ))|} ≤
      (∫ η, |(f : Lp ℝ 2 μ) (η 0)| ∂P) + 2 *
        ∫ η, |dynkinProcess hP f (n • u) η - dynkinProcess hP f 0 η| ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let Z : ℕ → C(ℝ, S) → ℝ := fun k η => (f : Lp ℝ 2 μ) (η (k • u : ℝ≥0))
  let M : ℕ → C(ℝ, S) → ℝ := fun k η =>
    dynkinProcess hP f (k • u) η - dynkinProcess hP f 0 η
  let R : C(ℝ, S) → C(ℝ, S) := Draft.dfgwRefl (((n • u : ℝ≥0) : ℝ) / 2)
  have hR : MeasurePreserving R P P := ⟨measurable_refl _, hP.reversible _⟩
  have hMt := martingale_dynkin_increment hP hcoord f
  have hM : Martingale M (gridPast u) P := by
    constructor
    · intro k
      exact hMt.stronglyMeasurable (k • u)
    · intro k l hkl
      exact hMt.condExp_ae_eq (nsmul_le_nsmul_left (show 0 ≤ u from bot_le) hkl)
  have hraw := martingale_dynkinProcess hP hcoord f
  have hraw0 : StronglyMeasurable[gridPast u 0] (dynkinProcess hP f 0) := by
    change StronglyMeasurable[Draft.dfgwPast ((0 : ℕ) • u)] (dynkinProcess hP f 0)
    rw [zero_nsmul]
    exact hraw.stronglyMeasurable 0
  have hconst : Martingale (fun _ : ℕ => dynkinProcess hP f 0) (gridPast u) P :=
    martingale_const_fun (gridPast u) P hraw0 (hraw.integrable 0)
  have hZeq : Z 0 = dynkinProcess hP f 0 := by
    funext η
    simp only [Z, zero_nsmul, NNReal.coe_zero, dynkinProcess, intervalIntegral.integral_same, sub_zero]
  have hZ0 : Martingale (fun _ : ℕ => Z 0) (gridPast u) P := by rw [hZeq]; exact hconst
  have hrep : ∀ᵐ η ∂P, ∀ k ≤ n, 2 * (Z k η - Z 0 η) =
      M k η - (M n (R η) - M (n - k) (R η)) := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : k ≤ n
    · have hkn : k • u ≤ n • u := nsmul_le_nsmul_left (show 0 ≤ u from bot_le) hk
      have htime : (n • u : ℝ≥0) - k • u = (n - k) • u := by
        apply NNReal.eq
        rw [NNReal.coe_sub hkn]
        simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_sub hk]
        ring
      filter_upwards [ae_observable_difference_eq_dynkin_forward_sub_reversed hP f (k • u)
        (n • u) hkn] with η hη _
      simp only [htime] at hη
      simp only [Z, M, R, zero_nsmul, NNReal.coe_zero]
      linarith
    · exact Eventually.of_forall fun η hk' => (hk hk').elim
  exact measureReal_max_le_of_forward_sub_reversed Z M R hR hZ0 hM n a ha hrep

end EinsteinFull.External.DFGW
