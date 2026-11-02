import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSmoothR01
import EinsteinRelation.Regeneration.EndpointGap

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint.SbxCFactorizationR01
open EinsteinRelation EinsteinFull.Blueprint

/-- Extract both identities under both laws from the conditioned iteration
contract for `app:factorization` (paper/main.tex:1474–1487).
The complete graph binder list is retained; independence and coupling scope
are already incorporated in the iteration contract's final conjunct. -/
@[nolint unusedArguments]
theorem appendixFactorizationSmooth_of_deps
    (_hindependence : independenceSmoothStmt)
    (hiterate : conditionIterateSmoothStmt)
    (_hscope : couplingScopeSmoothStmt) :
    appendixFactorizationSmoothStmt := by
  intro d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  exact (hiterate d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD).2.2


/-- The appendix slice identity with constant past test, together with empty
small slices and the actual restricted past-kernel locality, gives the
Section 3 environmental factorization at every lattice index. -/
-- The graph retains slices and coupling scope; the appendix identity already
-- incorporates them, and the proved endpoint geometry supplies the past barrier.
@[nolint unusedArguments]
theorem environmentalFactorizationSmooth_of_deps
    (hfactor : appendixFactorizationSmoothStmt)
    (hpast : pastKernelSmoothStmt)
    (_hslices : slicesSmoothStmt)
    (hsmall : node_rt_u3A_factorization_u23_small_u2D_indicesStmt)
    (_hscope : couplingScopeSmoothStmt) :
    environmentalFactorizationSmoothStmt := by
  classical
  intro d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
  constructor
  · intro F hF hbF Φ hΦ hbΦ n μ hμ
    by_cases hn : 2 ≤ n
    · have hh := (hfactor d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
        P K hK hD Φ hΦ hbΦ μ hμ).2 F hF hbF n hn (fun _ => 1)
        measurable_const ⟨1, fun _ => by norm_num⟩
      simpa only [mul_one] using hh
    · rw [hsmall d hd lam l h₀ hl n (by omega)]
      simp only [Measure.restrict_empty, integral_zero_measure, zero_mul]
  · intro m H hH hbH y
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    have hR : 0 < R := div_pos hl h₀
    have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
    let G := (Regeneration.forcedBitTrialEvent Δ lam R i m).indicator H
    let E : Set (Regeneration.CoupledSample d) :=
      {z | y ∈ Regeneration.endpointBall i R (z.1 ((m : ℝ≥0) * Δ))}
    let J := E.indicator G
    have hJ : Measurable[Regeneration.finiteHistorySigma Δ m] J :=
      (hH.indicator (Regeneration.measurableSet_forcedBitTrialEvent_finiteHistory
        Δ hΔ lam R hR i m)).indicator
        (Regeneration.measurableSet_endpointBall_past Δ R i m y)
    have hbJ : Regeneration.BoundedRealTest J := by
      obtain ⟨C, hC⟩ := hbH
      refine ⟨max C 0, fun z => ?_⟩
      by_cases hz : z ∈ E
      · by_cases hΓ : z ∈ Regeneration.forcedBitTrialEvent Δ lam R i m
        · simpa only [J, G, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
            (hC z).trans (le_max_left C 0)
        · simpa only [J, G, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ,
            abs_zero] using (le_max_right C 0)
      · simpa only [J, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
    have hbar : ∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ →
        z.1 t i ≤ y i - 7 * R) → J z = 0 := by
      intro z hz
      by_cases he : z ∈ E
      · by_cases hΓ : z ∈ Regeneration.forcedBitTrialEvent Δ lam R i m
        · exact (hz (Regeneration.forcedBitTrialEvent_endpoint_past_barrier
            Δ hΔ lam R h₀ hR i m z hΓ y he)).elim
        · simp only [J, G, Set.indicator_of_mem he, Set.indicator_of_notMem hΓ]
      · exact Set.indicator_of_notMem he G
    obtain ⟨A, hA, hAe⟩ := hpast d hd D Q hQ lam h₀ h₁ l δ hl hsep hδ₀ hδ₁
      P K hK m (y i - 7 * R) J hJ hbJ hbar
    have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
    rw [hv] at hA
    refine ⟨A, hA, ?_⟩
    filter_upwards [hAe] with ω hω
    rw [← hω]
    change (∫ z, G z *
      (if y ∈ Regeneration.endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) then 1 else 0)
      ∂K (0, ω)) = ∫ z, J z ∂K (0, ω)
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ E
    · change G z * (if z ∈ E then 1 else 0) = E.indicator G z
      rw [if_pos hz, Set.indicator_of_mem hz, mul_one]
    · change G z * (if z ∈ E then 1 else 0) = E.indicator G z
      rw [if_neg hz, Set.indicator_of_notMem hz, mul_zero]


end EinsteinFull.Blueprint.SbxCFactorizationR01
