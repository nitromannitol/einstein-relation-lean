import EinsteinRelation.Regeneration.KilledSegmentLocality
import EinsteinRelation.Regeneration.HalfSpaces

/-!
# The local one-interval ingredients in Step 2

Source `paper/main.tex:377–381`. The two geometric alternatives for a
past interval, and the future coupling-ball containment, use the literal
Euclidean balls. The unrestricted restricted-path test and the killed
bridge mixture are identified directly from frozen GMP stopped locality.
Iteration over intervals is a separate internal obligation.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- The coupling ball has precisely the longitudinal bounds used in both
half-space arguments of Step 2. -/
theorem couplingRegion_coordinate_bounds {d : ℕ} (i : Fin d) (R : ℝ)
    (z y : Vec d) (hy : y ∈ couplingRegion i R z) :
    z i - R < y i ∧ y i < z i + 11 * R := by
  have hb : euclideanNorm (y - (z + (5 * R) • unitVector i)) < 6 * R := hy
  have ha := lt_of_le_of_lt
    (coordinate_abs_le_euclideanNorm (y - (z + (5 * R) • unitVector i)) i) hb
  have hc : (y - (z + (5 * R) • unitVector i)) i = y i - (z i + 5 * R) := by
    simp [unitVector]
  rw [hc, abs_lt] at ha
  constructor <;> linarith

theorem endpointBall_coordinate_bounds {d : ℕ} (i : Fin d) (R : ℝ)
    (z y : Vec d) (hy : y ∈ endpointBall i R z) :
    z i + 8 * R < y i ∧ y i < z i + 10 * R := by
  have hb : euclideanNorm (y - (z + (9 * R) • unitVector i)) < R := hy
  have ha := lt_of_le_of_lt
    (coordinate_abs_le_euclideanNorm (y - (z + (9 * R) • unitVector i)) i) hb
  have hc : (y - (z + (9 * R) • unitVector i)) i = y i - (z i + 9 * R) := by
    simp [unitVector]
  rw [hc, abs_lt] at ha
  constructor <;> linarith

/-- The low starting-point case of the past locality argument. -/
theorem couplingRegion_subset_past_halfSpace {d : ℕ} (i : Fin d) (R v : ℝ)
    (z : Vec d) (hz : z i < v - 8 * R) :
    couplingRegion i R z ⊆ {y | y i < v + 3 * R} := by
  intro y hy
  have h := (couplingRegion_coordinate_bounds i R z y hy).2
  show y i < v + 3 * R
  linarith

/-- In the other past case, a successful endpoint is strictly beyond the
past barrier, so a path constrained below that barrier cannot contribute. -/
theorem endpointBall_subset_above_past_barrier {d : ℕ} (i : Fin d) (R v : ℝ)
    (z : Vec d) (hz : v - 8 * R ≤ z i) :
    endpointBall i R z ⊆ {y | v < y i} := by
  intro y hy
  have h := (endpointBall_coordinate_bounds i R z y hy).1
  show v < y i
  linarith

/-- Every interval starting above the no-backtracking barrier uses a
coupling ball contained in the source future half-space. -/
theorem couplingRegion_subset_future_halfSpace {d : ℕ} (i : Fin d) (R : ℝ)
    (z : Vec d) (hz : -R ≤ z i) :
    couplingRegion i R z ⊆ {y | -2 * R < y i} := by
  intro y hy
  have h := (couplingRegion_coordinate_bounds i R z y hy).1
  show -2 * R < y i
  linarith

/-- A segment test is determined by the stopped law at its horizon. This
uses precisely the segment-invariance binder of `OneIntervalKernelAt`. -/
theorem integral_eq_of_map_stopPathAt_eq {d : ℕ} (T : ℝ≥0)
    (μ ν : Measure (Path d))
    (heq : μ.map (Diffusion.stopPathAt T) = ν.map (Diffusion.stopPathAt T))
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ T → γ t = γ' t) → F γ = F γ') :
    (∫ γ, F γ ∂μ) = ∫ γ, F γ ∂ν := by
  have hstopped : ∀ γ : Path d, F (Diffusion.stopPathAt T γ) = F γ := by
    intro γ
    apply hsegment
    intro t ht
    exact congrArg γ (min_eq_left ht)
  have h := congrArg (fun ξ : Measure (Path d) => ∫ γ, F γ ∂ξ) heq
  simpa only [integral_map (Diffusion.continuous_stopPathAt T).measurable.aemeasurable
    hF.aestronglyMeasurable, hstopped] using h

/-- Unrestricted segment tests supported on paths inside the locality
region can also be recovered from the frozen stopped-law equality. -/
theorem integral_supported_segment_eq_of_stoppedLaw_eq {d : ℕ}
    (U : Set (Vec d)) (hU : IsOpen U) (T : ℝ≥0) (μ ν : Measure (Path d))
    (hm : Measurable (Diffusion.localityStoppedPath U))
    (heq : μ.map (Diffusion.localityStoppedPath U) = ν.map (Diffusion.localityStoppedPath U))
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ T → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ T → γ t ∈ U) :
    (∫ γ, F γ ∂μ) = ∫ γ, F γ ∂ν := by
  classical
  let S : Set (Path d) := {γ | ∀ t : ℝ≥0, t ≤ T → γ t ∈ U}
  have hS : MeasurableSet S := by
    have hopen := ContinuousMap.isOpen_setOf_mapsTo (X := ℝ≥0) (Y := Vec d)
      (K := Set.Icc (0 : ℝ≥0) T) isCompact_Icc hU
    simpa only [Set.MapsTo, Set.mem_Icc, zero_le, true_and] using hopen.measurableSet
  have hind : S.indicator F = F := by
    funext γ
    by_cases hγ : γ ∈ S
    · exact Set.indicator_of_mem hγ _
    · have hzero : F γ = 0 := by
        by_contra hn
        exact hγ (hsupport γ hn)
      simp [hγ, hzero]
  have hrestrict := Diffusion.map_restrict_stopPathAt_eq_of_stoppedLaw_eq U U hU hU
    Set.Subset.rfl T μ ν hm heq
  have h := integral_eq_of_map_stopPathAt_eq T (μ.restrict S) (ν.restrict S)
    hrestrict F hF hsegment
  simpa only [← integral_indicator hS, hind] using h

/-- Both one-interval test integrals used in the true/false bit formulas
are local when the coupling ball is contained in the region and the test
vanishes on paths leaving it. -/
theorem oneInterval_integrals_eq_of_locality (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (U : Set (Vec d)) (hU : IsOpen U)
    (ω ω' : FieldPair d) (hω : IsRegular Λ₀ ω) (hω' : IsRegular Λ₀ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (heq : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam h0 h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω' hω' lam h0 h1)
    (P P' : QuenchedPathLaws d) (z : Vec d) (hz : z ∈ U)
    (hP : P (z, ω) = r.pathLaw z) (hP' : P' (z, ω') = r'.pathLaw z)
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (hball : couplingRegion i R z ⊆ U)
    (F : Path d → ℝ) (hF : Measurable F)
    (hsegment : ∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ')
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U) :
    (∫ γ, F γ ∂P (z, ω)) = (∫ γ, F γ ∂P' (z, ω')) ∧
      (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) =
        ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P' z ω' := by
  obtain ⟨hm, hstop⟩ := Diffusion.realization_map_localityStoppedPath_eq hLoc hd Λ₀ hΛ₀
    U hU ω ω' hω hω' lam h0 h1 heq r r' z hz
  have hbridge := (killedSegment_and_bridge_map_stop_eq_of_locality hLoc hd Λ₀ hΛ₀ U hU
    ω ω' hω hω' lam h0 h1 heq r r' P P' z hz hP hP' Δ R i hball).2
  refine ⟨?_, integral_eq_of_map_stopPathAt_eq Δ _ _ hbridge F hF hsegment⟩
  rw [hP, hP']
  exact integral_supported_segment_eq_of_stoppedLaw_eq U hU Δ _ _ hm hstop F hF
    hsegment hsupport


end EinsteinRelation.Regeneration
