import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinRelation.Mobility.DriftBoundPointwise
import EinsteinRelation.Entropy.GammaTimeDensities

/-! # The resolvent route to the Fisher bound (Lemma 4.1)

Source: `paper/main.tex` 518-624, in the discrete resolvent form of
the proof of Lemma 4.1. This file starts with the almost sure
regularity of the reduced coefficients that the elliptic regularity step uses.
-/

open MeasureTheory Filter
open scoped ENNReal Topology NNReal

noncomputable section

open EinsteinRelation.External.GantertSection7Support

namespace EinsteinRelation.Entropy

variable {d : ℕ}

theorem continuous_entry' (x : Vec d) (j k : Fin d) :
    Continuous fun w : FieldPair d => w.1 x j k :=
  ((continuous_eval_const x).comp continuous_fst).matrix_elem j k

/-- The closed set of coefficient pairs with entries bounded by `K` and `L`-Lipschitz. -/
theorem isClosed_goodSet (K : ℝ) (L : ℝ≥0) :
    IsClosed {w : FieldPair d | (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k} := by
  have hset : {w : FieldPair d | (∀ x j k, |w.1 x j k| ≤ K) ∧
      ∀ j k, LipschitzWith L fun y => w.1 y j k} =
      (⋂ x : Vec d, ⋂ j : Fin d, ⋂ k : Fin d, {w : FieldPair d | |w.1 x j k| ≤ K}) ∩
        ⋂ j : Fin d, ⋂ k : Fin d, ⋂ x : Vec d, ⋂ y : Vec d,
          {w : FieldPair d | dist (w.1 x j k) (w.1 y j k) ≤ L * dist x y} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, lipschitzWith_iff_dist_le_mul]
  rw [hset]
  exact IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun j => isClosed_iInter fun k =>
      isClosed_le (continuous_entry' x j k).abs continuous_const)
    (isClosed_iInter fun j => isClosed_iInter fun k => isClosed_iInter fun x =>
      isClosed_iInter fun y =>
        isClosed_le ((continuous_entry' x j k).dist (continuous_entry' y j k)) continuous_const)

/-- Almost every reduced coefficient has entries bounded by `sourceReducedBound Λ₀` and Lipschitz
with a constant depending only on `Λ₀` and `d`. -/
theorem ae_good {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∃ (K : ℝ) (L : ℝ≥0), ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q),
      (∀ x j k, |w.1 x j k| ≤ K) ∧ ∀ j k, LipschitzWith L fun y => w.1 y j k := by
  have hΛ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hC : 0 ≤ Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2) := by positivity
  refine ⟨sourceReducedBound Λ₀,
    ⟨Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2) * ((d : ℝ) + 1), by positivity⟩, ?_⟩
  unfold Carriers.reducedReferenceLaw
  rw [ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable
    (isClosed_goodSet _ _).measurableSet]
  filter_upwards [Q.regular] with ω hω
  obtain ⟨hΛ1, hell, -, hlip, -⟩ := sourceReducedBound_support hΛ hω
  refine ⟨fun x j k => ?_, fun j k => ?_⟩
  · obtain ⟨hsymm, hbd⟩ := hell x
    have hlow : ∀ ξ : Vec d, 0 ≤ dotProduct ξ ((reducedCoefficient ω x).mulVec ξ) := fun ξ =>
      (mul_nonneg (inv_nonneg.mpr (by linarith)) (euclideanSq_nonneg_coords ξ)).trans (hbd ξ).1
    exact abs_entry_le_of_quadratic_bounds (by linarith) _ hsymm hlow (fun ξ => (hbd ξ).2) j k
  · exact lipschitzWith_of_euclidean_bound _ hC (hlip.entry_bound j k)

/-! ## The resolvent recursion for the Gamma densities -/

/-- The density preceding `ρ_m` in the recursion: `ρ_{m-1}`, and `1` for `m = 0`. -/
def gammaPrev (ρ : ℕ → FieldPair d → ℝ) : ℕ → FieldPair d → ℝ
  | 0 => fun _ => 1
  | m + 1 => ρ m

/-- **The summed recursion**: `μ (E[ρ_m F] - E[F]) = ∑_{k ≤ m} E[ρ_k L F]` for horizontal tests,
from the annealed Dynkin identity and the Gamma tails. -/
theorem gamma_sum_identity (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {μ : ℝ} (hμ : 0 < μ) {ρ : ℕ → FieldPair d → ℝ}
    (hρ : ∀ m, IsGammaDensity Q.measure P op μ m (ρ m)) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (v w : FieldPair d), IsRegular (sourceReducedBound Λ₀) v → v.1 = w.1 → ∀ x,
      |envGenerator hd lam F (translate x w)| ≤ B) (m : ℕ) :
    μ * (∫ w, ρ m w * F w ∂(Carriers.reducedReferenceLaw Q) -
        ∫ w, F w ∂(Carriers.reducedReferenceLaw Q)) =
      ∑ k ∈ Finset.range (m + 1),
        ∫ w, ρ k w * clampedEnvGenerator hd lam B F w ∂(Carriers.reducedReferenceLaw Q) := by
  obtain ⟨M0, -, -, -, -, hb0, -, -⟩ := hF.exists_bounds
  have hFB : ∀ w, |F w| ≤ M0 := fun w => by simpa using hb0 w 0
  have hFm : Measurable F := hF.1
  set G := clampedEnvGenerator hd lam B F with hGdef
  have hGm : Measurable G := measurable_clampedEnvGenerator hd lam B hF
  have hGB : ∀ w, |G w| ≤ B := abs_clampedEnvGenerator_le hB0 F
  set c := ∫ w, F w ∂(Carriers.reducedReferenceLaw Q) with hcdef
  have href : Carriers.reducedReferenceLaw Q = Measure.map reduce Q.measure := rfl
  have hI : ∀ k, ∫ w, ρ k w * G w ∂(Carriers.reducedReferenceLaw Q) =
      ∫ t, gk μ k t * Density.observationMean Q.measure P op G t := fun k => by
    rw [href]
    exact integral_mul_gammaDensity Q.measure P op hμ k (hρ k) G hGm hGB
  have hIF : ∫ w, ρ m w * F w ∂(Carriers.reducedReferenceLaw Q) =
      ∫ t, gk μ m t * Density.observationMean Q.measure P op F t := by
    rw [href]
    exact integral_mul_gammaDensity Q.measure P op hμ m (hρ m) F hFm hFB
  have hmF := Density.measurable_integral_reducedObservationAt Q.measure P op F hFm
  have hmG := Density.measurable_integral_reducedObservationAt Q.measure P op G hGm
  have i1 : Integrable (fun t => gk μ m t * Density.observationMean Q.measure P op F t) := by
    refine Integrable.mono' ((integrable_gk hμ m).mul_const M0)
      ((measurable_gk μ m).mul hmF).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gk_nonneg hμ.le m t)]
    exact mul_le_mul_of_nonneg_left
      (Density.abs_integral_reducedObservationAt_le Q.measure P op F hFB t) (gk_nonneg hμ.le m t)
  have hsplit : (∫ t, gk μ m t * Density.observationMean Q.measure P op F t) - c =
      ∫ t, gk μ m t * (Density.observationMean Q.measure P op F t - c) := by
    have i2 : Integrable (fun t => gk μ m t * c) := (integrable_gk hμ m).mul_const c
    have e : (fun t => gk μ m t * (Density.observationMean Q.measure P op F t - c)) =
        fun t => gk μ m t * Density.observationMean Q.measure P op F t - gk μ m t * c :=
      funext fun t => mul_sub _ _ _
    rw [e, integral_sub i1 i2, integral_mul_const, integral_gk hμ m, one_mul]
  have hdyn : ∀ t, gk μ m t * (Density.observationMean Q.measure P op F t - c) =
      gk μ m t * ∫ u in (0 : ℝ)..t, Density.observationMean Q.measure P op G u := fun t => by
    by_cases ht : 0 ≤ t
    · rw [hcdef, annealed_dynkin hFOT hd Q h0 h1 P op hP hF hB0 hB ht]
    · rw [gk_of_neg μ m (not_le.mp ht), zero_mul, zero_mul]
  rw [hIF, hsplit, integral_congr_ae (ae_of_all _ hdyn),
    integral_gk_mul_intervalIntegral hμ m (h := Density.observationMean Q.measure P op G) hmG
      (fun u => Density.abs_integral_reducedObservationAt_le Q.measure P op G hGB u),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hI k, mul_div_cancel₀ _ hμ.ne']

/-- **The resolvent recursion**: `μ E[ρ_m F] - E[ρ_m L F] = μ E[ρ_{m-1} F]`, with `ρ_{-1} = 1`. -/
theorem gamma_resolvent_equation (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {μ : ℝ} (hμ : 0 < μ) {ρ : ℕ → FieldPair d → ℝ}
    (hρ : ∀ m, IsGammaDensity Q.measure P op μ m (ρ m)) (m : ℕ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) :
    μ * (∫ w, ρ m w * F w ∂(Carriers.reducedReferenceLaw Q)) -
        ∫ w, ρ m w * envGenerator hd lam F w ∂(Carriers.reducedReferenceLaw Q) =
      ∫ w, (μ * gammaPrev ρ m w) * F w ∂(Carriers.reducedReferenceLaw Q) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_envGenerator_le hd lam hF (sourceReducedBound_pos' Λ₀)
  have hcl : ∀ k, ∫ w, ρ k w * clampedEnvGenerator hd lam B F w ∂(Carriers.reducedReferenceLaw Q) =
      ∫ w, ρ k w * envGenerator hd lam F w ∂(Carriers.reducedReferenceLaw Q) := fun k =>
    integral_congr_ae ((ae_abs_envGenerator_le hd Q h0 h1 hP hF hB).mono fun w hw => by
      simp only [clampedEnvGenerator_eq hw])
  have hS := gamma_sum_identity hFOT hd Q h0 h1 P op hP hμ hρ hF hB0 hB
  have hpull : ∀ g : FieldPair d → ℝ, ∫ w, (μ * g w) * F w ∂(Carriers.reducedReferenceLaw Q) =
      μ * ∫ w, g w * F w ∂(Carriers.reducedReferenceLaw Q) := fun g => by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun w => by ring)
  cases m with
  | zero =>
    have h := hS 0
    rw [zero_add, Finset.sum_range_one, hcl] at h
    simp only [gammaPrev, mul_one]
    rw [integral_const_mul]
    rw [mul_sub] at h
    linarith
  | succ k =>
    have hk1 := hS (k + 1)
    have hk := hS k
    rw [Finset.sum_range_succ, ← hk, hcl] at hk1
    simp only [gammaPrev]
    rw [hpull]
    rw [mul_sub, mul_sub] at hk1
    linarith

end EinsteinRelation.Entropy
