import EinsteinRelation.Mobility.MainStepsBounds
import EinsteinRelation.Correctors.HeatSmoothingContraction
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import EinsteinRelation.Carriers.ScalarAveragingTwin
import EinsteinRelation.Calculus.EnvironmentWeakCalculus

/-! # The velocity rate from the internal steps

Source: `paper/main.tex`, subsection "The velocity" (lines 1092-1149), which proves
`eq.reduced-velocity-rate` (line 1149), the statement of `VelocityRateStep` in `Mobility/MainSteps`.

This file collects the inputs and the algebra of that proof:

* the step statements `AKMFluxDecay` (the flux estimate (4.3) of Theorem 4.1 in `AKM2019book`,
  for the centred flux of `eq.centered-flux`), `VelocityAbelStep` (the Abel limit of the
  drift, lines 1140-1147) and `VelocityResolventRateStep` (`eq.velocity-resolvent-rate`,
  lines 1133-1137);
* the averaging assumption `eq.scalar-averaging-assumption` for the local flux error, from the
  flux estimate, the `L^m` contraction of the heat smoothing, and the local corrector error
  (lines 1101-1112);
* the dyadic localization scale of `eq.localization-scale` (line 1098);
* the passage from the Abel limit and the resolvent rate to the component estimate
  `|ℓ_i / λ - ā_{1i}| ≤ C λ`, and from the components to the Euclidean estimate.

The corrected generator equation `eq.corrected-generator` and the application of Lemma 4.3 that
yield `VelocityResolventRateStep` are not in this file.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinRelation

open EinsteinRelation.Correctors
open EinsteinRelation.Correctors.StationarySpatialRealization (spatialRealization)
open EinsteinRelation.Carriers (reducedReferenceLaw IsReducedLaplaceDensity)

/-- The index `e₁ = ⟨0, _⟩ : Fin d`, which exists since `2 ≤ d`. -/
def firstIdx {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- Step `AKMFluxDecay`, the flux estimate `‖H_t (g_i)_1‖_{L^m(Q)} ≤ C_m (1 + t)^{-1/2}` of
`paper/main.tex` lines 1101-1112 (the estimate (4.3) of Theorem 4.1 in `AKM2019book`). The field
`g_i = a(e_i + ∇φ_i) - ā e_i` is the centred flux of `eq.centered-flux`. On the reduced space it is
the spatial representative of `canonicalCorrectorFlux Q i` minus the constant
`expectedCorrectorFlux Q i`, and its first coordinate is taken at `firstIdx hd`. The constant `C`
depends on `d`, `Λ₀`, `r₀` and `m`, but not on the environment law, the direction `i` or `t`. -/
def AKMFluxDecay : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (m : ℝ), 2 ≤ m →
    ∃ C : ℝ, ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ), 0 ≤ t →
      eLpNorm (heatSmoothed t (fun ω : FieldPair d =>
          (spatialRealization (canonicalCorrectorFlux Q i) ((0 : Vec d), ω)).ofLp (firstIdx hd) -
            (expectedCorrectorFlux Q i).ofLp (firstIdx hd)))
        (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * (Real.sqrt (1 + t))⁻¹)

/-- Step `VelocityAbelStep`, the Abel limit of the drift `b_i^λ = ½ D·(a e_i) + λ e₁·a e_i`
(`paper/main.tex` lines 1140-1147). The divergence `D·(a e_i)` is any weak horizontal divergence
of `a e_i`; `ρ_s` is any family of densities of the reduced Laplace-time law. For every quenched
velocity `v` of the reduced family at force `0 < λ ≤ 1`, the Abel integrals `E[ρ_s b_i^λ]`
converge to `v_i` as `s ↓ 0`. -/
def VelocityAbelStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
    IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ v : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P' lam)) v →
      ∀ (hQ : IsStationary (reducedReferenceLaw Q)) (i : Fin d) (divA : FieldPair d → ℝ),
        HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ
          (fun ω : FieldPair d => (ω.1 0).mulVec (unitVector i)) divA →
        ∀ (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω))
          (rhoOf : ℝ → FieldPair d → ℝ),
          (∀ s : {r : ℝ // 0 < r},
            IsReducedLaplaceDensity Q.measure (P' lam) origin_probability s (rhoOf s.1)) →
          Tendsto (fun s : ℝ => ∫ ω, rhoOf s ω *
              ((1 / 2 : ℝ) * divA ω + lam * (ω.1 0) (firstIdx hd) i) ∂(reducedReferenceLaw Q))
            (𝓝[>] 0) (𝓝 (v i))

/-- Step `VelocityResolventRateStep`, the resolvent bound `eq.velocity-resolvent-rate`
(`paper/main.tex` lines 1133-1137). There are constants `C` and `0 < lamStar ≤ 1`, depending only
on `d`, `Λ₀` and `r₀`, such that for `0 < λ ≤ lamStar`, each component `i`, and each `0 < s ≤ λ²`,
the Abel integral of the drift differs from `λ ā_{1i}` by at most `C λ² + C s K` for a constant `K`
depending on the data but not on `s`. -/
def VelocityResolventRateStep : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ C lamStar : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P' : DiffusionFamily d),
      IsGMPReducedFamily hd Q.ellipticity_parameter Q P' →
      ∀ lam : ℝ, 0 < lam → lam ≤ lamStar →
      ∀ (hQ : IsStationary (reducedReferenceLaw Q)) (i : Fin d) (divA : FieldPair d → ℝ),
        HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ
          (fun ω : FieldPair d => (ω.1 0).mulVec (unitVector i)) divA →
        ∀ (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω))
          (rhoOf : ℝ → FieldPair d → ℝ),
          (∀ s : {r : ℝ // 0 < r},
            IsReducedLaplaceDensity Q.measure (P' lam) origin_probability s (rhoOf s.1)) →
          ∃ K : ℝ, ∀ s : ℝ, 0 < s → s ≤ lam ^ 2 →
            |(∫ ω, rhoOf s ω * ((1 / 2 : ℝ) * divA ω + lam * (ω.1 0) (firstIdx hd) i)
                ∂(reducedReferenceLaw Q)) - lam * abar Q (firstIdx hd) i| ≤
              C * lam ^ 2 + C * s * K

/-! ## The averaging assumption for the local flux error -/

/-- The averaging assumption `eq.scalar-averaging-assumption` for a field `f` that is a bounded
`L^m` approximation of the centred flux: if `g` satisfies the flux decay with constants `A m`
and `‖f - g‖_{L^m} ≤ B m R⁻¹` (the local corrector error, `eq.velocity-local-error`), then
`f` satisfies the averaging bound with `M m = A m + B m`. -/
theorem isScalarAveragingField_of_flux_approx {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    [IsProbabilityMeasure (Carriers.reducedReferenceLaw Q)]
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (M A B : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    {f g : FieldPair d → ℝ}
    (hfL : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}] f)
    (hf : Measurable f) (hg : Measurable g)
    (hM : ∀ m : ℝ, 2 ≤ m → M m = A m + B m)
    (hA : ∀ m : ℝ, 2 ≤ m → 0 ≤ A m) (hB : ∀ m : ℝ, 2 ≤ m → 0 ≤ B m)
    (hfm : ∀ m : ℝ, 2 ≤ m → MemLp f (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q))
    (hgm : ∀ m : ℝ, 2 ≤ m → MemLp g (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q))
    (hflux : ∀ m : ℝ, 2 ≤ m → ∀ t : ℝ, 0 ≤ t →
      eLpNorm (heatSmoothed t g) (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (A m * (Real.sqrt (1 + t))⁻¹))
    (happrox : ∀ m : ℝ, 2 ≤ m →
      eLpNorm (f - g) (ENNReal.ofReal m) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (B m * R⁻¹)) :
    Carriers.IsScalarAveragingField Q M R f := by
  refine ⟨hfL, fun m hm t ht => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have key := eLpNorm_heatSmoothed_le_of_approx (Carriers.reducedReferenceLaw Q) hQ hm1 hf hg
    (hfm m hm) (hgm m hm) ht (hA m hm) (hB m hm) hR (hflux m hm t ht) (happrox m hm)
  rw [hM m hm]
  exact key

/-! ## Scalar and Euclidean algebra -/

/-- The Abel limit and the resolvent bound give the component estimate: if `F s` tends to `ℓ` as
`s ↓ 0` and `|F s - m| ≤ C λ² + C s K` for `0 < s ≤ λ²`, then `|ℓ - m| ≤ C λ²`. -/
theorem abs_sub_le_of_abel_resolvent {F : ℝ → ℝ} {ℓ m C K lam : ℝ} (hlam : 0 < lam)
    (hlim : Tendsto F (𝓝[>] 0) (𝓝 ℓ))
    (hF : ∀ s : ℝ, 0 < s → s ≤ lam ^ 2 → |F s - m| ≤ C * lam ^ 2 + C * s * K) :
    |ℓ - m| ≤ C * lam ^ 2 := by
  have hA : Tendsto (fun s => |F s - m|) (𝓝[>] 0) (𝓝 |ℓ - m|) := (hlim.sub_const m).abs
  have hcont : Continuous (fun s : ℝ => C * lam ^ 2 + C * s * K) := by fun_prop
  have hB : Tendsto (fun s : ℝ => C * lam ^ 2 + C * s * K) (𝓝[>] 0)
      (𝓝 (C * lam ^ 2 + C * 0 * K)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [mul_zero, zero_mul, add_zero] at hB
  refine le_of_tendsto_of_tendsto hA hB ?_
  filter_upwards [Ioo_mem_nhdsGT (pow_pos hlam 2)] with s hs
  exact hF s hs.1 hs.2.le

/-- Division by `λ`: `|ℓ - λ m| ≤ C λ²` gives `|λ⁻¹ ℓ - m| ≤ C λ`. -/
theorem abs_inv_mul_sub_le {ℓ m C lam : ℝ} (hlam : 0 < lam)
    (h : |ℓ - lam * m| ≤ C * lam ^ 2) : |lam⁻¹ * ℓ - m| ≤ C * lam := by
  have e : lam⁻¹ * ℓ - m = lam⁻¹ * (ℓ - lam * m) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr hlam)]
  calc lam⁻¹ * |ℓ - lam * m| ≤ lam⁻¹ * (C * lam ^ 2) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hlam.le)
    _ = C * lam * (lam⁻¹ * lam) := by ring
    _ = C * lam := by rw [inv_mul_cancel₀ hlam.ne', mul_one]

/-- The Euclidean norm is at most the sum of the absolute coordinates. -/
theorem euclideanNorm_le_sum_abs {d : ℕ} (x : Vec d) : euclideanNorm x ≤ ∑ i, |x i| := by
  have h1 : ∑ i, x i * x i ≤ (∑ i, |x i|) ^ 2 := by
    calc ∑ i, x i * x i = ∑ i, |x i| * |x i| :=
          Finset.sum_congr rfl fun i _ => (abs_mul_abs_self (x i)).symm
      _ ≤ ∑ i, ∑ j, |x i| * |x j| :=
          Finset.sum_le_sum fun i hi => Finset.single_le_sum
            (f := fun j => |x i| * |x j|) (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hi
      _ = (∑ i, |x i|) ^ 2 := by rw [sq, Finset.sum_mul_sum]
  unfold euclideanNorm euclideanSq dot
  calc Real.sqrt (∑ i, x i * x i) ≤ Real.sqrt ((∑ i, |x i|) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ∑ i, |x i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

/-- Componentwise bound for `λ⁻¹ v - a` gives the Euclidean bound with the factor `d`. -/
theorem euclideanNorm_inv_smul_sub_le {d : ℕ} {lam C : ℝ} (v a : Vec d)
    (h : ∀ i : Fin d, |lam⁻¹ * v i - a i| ≤ C * lam) :
    euclideanNorm (lam⁻¹ • v - a) ≤ d * (C * lam) := by
  refine (euclideanNorm_le_sum_abs _).trans ?_
  calc ∑ i, |(lam⁻¹ • v - a) i| ≤ ∑ _i : Fin d, C * lam :=
        Finset.sum_le_sum fun i _ => by simpa using h i
    _ = d * (C * lam) := by simp

/-! ## The component estimate for the velocity -/

/-- The first homogenized column is the first row of `ā` transposed: `(ā e₁)_i = ā_{1i}`. -/
theorem abarE1_apply_eq_abar {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) : abarE1 hd Q i = abar Q (firstIdx hd) i := by
  have hsym : abar Q (firstIdx hd) i = abar Q i (firstIdx hd) := by
    rw [abar_eq_homogenizedMatrix Q]
    exact homogenizedMatrix_apply_comm Q (firstIdx hd) i
  exact hsym.symm

/-- Velocity estimate from the component bounds `|v_i - λ ā_{1i}| ≤ C λ²`:
`‖λ⁻¹ v - ā e₁‖ ≤ d C λ`. -/
theorem velocity_bound_of_components {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam C : ℝ} (hlam : 0 < lam) (v : Vec d)
    (hcomp : ∀ i : Fin d, |v i - lam * abar Q (firstIdx hd) i| ≤ C * lam ^ 2) :
    euclideanNorm (lam⁻¹ • v - abarE1 hd Q) ≤ d * (C * lam) := by
  refine euclideanNorm_inv_smul_sub_le v (abarE1 hd Q) fun i => ?_
  rw [abarE1_apply_eq_abar hd Q i]
  exact abs_inv_mul_sub_le hlam (hcomp i)

/-- The velocity estimate of `VelocityRateStep` for one quenched velocity, from the Abel limits
of the components and the component resolvent bounds: each `F i` tends to `v i` and satisfies
`|F i s - λ ā_{1i}| ≤ C λ² + C s K i` for `0 < s ≤ λ²`. -/
theorem velocity_rate_of_component_rates {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam C : ℝ} (hlam : 0 < lam) (v : Vec d)
    (F : Fin d → ℝ → ℝ) (K : Fin d → ℝ)
    (hlim : ∀ i : Fin d, Tendsto (F i) (𝓝[>] 0) (𝓝 (v i)))
    (hF : ∀ (i : Fin d) (s : ℝ), 0 < s → s ≤ lam ^ 2 →
      |F i s - lam * abar Q (firstIdx hd) i| ≤ C * lam ^ 2 + C * s * K i) :
    euclideanNorm (lam⁻¹ • v - abarE1 hd Q) ≤ d * (C * lam) :=
  velocity_bound_of_components hd Q hlam v fun i =>
    abs_sub_le_of_abel_resolvent hlam (hlim i) (hF i)

end EinsteinRelation
