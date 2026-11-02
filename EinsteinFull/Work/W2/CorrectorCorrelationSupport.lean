import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Frozen.VelocityCorrelation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Massive correlations and the canonical corrector energy

The Laplace integral uses the actual complete stationary unforced semigroup.
The zero-mass identification uses strong Euclidean gradient convergence, without
requiring a stationary scalar corrector, including in dimension two.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors

private instance reducedProbability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Every actual unforced stationary evolution is an L2 contraction. -/
theorem IsComplexEnvironmentSemigroup.unforced_norm_apply_le
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : ‖P t f‖ ≤ ‖f‖ := by
  have hb : ‖P t‖ ≤ 1 := by simpa [complexForceShift] using! hP.norm_le t
  exact ((P t).le_opNorm f).trans (by simpa using! mul_le_mul_of_nonneg_right hb (norm_nonneg f))

/-- Positive exponential damping makes every actual L2 orbit Bochner integrable. -/
theorem IsComplexEnvironmentSemigroup.integrable_laplace_orbit
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) • P t.toNNReal f) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-s * t) • P t.toNNReal f) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 f).comp continuous_real_toNNReal)
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0).mul_const ‖f‖).mono'
    hc.aestronglyMeasurable
  filter_upwards with t
  erw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hP.unforced_norm_apply_le _ f) (Real.exp_pos _).le

/-- The actual damped semigroup orbit is the full positive generator resolvent. -/
theorem IsComplexEnvironmentSemigroup.laplace_orbit_eq_resolvent
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • P t.toNNReal f) =
      unforcedComplexResolvent Q i s hs f := by
  let u := unforcedComplexResolvent Q i s hs f
  let F : ℝ → Lp ℂ 2 (reducedLaw Q) := fun t => -(Real.exp (-s * t) • P t.toNNReal u)
  have hF : Continuous F :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 u).comp continuous_real_toNNReal)).neg
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt F
      (Real.exp (-s * t) • P t.toNNReal f) (Ici t) t := by
    have he := ((hasDerivAt_id t).const_mul (-s)).exp
    have ho := hP.hasDerivWithinAt_orbit (unforcedComplexResolvent_spec Q i s hs f) t ht
    have hh := (he.hasDerivWithinAt.smul ho).neg
    simp only [id_eq, mul_one] at hh
    erw [map_sub, map_smul, Complex.coe_smul] at hh
    convert! hh using 1
    module
  have hfinite (T : ℝ) (hT : 0 ≤ T) :
      (∫ t in (0 : ℝ)..T, Real.exp (-s * t) • P t.toNNReal f) = F T - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hF.continuousOn
      (fun t ht => (hd t ht.1.le).mono Ioi_subset_Ici_self)
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 f).comp continuous_real_toNNReal)).intervalIntegrable 0 T
  have hexp : Tendsto (fun t : ℝ => Real.exp (-s * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hs))
  have hzero : Tendsto F atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun t => ?_) (by simpa using! hexp.mul_const ‖u‖)
    change ‖-(Real.exp (-s * t) • P t.toNNReal u)‖ ≤ _
    erw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [neg_mul] using!
      mul_le_mul_of_nonneg_left (hP.unforced_norm_apply_le t.toNNReal u)
        (Real.exp_pos (-s * t)).le
  have hlim := intervalIntegral_tendsto_integral_Ioi 0
    (hP.integrable_laplace_orbit s hs f) tendsto_id
  have hlim' := hzero.sub_const (F 0)
  have heq : (∫ t in Ioi (0 : ℝ), Real.exp (-s * t) • P t.toNNReal f) = -F 0 := by
    apply tendsto_nhds_unique hlim
    simp only [zero_sub] at hlim'
    apply hlim'.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [zero_sub] using! (hfinite T hT).symm
  simpa [F, hP.1, u] using! heq

/-- Every damped bilinear correlation is integrable in actual time. -/
theorem IsComplexEnvironmentSemigroup.integrable_laplace_correlation
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    IntegrableOn (fun t : ℝ => (Real.exp (-s * t) : ℂ) *
      ∫ ω, g ω * P t.toNNReal f ω ∂reducedLaw Q) (Ioi 0) := by
  let L := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 g).restrictScalars ℝ
  have hi := L.integrable_comp (hP.integrable_laplace_orbit s hs f)
  simpa only [map_smul, Complex.real_smul, L, ContinuousLinearMap.coe_restrictScalars', smul_eq_mul,
    ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply'] using! hi

/-- Actual Laplace-resolvent correlation identity, with no Fubini assumption. -/
theorem IsComplexEnvironmentSemigroup.laplace_correlation_eq_resolvent
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
      ∫ ω, g ω * P t.toNNReal f ω ∂reducedLaw Q) =
      ∫ ω, g ω * unforcedComplexResolvent Q i s hs f ω ∂reducedLaw Q := by
  let L := ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 g).restrictScalars ℝ
  have he := L.integral_comp_comm (hP.integrable_laplace_orbit s hs f)
  erw [hP.laplace_orbit_eq_resolvent s hs f] at he
  simpa only [map_smul, Complex.real_smul, L, ContinuousLinearMap.coe_restrictScalars', smul_eq_mul,
    ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply'] using! he

private theorem coefficient_inner_eq_integral {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (u v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
    inner ℝ v (reducedOriginCoefficientAction Q u) =
      ∫ ω, ∑ j, ∑ k, ω.1 0 j k * u ω k * v ω j ∂reducedLaw Q := by
  erw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reducedOriginCoefficientAction_coeFn Q u] with ω hω
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ j, (reducedOriginCoefficientAction Q u ω) j * v ω j) = _
  simp only [hω, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rfl

/-- The raw anisotropic corrector energy is the bounded coefficient L2 pairing. -/
theorem corrector_energy_eq_inner {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    (∫ ω, ∑ a, ∑ b, ω.1 0 a b * correctorGradient Q k ω b *
      correctorGradient Q j ω a ∂reducedLaw Q) =
      inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) :=
  (coefficient_inner_eq_integral Q _ _).symm

/-- Each corrector equation is valid against every closed potential gradient. -/
theorem corrector_energy_eq_neg_affine_pairing {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d)
    (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
    (hv : v ∈ correctorPotentialDomain Q) :
    inner ℝ v (reducedOriginCoefficientAction Q (correctorGradient Q j)) =
      -inner ℝ v (reducedOriginCoefficientAction Q (correctorAffineField Q j)) := by
  let e : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorAffineField Q j
  let g : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorGradient Q j
  have h := correctorGradient_variational_domain Q j ⟨v, hv⟩
  change inner ℝ v (reducedOriginCoefficientAction Q (e + g)) = 0 at h
  erw [map_add, inner_add_right] at h
  linarith only [h]

private theorem affine_inner_coefficient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    inner ℝ (correctorAffineField Q j)
      (reducedOriginCoefficientAction Q (correctorAffineField Q k)) =
      ∫ ω, ω.1 0 j k ∂reducedLaw Q := by
  erw [coefficient_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (correctorUnitVector j),
    Lp.coeFn_const 2 (reducedLaw Q) (correctorUnitVector k)] with ω hj hk
  change correctorAffineField Q j ω = correctorUnitVector j at hj
  change correctorAffineField Q k ω = correctorUnitVector k at hk
  erw [hj, hk]
  simp [correctorUnitVector, mul_ite]

/-- The actual homogenized coefficient equals the mean coefficient minus corrector energy. -/
theorem homogenizedCoefficient_eq_mean_sub_corrector_energy {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    homogenizedCoefficient Q j k = (∫ ω, ω.1 0 j k ∂reducedLaw Q) -
      inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) := by
  have hj := corrector_energy_eq_neg_affine_pairing Q k (correctorGradient Q j)
    (correctorGradient_mem_potentialDomain Q j)
  have hk := corrector_energy_eq_neg_affine_pairing Q j (correctorGradient Q k)
    (correctorGradient_mem_potentialDomain Q k)
  have hsym (u v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
      inner ℝ u (reducedOriginCoefficientAction Q v) =
        inner ℝ v (reducedOriginCoefficientAction Q u) := by
    erw [reducedOriginCoefficientAction_symmetric, real_inner_comm]
    rfl
  erw [homogenizedCoefficient_eq_homogenizedMatrix, homogenizedMatrix_eq_inner]
  let ej : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorAffineField Q j
  let ek : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorAffineField Q k
  let gj : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorGradient Q j
  let gk : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorGradient Q k
  change inner ℝ (ej + gj) (reducedOriginCoefficientAction Q (ek + gk)) = _
  erw [map_add, inner_add_left, inner_add_right, inner_add_right,
    affine_inner_coefficient Q j k, hsym ej]
  erw [← neg_eq_iff_eq_neg.mpr hk, ← neg_eq_iff_eq_neg.mpr hj,
    hsym (correctorGradient Q k)]
  ring

private theorem column_inner_eq_integral {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
    inner ℝ G (reducedOriginCoefficientAction Q (correctorAffineField Q j)) =
      ∫ ω, ∑ k, ω.1 0 k j * G ω k ∂reducedLaw Q := by
  erw [coefficient_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (correctorUnitVector j)] with ω hj
  change correctorAffineField Q j ω = correctorUnitVector j at hj
  erw [hj]
  simp [correctorUnitVector, mul_ite]

private theorem complex_column_of_real_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
    (H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hH : ∀ᵐ ω ∂reducedLaw Q, ∀ k, H k ω = (G ω k : ℂ)) :
    (∫ ω, ∑ k, (ω.1 0 k j : ℂ) * H k ω ∂reducedLaw Q) =
      (inner ℝ G (reducedOriginCoefficientAction Q (correctorAffineField Q j)) : ℝ) := by
  erw [column_inner_eq_integral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hH] with ω hω
  simp only [hω, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The literal drift-resolvent correlation equals its real massive-gradient column pairing. -/
theorem IsReducedDriftObservation.resolvent_correlation_eq_gradient
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d) (s : ℝ) (hs : 0 < s) :
    (∫ ω, β j ω * unforcedComplexResolvent Q i s hs (β k) ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (inner ℝ
        (unforcedComplexResolventRealGradient Q i s hs (β k) Complex.reCLM)
        (reducedOriginCoefficientAction Q (correctorAffineField Q j)) : ℝ) := by
  erw [hβ.integral_mul j _ _
    (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs (β k))]
  congr 1
  apply complex_column_of_real_gradient
  have he := hβ.resolvent_gradient_eq_complexify i k s hs
  filter_upwards [unforcedComplexResolventEuclideanGradient_ae Q i s hs (β k),
    (euclideanComplexify d).coeFn_compLpL
      (unforcedComplexResolventRealGradient Q i s hs (β k) Complex.reCLM)] with ω hω hc
  intro a
  erw [← hω a, he, hc]
  rfl

/-- The zero-mass drift-resolvent correlation is half the actual canonical corrector energy. -/
theorem IsReducedDriftObservation.tendsto_resolvent_correlation
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d) {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => ∫ ω, β j ω *
      unforcedComplexResolvent Q i (s n) (hs n) (β k) ω ∂reducedLaw Q)
      l (𝓝 ((1 / 2 : ℂ) * (inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) : ℝ))) := by
  have hg := hβ.tendsto_real_resolvent_gradient i k s hs ht
  have hp := Filter.Tendsto.inner (𝕜 := ℝ) hg (tendsto_const_nhds (x :=
    reducedOriginCoefficientAction Q (correctorAffineField Q j)))
  have hc := corrector_energy_eq_neg_affine_pairing Q j (correctorGradient Q k)
    (correctorGradient_mem_potentialDomain Q k)
  erw [reducedOriginCoefficientAction_symmetric, real_inner_comm] at hc
  have hc' : -(inner ℝ (correctorGradient Q k)
      (reducedOriginCoefficientAction Q (correctorAffineField Q j))) =
      inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) := by
    simpa only [real_inner_comm] using! hc.symm
  have hh := (Complex.continuous_ofReal.tendsto _).comp hp
  have hh' := hh.const_mul (-(1 / 2 : ℂ))
  simp_rw [hβ.resolvent_correlation_eq_gradient i j k]
  have hlimit : -(1 / 2 : ℂ) * (inner ℝ (correctorGradient Q k)
      (reducedOriginCoefficientAction Q (correctorAffineField Q j)) : ℝ) =
      (1 / 2 : ℂ) * (inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) : ℝ) := by
    rw [neg_mul, ← mul_neg, ← Complex.ofReal_neg, hc']
  rw [hlimit] at hh'
  simpa only [Function.comp_def] using! hh'

/-- The actual massive time correlation equals the actual massive-gradient pairing. -/
theorem IsReducedDriftObservation.laplace_correlation_eq_gradient
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
      ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (inner ℝ
        (unforcedComplexResolventRealGradient Q i s hs (β k) Complex.reCLM)
        (reducedOriginCoefficientAction Q (correctorAffineField Q j)) : ℝ) := by
  erw [hP.laplace_correlation_eq_resolvent, hβ.resolvent_correlation_eq_gradient]

/-- Zero-mass limit of the literal Laplace time correlation, with the factor one half. -/
theorem IsReducedDriftObservation.tendsto_laplace_correlation
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), (Real.exp (-s n * t) : ℂ) *
      ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q)
      l (𝓝 ((1 / 2 : ℂ) * (inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q (correctorGradient Q k)) : ℝ))) := by
  simp_rw [hP.laplace_correlation_eq_resolvent (s _) (hs _) (β k) (β j)]
  exact hβ.tendsto_resolvent_correlation i j k s hs ht

/-- The displayed raw corrector energy is integrable; the integral is not a default value. -/
theorem integrable_corrector_energy {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    Integrable (fun ω => ∑ a, ∑ b, ω.1 0 a b * correctorGradient Q k ω b *
      correctorGradient Q j ω a) (reducedLaw Q) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (correctorGradient Q j)
    (reducedOriginCoefficientAction Q (correctorGradient Q k))).congr
  filter_upwards [reducedOriginCoefficientAction_coeFn Q (correctorGradient Q k)] with ω hω
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ a, (reducedOriginCoefficientAction Q (correctorGradient Q k) ω) a *
    correctorGradient Q j ω a) = _
  simp only [hω, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rfl

/-- Exact massive correlation/energy identity using the canonical and massive real gradients. -/
theorem IsReducedDriftObservation.laplace_correlation_eq_corrector_energy
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
      ∫ ω, β j ω * P t.toNNReal (β k) ω ∂reducedLaw Q) =
      (1 / 2 : ℂ) * (inner ℝ (correctorGradient Q j)
        (reducedOriginCoefficientAction Q
          (unforcedComplexResolventRealGradient Q i s hs (β k) Complex.reCLM)) : ℝ) := by
  erw [hβ.laplace_correlation_eq_gradient i j k hP s hs]
  have hc := corrector_energy_eq_neg_affine_pairing Q j
    (unforcedComplexResolventRealGradient Q i s hs (β k) Complex.reCLM)
    (unforcedComplexResolventRealGradient_mem Q i s hs (β k) Complex.reCLM)
  erw [reducedOriginCoefficientAction_symmetric, real_inner_comm] at hc
  erw [hc]
  push_cast
  ring

/-- At zero force the frozen velocity correlation is exactly the drift bilinear pairing. -/
theorem velocityCorrelation_zero_eq {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k : Fin d)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    velocityCorrelation Q j k 0 P β a t =
      ∫ ω, β j ω * P t (β k) ω ∂reducedLaw Q := by
  simp only [velocityCorrelation, zero_smul, add_zero]

/-- Laplace integrability for the actual frozen zero-force velocity correlation. -/
theorem IsComplexEnvironmentSemigroup.integrable_laplace_velocityCorrelation
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (j k : Fin d)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => (Real.exp (-s * t) : ℂ) *
      velocityCorrelation Q j k 0 P β a t.toNNReal) (Ioi 0) := by
  simp_rw [velocityCorrelation_zero_eq]
  exact hP.integrable_laplace_correlation s hs (β k) (β j)

/-- Half-energy identification for the zero-mass limit of the frozen velocity correlation. -/
theorem IsReducedDriftObservation.tendsto_laplace_velocityCorrelation
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), (Real.exp (-s n * t) : ℂ) *
      velocityCorrelation Q j k 0 P β a t.toNNReal)
      l (𝓝 ((1 / 2 : ℂ) * (∫ ω, ∑ a, ∑ b,
        ω.1 0 a b * correctorGradient Q k ω b * correctorGradient Q j ω a
        ∂reducedLaw Q : ℝ))) := by
  simp_rw [velocityCorrelation_zero_eq, corrector_energy_eq_inner]
  exact hβ.tendsto_laplace_correlation i j k hP s hs ht

/-- The Laplace-regularized linear coefficient tends to the actual homogenized coefficient.
This does not assert convergence of the unweighted time integral. -/
theorem IsReducedDriftObservation.tendsto_laplace_linear_coefficient
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j k : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => (∫ ω, ω.1 0 j k ∂reducedLaw Q : ℝ) -
      (2 : ℂ) * ∫ t in Ioi (0 : ℝ), (Real.exp (-s n * t) : ℂ) *
        velocityCorrelation Q j k 0 P β a t.toNNReal)
      l (𝓝 (homogenizedCoefficient Q j k : ℂ)) := by
  have hh := (hβ.tendsto_laplace_velocityCorrelation i j k hP a s hs ht).const_mul (2 : ℂ)
  have hlim := hh.const_sub ((∫ ω, ω.1 0 j k ∂reducedLaw Q : ℝ) : ℂ)
  convert! hlim using 1
  congr 1
  erw [homogenizedCoefficient_eq_mean_sub_corrector_energy, corrector_energy_eq_inner]
  push_cast
  ring

/-- The exact raw mean-minus-energy identity in the manuscript's index order. -/
theorem mean_coefficient_sub_corrector_energy {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    (∫ ω, ω.1 0 j k ∂reducedLaw Q) -
      (∫ ω, ∑ a, ∑ b, ω.1 0 a b * correctorGradient Q k ω b *
        correctorGradient Q j ω a ∂reducedLaw Q) = homogenizedCoefficient Q j k := by
  erw [corrector_energy_eq_inner, homogenizedCoefficient_eq_mean_sub_corrector_energy]

end EinsteinFull
