import EinsteinRelation.Correctors.MollifierShiftFromCoordinateMoments
import EinsteinRelation.Correctors.PlanarSkewShiftMoments
import EinsteinRelation.Correctors.MollifierShiftSourceIdentity
import EinsteinRelation.Correctors.CanonicalFluxDivergenceSupport

/-! # Literal shifted means of canonical scalar and planar skew potentials

Source: `paper/main.tex:948–955`. Coordinate convolution bounds for the actual
canonical gradient and centered flux imply the printed shifted-integral bounds
for every genuine scalar and skew potential. The potentials and their equations
are supplied by the internal construction, with no extra gauge assumption.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

/-- Each Euclidean column norm of a planar skew matrix is the absolute
value of its independent entry. Source: `paper/main.tex:948–955`. -/
theorem euclideanNorm_column_planar_skew (A : Mat 2)
    (hA : A.transpose = -A) (k : Fin 2) :
    euclideanNorm (fun j => A j k) = |A 0 1| := by
  have h00 : A 0 0 = 0 := by
    have h := congrArg (fun B : Mat 2 => B 0 0) hA
    change A 0 0 = -A 0 0 at h
    linarith
  have h11 : A 1 1 = 0 := by
    have h := congrArg (fun B : Mat 2 => B 1 1) hA
    change A 1 1 = -A 1 1 at h
    linarith
  have h10 : A 1 0 = -A 0 1 := congrArg (fun B : Mat 2 => B 0 1) hA
  fin_cases k <;> simp only [euclideanNorm, euclideanSq, dot, Fin.sum_univ_two]
  · change Real.sqrt (A 0 0 * A 0 0 + A 1 0 * A 1 0) = _
    rw [h00, h10, zero_mul, zero_add, neg_mul_neg, ← pow_two, Real.sqrt_sq_eq_abs]
  · change Real.sqrt (A 0 1 * A 0 1 + A 1 1 * A 1 1) = _
    rw [h11, zero_mul, add_zero, ← pow_two, Real.sqrt_sq_eq_abs]

/-- Spatial almost-everywhere skew symmetry suffices for a weighted
entrywise integral. Source: `paper/main.tex:921–938,948–955`. -/
theorem integral_weight_skew_of_ae {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (μ : Measure Y) (w : Y → ℝ) (S : Y → Mat d)
    (hS : ∀ᵐ y ∂μ, (S y).transpose = -S y) :
    Matrix.transpose (fun j k => ∫ y, w y * S y j k ∂μ) =
      -(fun j k => ∫ y, w y * S y j k ∂μ) := by
  ext j k
  change (∫ y, w y * S y k j ∂μ) = -(∫ y, w y * S y j k ∂μ)
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hS] with y hy
  have h := congrArg (fun A : Mat d => A j k) hy
  change S y k j = -S y j k at h
  rw [h, mul_neg]


/-- A canonical gradient coordinate estimate gives the literal shifted-mean
estimate for any of its spatial potentials. Source: `paper/main.tex:948–955`. -/
theorem canonical_scalar_shift_moment_le_of_coordinate_bounds
    {d : ℕ} (hd : 0 < d) {L r₀ p C R : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hR : 0 < R)
    (u : FieldPair d → Vec d → ℝ)
    (hu : ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakGradient Set.univ (u ω)
      (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp))
    (hbound : ∀ x : Vec d, euclideanNorm x ≤ R → ∀ j : Fin d,
      eLpNorm (fun ω => ((fun z => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate z ω)).ofLp j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d R) x)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹))
    (y : Vec d) (hy : euclideanNorm y ≤ R) :
    MemLp (fun ω => ∫ z, (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * u ω z)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
    eLpNorm (fun ω => ∫ z, (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * u ω z)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal ((d : ℝ) * C) := by
  let G : FieldPair d → Vec d → Vec d := fun ω x =>
    ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
      (reducedEnvironmentLaw Q)) (translate x ω)).ofLp
  have ht : Measurable (fun z : FieldPair d × Vec d => translate z.2 z.1) :=
    Probability.continuous_translate.measurable.comp measurable_swap
  have hGm : Measurable (Function.uncurry G) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous.measurable.comp
      ((Lp.stronglyMeasurable _).measurable.comp ht)
  have hloc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, LocallyIntegrable (u ω) volume :=
    hu.mono fun _ hω => locallyIntegrableOn_univ.mp (hω ⟨0, hd⟩).1
  obtain ⟨hmem, hnorm⟩ := convolution_shift_moment_le_of_coordinate_bounds
    (reducedEnvironmentLaw Q) hp hC hR u G hGm hloc hu hbound y hy
  have heq : (fun ω => ∫ z, (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * u ω z) =ᵐ[reducedEnvironmentLaw Q]
      -(fun ω => (u ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d R) y -
        (u ω ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier d R) 0) := by
    filter_upwards [hloc] with ω hω
    rw [mollifier_shift_integral_eq_convolution_sub hω hR]
    exact (neg_sub _ _).symm
  refine ⟨(memLp_congr_ae heq).mpr hmem.neg, ?_⟩
  rw [eLpNorm_congr_ae heq, eLpNorm_neg]
  exact hnorm

/-- The actual canonical centered flux gives the literal shifted-mean
estimate of the independent planar skew entry. Source: `paper/main.tex:948–955`. -/
theorem canonical_planar_skew_shift_moment_le_of_coordinate_bounds
    {L r₀ p C R : ℝ} (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hR : 0 < R)
    (S : FieldPair 2 → Vec 2 → Mat 2)
    (hskew : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂volume,
      (S ω x).transpose = -(S ω x))
    (hdiv : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakRowDivergence Set.univ (S ω) (fun x =>
        (canonicalCorrectorFlux Q i (translate x ω)).ofLp - (expectedCorrectorFlux Q i).ofLp))
    (hbound : ∀ x : Vec 2, euclideanNorm x ≤ R → ∀ j : Fin 2,
      eLpNorm (fun ω => ((fun z => ((canonicalCorrectorFlux Q i (translate z ω)).ofLp -
          (expectedCorrectorFlux Q i).ofLp) j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) x)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹))
    (y : Vec 2) (hy : euclideanNorm y ≤ R) :
    MemLp (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z 0 1)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
    eLpNorm (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z 0 1)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * C) := by
  let q : FieldPair 2 → Vec 2 → Vec 2 := fun ω x =>
    (canonicalCorrectorFlux Q i (translate x ω)).ofLp - (expectedCorrectorFlux Q i).ofLp
  have ht : Measurable (fun z : FieldPair 2 × Vec 2 => translate z.2 z.1) :=
    Probability.continuous_translate.measurable.comp measurable_swap
  have hqm : Measurable (Function.uncurry q) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).continuous.measurable.comp
      ((Lp.stronglyMeasurable _).measurable.comp ht)).sub measurable_const
  obtain ⟨hmem, hnorm⟩ := planar_skew_shift_moment_le_of_flux_bounds
    (reducedEnvironmentLaw Q) hp hC hR S q hqm hskew hdiv hbound y hy
  have hloc : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      LocallyIntegrable (fun z => S ω z 0 1) volume := by
    filter_upwards [hskew, hdiv] with ω hs hd
    have hw := hasWeakGradient_planar_skew_entry_of_ae isOpen_univ (S ω) (q ω)
      (by simpa only [Measure.restrict_univ] using hs) hd
    exact locallyIntegrableOn_univ.mp (hw 0).1
  have heq : (fun ω => ∫ z, (Calculus.unitMassScaledMollifier 2 R z -
      Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z 0 1) =ᵐ[reducedEnvironmentLaw Q]
      -(fun ω => ((fun z => S ω z 0 1) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) y -
        ((fun z => S ω z 0 1) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) 0) := by
    filter_upwards [hloc] with ω hω
    rw [mollifier_shift_integral_eq_convolution_sub hω hR]
    exact (neg_sub _ _).symm
  refine ⟨(memLp_congr_ae heq).mpr hmem.neg, ?_⟩
  rw [eLpNorm_congr_ae heq, eLpNorm_neg]
  exact hnorm

/-- Literal shifted means of every planar skew column satisfy the same
Euclidean estimate as its independent entry. Source: `paper/main.tex:948–955`. -/
theorem canonical_planar_skew_column_shift_moment_le_of_coordinate_bounds
    {L r₀ p C R : ℝ} (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hR : 0 < R)
    (S : FieldPair 2 → Vec 2 → Mat 2)
    (hskew : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ᵐ x ∂volume,
      (S ω x).transpose = -(S ω x))
    (hdiv : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakRowDivergence Set.univ (S ω) (fun x =>
        (canonicalCorrectorFlux Q i (translate x ω)).ofLp - (expectedCorrectorFlux Q i).ofLp))
    (hbound : ∀ x : Vec 2, euclideanNorm x ≤ R → ∀ j : Fin 2,
      eLpNorm (fun ω => ((fun z => ((canonicalCorrectorFlux Q i (translate z ω)).ofLp -
          (expectedCorrectorFlux Q i).ofLp) j)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Calculus.unitMassScaledMollifier 2 R) x)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (C * R⁻¹))
    (y : Vec 2) (hy : euclideanNorm y ≤ R) (k : Fin 2) :
    MemLp (fun ω => euclideanNorm (fun j => ∫ z,
      (Calculus.unitMassScaledMollifier 2 R z -
        Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
    eLpNorm (fun ω => euclideanNorm (fun j => ∫ z,
      (Calculus.unitMassScaledMollifier 2 R z -
        Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * C) := by
  obtain ⟨hmem, hnorm⟩ := canonical_planar_skew_shift_moment_le_of_coordinate_bounds
    Q i hp hC hR S hskew hdiv hbound y hy
  have heq : (fun ω => euclideanNorm (fun j => ∫ z,
      (Calculus.unitMassScaledMollifier 2 R z -
        Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z j k)) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω => ‖∫ z, (Calculus.unitMassScaledMollifier 2 R z -
        Calculus.unitMassScaledMollifier 2 R (z - y)) * S ω z 0 1‖) := by
    filter_upwards [hskew] with ω hω
    exact (euclideanNorm_column_planar_skew _
      (integral_weight_skew_of_ae volume _ (S ω) hω) k).trans (Real.norm_eq_abs _).symm
  refine ⟨(memLp_congr_ae heq).mpr hmem.norm, ?_⟩
  rw [eLpNorm_congr_ae heq, eLpNorm_norm]
  exact hnorm

end EinsteinRelation.Correctors
