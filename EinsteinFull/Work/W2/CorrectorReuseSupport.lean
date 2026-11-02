import EinsteinFull.Frozen.JointObservation
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinRelation.Correctors.CanonicalGradientSecondMoment
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinRelation.Clock.CentredClockField

/-!
# Variational corrector support for the actual reduced environment

The canonical Lax–Milgram corrector of the pinned blueprint is exactly the
frozen `correctorGradient`. These results expose its closed potential domain,
mean, full horizontal variational characterization, and actual homogenized
flux. They supply stationary prerequisites for `p:covariance` (main.tex
878–901) and `l:finite-xi` (1091–1125); no covariance limit or corrector
identification with a parabolic time integral is asserted.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Correctors

private instance reducedLaw_probability_instance {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

variable {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)

/-- The frozen pushforward and blueprint reduced law are literally identical. -/
theorem reducedLaw_eq_reducedEnvironmentLaw :
    reducedLaw Q = reducedEnvironmentLaw Q := rfl

/-- The frozen gradient is the blueprint's Euclidean L2 variational gradient. -/
theorem correctorGradient_eq_canonical (i : Fin d) :
    correctorGradient Q i = (canonicalCorrectorGradient Q i).val := rfl

/-- The gradient belongs to the closure of the actual horizontal H1 gradients. -/
theorem correctorGradient_mem_potentialDomain (i : Fin d) :
    correctorGradient Q i ∈ correctorPotentialDomain Q :=
  (canonicalCorrectorGradient Q i).property

/-- Each actual Euclidean coordinate is integrable under the reduced law. -/
theorem integrable_correctorGradient_coordinate (i j : Fin d) :
    Integrable (fun ω => correctorGradient Q i ω j) (reducedLaw Q) :=
  ((Lp.memLp (correctorGradient Q i)).eval_piLp j).integrable (by norm_num)

/-- Every coordinate of the frozen corrector gradient has mean zero. -/
theorem integral_correctorGradient_coordinate (i j : Fin d) :
    (∫ ω, correctorGradient Q i ω j ∂reducedLaw Q) = 0 := by
  have h := canonicalCorrectorGradient_mean_zero Q i j
  rw [euclideanCoordinateMean, ContinuousLinearMap.comp_apply,
    l2Expectation_apply] at h
  refine Eq.trans (integral_congr_ae ?_) h
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j)
    (correctorGradient Q i) (p := 2) (μ := reducedLaw Q)] with ω hω
  exact hω.symm

/-- Mean zero holds as a Euclidean vector identity as well. -/
theorem integral_correctorGradient (i : Fin d) :
    (∫ ω, correctorGradient Q i ω ∂reducedLaw Q) = 0 := by
  ext j
  rw [eval_integral_piLp (integrable_correctorGradient_coordinate Q i) j]
  exact integral_correctorGradient_coordinate Q i j

/-- The flux of the actual frozen gradient annihilates the whole closed domain. -/
theorem correctorGradient_variational_domain (i : Fin d)
    (v : correctorPotentialDomain Q) :
    inner ℝ (v.val : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
      (correctorFluxOfGradient Q i (correctorGradient Q i)) = 0 :=
  canonicalCorrectorGradient_variational_domain Q i v

/-- In particular, every actual horizontal H1 gradient is an admissible test. -/
theorem correctorGradient_variational_horizontalH1 (i : Fin d)
    (f : horizontalH1 (reducedLaw Q) (reducedEnvironmentLaw_stationary Q)) :
    inner ℝ (horizontalEuclideanGradient (reducedLaw Q)
      (reducedEnvironmentLaw_stationary Q) f)
      (correctorFluxOfGradient Q i (correctorGradient Q i)) = 0 :=
  canonicalCorrectorGradient_variational_horizontalH1 Q i f

/-- Testing against all horizontal H1 gradients uniquely identifies a potential gradient. -/
theorem eq_correctorGradient_of_variational (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
    (hG : G ∈ correctorPotentialDomain Q)
    (hvar : ∀ f : horizontalH1 (reducedLaw Q) (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedLaw Q)
        (reducedEnvironmentLaw_stationary Q) f) (correctorFluxOfGradient Q i G) = 0) :
    G = correctorGradient Q i := by
  exact congrArg Subtype.val
    (correctorGradient_eq_canonical_of_horizontal_variational Q i ⟨G, hG⟩ hvar)

/-- Full characterization in the unbundled Euclidean L2 carrier. -/
theorem eq_correctorGradient_iff (i : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
    G = correctorGradient Q i ↔ G ∈ correctorPotentialDomain Q ∧
      ∀ f : horizontalH1 (reducedLaw Q) (reducedEnvironmentLaw_stationary Q),
        inner ℝ (horizontalEuclideanGradient (reducedLaw Q)
          (reducedEnvironmentLaw_stationary Q) f) (correctorFluxOfGradient Q i G) = 0 := by
  constructor
  · rintro rfl
    exact ⟨correctorGradient_mem_potentialDomain Q i,
      correctorGradient_variational_horizontalH1 Q i⟩
  · rintro ⟨hG, hvar⟩
    exact eq_correctorGradient_of_variational Q i G hG hvar

/-- Ellipticity gives a uniform second-moment bound without a literature input. -/
theorem norm_correctorGradient_le (i : Fin d) :
    ‖correctorGradient Q i‖ ≤ (Real.exp (2 * Λ₀) * Λ₀) ^ 2 :=
  norm_canonicalCorrectorGradient_le Q i

/-- The same estimate written as the second moment of the Euclidean norm. -/
theorem integral_norm_correctorGradient_sq_le (i : Fin d) :
    (∫ ω, ‖correctorGradient Q i ω‖ ^ 2 ∂reducedLaw Q) ≤
      (Real.exp (2 * Λ₀) * Λ₀) ^ 4 := by
  have hnorm : (∫ ω, ‖correctorGradient Q i ω‖ ^ 2 ∂reducedLaw Q) =
      ‖correctorGradient Q i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hnorm]
  calc
    _ ≤ ((Real.exp (2 * Λ₀) * Λ₀) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_correctorGradient_le Q i) 2
    _ = _ := by ring

/-- The blueprint flux has exactly the raw coefficient formula, almost everywhere. -/
theorem correctorFluxOfGradient_ae (i : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d,
      correctorFluxOfGradient Q i (correctorGradient Q i) ω j =
        ∑ k : Fin d, ω.1 0 j k * (unitVector i k + correctorGradient Q i ω k) := by
  filter_upwards [reducedOriginCoefficientAction_coeFn Q
    (correctorAffineField Q i + ((canonicalCorrectorGradient Q i).val :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))),
    Lp.coeFn_add (correctorAffineField Q i) ((canonicalCorrectorGradient Q i).val :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)),
    Lp.coeFn_const 2 (reducedLaw Q) (correctorUnitVector i)] with ω ha hadd hc
  intro j
  have hsum : (correctorAffineField Q i + ((canonicalCorrectorGradient Q i).val :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) ω =
      correctorUnitVector i + (canonicalCorrectorGradient Q i).val ω := hadd.trans (congrArg (· + _) hc)
  change (reducedOriginCoefficientAction Q
    (correctorAffineField Q i + ((canonicalCorrectorGradient Q i).val :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) ω).ofLp j = _
  rw [ha, hsum]
  rfl

/-- Each entry of the raw affine flux is integrable. -/
theorem integrable_correctorFlux_coordinate (i j : Fin d) :
    Integrable (fun ω => ∑ k : Fin d,
      ω.1 0 j k * (unitVector i k + correctorGradient Q i ω k)) (reducedLaw Q) := by
  apply (((Lp.memLp (correctorFluxOfGradient Q i
    (correctorGradient Q i))).eval_piLp j).integrable (by norm_num)).congr
  filter_upwards [correctorFluxOfGradient_ae Q i] with ω hω
  exact hω j

/-- The actual anisotropic homogenized matrix is the expected raw corrector flux. -/
theorem homogenizedCoefficient_eq_integral_flux (j i : Fin d) :
    homogenizedCoefficient Q j i = ∫ ω, ∑ k : Fin d,
      ω.1 0 j k * (unitVector i k + correctorGradient Q i ω k) ∂reducedLaw Q := by
  change (∫ ω, canonicalCorrectorFlux Q i ω ∂reducedEnvironmentLaw Q) j = _
  rw [eval_integral_piLp (fun k =>
    ((Lp.memLp (canonicalCorrectorFlux Q i)).eval_piLp k).integrable (by norm_num)) j]
  apply integral_congr_ae
  filter_upwards [correctorFluxOfGradient_ae Q i] with ω hω
  exact hω j

/-- The two existing homogenized-matrix definitions agree literally. -/
theorem homogenizedCoefficient_eq_homogenizedMatrix :
    homogenizedCoefficient Q = homogenizedMatrix Q := rfl

/-- The homogenized coefficient remains symmetric, with no isotropy assumption. -/
theorem homogenizedCoefficient_transpose :
    (homogenizedCoefficient Q).transpose = homogenizedCoefficient Q :=
  homogenizedMatrix_transpose Q

/-- The frozen homogenized coefficient inherits Euclidean ellipticity. -/
theorem homogenizedCoefficient_isElliptic :
    IsElliptic (sourceReducedBound Λ₀) (fun _ : Vec d => homogenizedCoefficient Q) :=
  homogenizedMatrix_isElliptic Q

/-- Every column has the structural Euclidean bound, uniformly over laws. -/
theorem homogenizedCoefficient_column_bound (i : Fin d) :
    euclideanNorm ((homogenizedCoefficient Q).mulVec (unitVector i)) ≤ sourceReducedBound Λ₀ :=
  homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i

/-- The affine gradient has the deterministic unit-vector mean. -/
theorem integral_correctorAffine_coordinate (i k : Fin d) :
    (∫ ω, unitVector i k + correctorGradient Q i ω k ∂reducedLaw Q) = unitVector i k := by
  rw [integral_add (integrable_const _) (integrable_correctorGradient_coordinate Q i k),
    integral_correctorGradient_coordinate, integral_const, probReal_univ, one_smul, add_zero]

/-- The actual commutator is the raw flux minus the homogenized affine flux. -/
theorem commutatorObservation_eq_flux_sub (j i : Fin d) (ω : FieldPair d) :
    commutatorObservation Q j i ω =
      (∑ k : Fin d, ω.1 0 j k * (unitVector i k + correctorGradient Q i ω k)) -
        ∑ k : Fin d, homogenizedCoefficient Q j k *
          (unitVector i k + correctorGradient Q i ω k) := by
  simp only [commutatorObservation, sub_mul, Finset.sum_sub_distrib]

/-- No integrability assumption is needed for the frozen commutator. -/
theorem integrable_commutatorObservation (j i : Fin d) :
    Integrable (commutatorObservation Q j i) (reducedLaw Q) := by
  have hA : Integrable (fun ω => ∑ k : Fin d, homogenizedCoefficient Q j k *
      (unitVector i k + correctorGradient Q i ω k)) (reducedLaw Q) :=
    integrable_finset_sum _ fun k _ =>
      ((integrable_const _).add (integrable_correctorGradient_coordinate Q i k)).const_mul _
  exact ((integrable_correctorFlux_coordinate Q i j).sub hA).congr
    (Filter.Eventually.of_forall fun ω => (commutatorObservation_eq_flux_sub Q j i ω).symm)

/-- The commutator in the covariance proposition has mean zero, for each matrix entry. -/
theorem integral_commutatorObservation (j i : Fin d) :
    (∫ ω, commutatorObservation Q j i ω ∂reducedLaw Q) = 0 := by
  have hA (k : Fin d) : Integrable (fun ω => homogenizedCoefficient Q j k *
      (unitVector i k + correctorGradient Q i ω k)) (reducedLaw Q) :=
    ((integrable_const _).add (integrable_correctorGradient_coordinate Q i k)).const_mul _
  simp_rw [commutatorObservation_eq_flux_sub]
  rw [integral_sub (integrable_correctorFlux_coordinate Q i j)
    (integrable_finset_sum _ (fun k _ => hA k)),
    integral_finset_sum _ (fun k _ => hA k)]
  simp_rw [integral_const_mul, integral_correctorAffine_coordinate]
  rw [← homogenizedCoefficient_eq_integral_flux]
  simp [unitVector, Pi.single_apply, mul_ite]

/-- Every given L2 realization of the actual joint field is centered. -/
theorem IsJointObservation.integral_eq_zero
    {Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)} (hZ : IsJointObservation Q Z)
    (a : JointObservationIndex d) : (∫ ω, Z a ω ∂reducedLaw Q) = 0 := by
  rcases a with ⟨j, i⟩ | ⟨⟩
  · rw [integral_congr_ae (hZ.1 j i), integral_complex_ofReal,
      integral_commutatorObservation, Complex.ofReal_zero]
  · rw [integral_congr_ae hZ.2, integral_complex_ofReal]
    have hclock : (∫ ω, ω.2 0 - ∫ ω', ω'.2 0 ∂reducedLaw Q ∂reducedLaw Q) = 0 :=
      Clock.integral_centredClock Q
    rw [hclock, Complex.ofReal_zero]

end EinsteinFull
