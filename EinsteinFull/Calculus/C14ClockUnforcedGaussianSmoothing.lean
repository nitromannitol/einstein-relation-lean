import EinsteinFull.Calculus.C5ClockFullUnforcedSmoothing
import EinsteinFull.Work.W2.ActualMassiveCorrectorSpatialEllipticRealizationProof
import EinsteinFull.Work.W6.PhysicalLocalTestingSupport
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.ReferenceSpatialCutoff
import EinsteinRelation.Correctors.RescaledSpatialCutoff
import EinsteinRelation.Environment.ActualImageLpTransportSupport
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Environment.LocalIntegralMeasurability
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Pointwise

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Sharpness

noncomputable section

private def clockPhysicalFlux {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (x : Vec d) (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
  ∑ k, clockCoefficientMulAt Q x j k
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))

private theorem clockPhysicalFlux_coe {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (x : Vec d) (j : Fin d) :
    clockPhysicalFlux Q G x j =ᵐ[reducedLaw Q]
      fun ω => ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => clockCoefficientMulAt Q x j k
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))),
    ae_all_iff.mpr (fun k => clockCoefficientMulAt_coe Q x j k
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))),
    ae_all_iff.mpr (fun k => coeFn_complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) x (G k))] with ω hsum hmul htrans
  change (∑ k, clockCoefficientMulAt Q x j k
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))) ω = _
  rw [hsum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [hmul k, htrans k])

private theorem clockPhysicalFlux_eq_translation {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (x : Vec d) (j : Fin d) :
    clockPhysicalFlux Q G x j =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        ((memLp_complex_coefficient_flux Q G j).toLp
          (fun ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω)) := by
  have hrep := (measurePreserving_translate (reducedLaw Q)
    (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae
      (memLp_complex_coefficient_flux Q G j).coeFn_toLp
  apply Lp.ext
  filter_upwards [clockPhysicalFlux_coe Q G x j, hrep,
    coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      ((memLp_complex_coefficient_flux Q G j).toLp
        (fun ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω))] with ω h₁ h₂ h₃
  simp only [translate_matrix, add_zero] at h₂
  exact h₁.trans (h₂.symm.trans h₃.symm)

/-- The actual horizontal generator equation as an equality of spatial
Bochner integrals in environment L². No samplewise version of a conditional
expectation or simultaneous uncountable event is used. -/
private theorem clock_physical_generator_weak {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, φ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) =
      (-1 / 2 : ℂ) • ∫ x : Vec d,
        ∑ j, coordinateDerivative j φ x • clockPhysicalFlux Q G x j := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hderiv (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hflux (j : Fin d) : Continuous (fun x => clockPhysicalFlux Q G x j) := by
    simp_rw [clockPhysicalFlux_eq_translation]
    exact (continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun x : Vec d =>
      ∑ j, coordinateDerivative j φ x • clockPhysicalFlux Q G x j) := by
    apply integrable_finsetSum
    intro j _
    exact ((hderiv j).smul (hflux j)).integrable_of_hasCompactSupport
      (hφc.fderiv_apply ℝ (unitVector j)).smul_right
  let U : Vec d × FieldPair d → ℂ := fun p =>
    ∑ j, (coordinateDerivative j φ p.1 : ℂ) *
      (∑ k, (p.2.1 p.1 j k : ℂ) * G k (translate p.1 p.2))
  have hUm : Measurable U := by
    apply Finset.measurable_sum
    intro j _
    apply (Complex.measurable_ofReal.comp ((hderiv j).measurable.comp measurable_fst)).mul
    apply Finset.measurable_sum
    intro k _
    exact (Complex.continuous_ofReal.comp
      ((continuous_snd.fst.eval continuous_fst).matrix_elem j k)).measurable.mul
        ((Lp.stronglyMeasurable (G k)).measurable.comp
          Probability.continuous_translate.measurable)
  have hU (x : Vec d) : (fun ω => U (x, ω)) =ᵐ[reducedLaw Q]
      ⇑(∑ j, coordinateDerivative j φ x • clockPhysicalFlux Q G x j) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
        (fun j => coordinateDerivative j φ x • clockPhysicalFlux Q G x j),
      ae_all_iff.mpr (fun j => Lp.coeFn_smul (coordinateDerivative j φ x)
        (clockPhysicalFlux Q G x j)),
      ae_all_iff.mpr (fun j => clockPhysicalFlux_coe Q G x j)] with ω hsum hsmul hcoe
    rw [hsum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsmul j]
    simp only [Pi.smul_apply]
    rw [hcoe j]
    exact Complex.real_smul.symm
  have hr := coeFn_integral_joint_l2_representative hi hUm hU
  apply Lp.ext
  filter_upwards [clock_translation_test_integral_coe Q g φ hφ.continuous hφc,
    hr, Lp.coeFn_smul (-1 / 2 : ℂ)
      (∫ x : Vec d, ∑ j, coordinateDerivative j φ x • clockPhysicalFlux Q G x j),
    hfg.unforced_spatial_allTests hG] with ω hl hr hs hw
  rw [hl, hs]
  simp only [Pi.smul_apply]
  rw [hr]
  simpa only [U, mul_comm, smul_eq_mul, neg_div] using hw φ hφ hφc

/-- A fixed bounded operator commuting with the actual coefficient multipliers
on the test support preserves the spatial generator equation there. -/
private theorem clock_local_operator_spatial_generator {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    (L : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hL : ∀ x ∈ U, ∀ j k v,
      L (clockCoefficientMulAt Q x j k v) = clockCoefficientMulAt Q x j k (L v))
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ x : Vec d, φ x • L
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) =
      (-1 / 2 : ℂ) • ∫ x : Vec d, ∑ j, coordinateDerivative j φ x •
        (∑ k, clockCoefficientMulAt Q x j k (L
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k)))) := by
  have hil : Integrable (fun x : Vec d => φ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) :=
    (hφ.continuous.smul ((continuous_complexTranslation _ _).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport hφc.smul_right
  have hir : Integrable (fun x : Vec d =>
      ∑ j, coordinateDerivative j φ x • clockPhysicalFlux Q G x j) := by
    apply integrable_finsetSum
    intro j _
    have hc : Continuous (fun x => clockPhysicalFlux Q G x j) := by
      simp_rw [clockPhysicalFlux_eq_translation]
      exact (continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const)
    exact (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul hc
      ).integrable_of_hasCompactSupport (hφc.fderiv_apply ℝ (unitVector j)).smul_right
  have he := congrArg L (clock_physical_generator_weak Q hfg hG φ hφ hφc)
  rw [map_smul, ← L.integral_comp_comm hil, ← L.integral_comp_comm hir] at he
  simp only [L.map_smul_of_tower] at he
  refine he.trans ?_
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_sum, L.map_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : coordinateDerivative j φ x = 0
  · simp only [hj, zero_smul]
  have hx : x ∈ U := hφU ((tsupport_fderiv_apply_subset ℝ (unitVector j))
    (subset_closure (show x ∈ Function.support (coordinateDerivative j φ) from hj)))
  congr 1
  simp only [clockPhysicalFlux, map_sum]
  exact Finset.sum_congr rfl (fun k _ => hL x hx j k _)

/-- The retained joint-field projection preserves the actual anisotropic
spatial equation within the retained region. -/
private theorem clock_projection_spatial_generator {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ x : Vec d, φ x • clockLocalProjection Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) =
      (-1 / 2 : ℂ) • ∫ x : Vec d, ∑ j, coordinateDerivative j φ x •
        (∑ k, clockCoefficientMulAt Q x j k (clockLocalProjection Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k)))) :=
  clock_local_operator_spatial_generator Q U (clockLocalProjection Q U)
    (fun x hx j k v => clockLocalProjection_coefficient_commute Q U x hx j k v)
    hfg hG φ hφ hφc hφU

private def clockProjectionError {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  ContinuousLinearMap.id ℂ _ - clockLocalProjection Q U

/-- The complementary conditional projection is also an L² contraction. -/
private theorem clock_projection_error_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖clockProjectionError Q U f‖ ≤ ‖f‖ := by
  let : Fact (localSigma U ≤ borel (FieldPair d)) :=
    ⟨Probability.localSigma_le_borel U⟩
  let K := lpMeas ℂ ℂ (localSigma U) 2 (reducedLaw Q)
  change ‖f - K.starProjection f‖ ≤ ‖f‖
  rw [← K.starProjection_orthogonal_val]
  exact Kᗮ.norm_starProjection_apply_le f

/-- Before moving the actual coefficients through the projection, the error
has a global divergence equation with the projected actual flux. Keeping
that flux also outside the retained region allows global common-test
arguments without extending a local equation across the boundary. -/
private theorem clock_projection_error_global_divergence {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, φ x • clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) =
      (-1 / 2 : ℂ) • ∫ x : Vec d, ∑ j, coordinateDerivative j φ x •
        clockProjectionError Q U (clockPhysicalFlux Q G x j) := by
  let L := clockProjectionError Q U
  have hil : Integrable (fun x : Vec d => φ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) :=
    (hφ.continuous.smul ((continuous_complexTranslation _ _).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport hφc.smul_right
  have hir : Integrable (fun x : Vec d =>
      ∑ j, coordinateDerivative j φ x • clockPhysicalFlux Q G x j) := by
    apply integrable_finsetSum
    intro j _
    have hc : Continuous (fun x => clockPhysicalFlux Q G x j) := by
      simp_rw [clockPhysicalFlux_eq_translation]
      exact (continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const)
    exact (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul hc
      ).integrable_of_hasCompactSupport (hφc.fderiv_apply ℝ (unitVector j)).smul_right
  have he := congrArg L (clock_physical_generator_weak Q hfg hG φ hφ hφc)
  rw [map_smul, ← L.integral_comp_comm hil, ← L.integral_comp_comm hir] at he
  simpa only [map_sum, L.map_smul_of_tower] using he

/-- The conditional error retains the actual physical weak gradient. This
does not assert that conditioning commutes with translations. -/
private theorem clock_projection_error_spatial_weak_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (j : Fin d)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, coordinateDerivative j φ x • clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) =
      - ∫ x : Vec d, φ x • clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) := by
  let B := (clockProjectionError Q U).restrictScalars ℝ
  let u : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x => B
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  let v : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x => B
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)
  have hu : Continuous u := B.continuous.comp
    ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hv : Continuous v := B.continuous.comp
    ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hφ' : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ'c : HasCompactSupport (coordinateDerivative j φ) :=
    hφc.fderiv_apply ℝ (unitVector j)
  have hφline (x : Vec d) :
      HasLineDerivAt ℝ φ (coordinateDerivative j φ x) x (unitVector j) :=
    (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _
  have huline (x : Vec d) : HasLineDerivAt ℝ u (v x) x (unitVector j) :=
    B.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (clock_translation_line_deriv Q j f g hfg x) rfl
  have hiu : Integrable (fun x => φ x • u x) :=
    (hφ.continuous.smul hu).integrable_of_hasCompactSupport hφc.smul_right
  have hiv : Integrable (fun x => φ x • v x) :=
    (hφ.continuous.smul hv).integrable_of_hasCompactSupport hφc.smul_right
  have hiu' : Integrable (fun x => coordinateDerivative j φ x • u x) :=
    (hφ'.smul hu).integrable_of_hasCompactSupport hφ'c.smul_right
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (E := Vec d) (F := ℝ) (G := Lp ℂ 2 (reducedLaw Q))
    (W := Lp ℂ 2 (reducedLaw Q)) (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    hiu' hiv hiu (fun x _ => hφline x) (fun x _ => huline x)
  simpa only [neg_neg, ContinuousLinearMap.lsmul_apply, u, v, B,
    ContinuousLinearMap.coe_restrictScalars'] using
    (congrArg Neg.neg hparts).symm

/-- The error left by conditioning satisfies the same spatial PDE in the
retained region. Its coefficient multiplication is the original one. -/
private theorem clock_projection_error_spatial_generator {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ x : Vec d, φ x • clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) =
      (-1 / 2 : ℂ) • ∫ x : Vec d, ∑ j, coordinateDerivative j φ x •
        (∑ k, clockCoefficientMulAt Q x j k (clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k)))) := by
  apply clock_local_operator_spatial_generator Q U (clockProjectionError Q U) ?_
    hfg hG φ hφ hφc hφU
  intro x hx j k v
  simp only [clockProjectionError, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, clockLocalProjection_coefficient_commute Q U x hx]

/-- The literal initial clock has zero conditional error at each retained point. -/
private theorem clock_projection_error_initial {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (x : Vec d) (hx : x ∈ U)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x μ) = 0 := by
  simp only [clockProjectionError, sub_apply,
    ContinuousLinearMap.id_apply, clockLocalProjection_initial_clock Q U x hx μ hμ, sub_self]

/-- Time differentiation of the actual domain orbit commutes with the fixed
conditional error map at each spatial point. -/
private theorem clock_projection_error_hasDerivAt {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (x : Vec d) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    HasDerivAt (fun s : ℝ => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (P s.toNNReal f)))
      (clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (P t g))) (t : ℝ) := by
  let B := ((clockProjectionError Q U).comp
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap
      ).restrictScalars ℝ
  exact B.hasFDerivAt.comp_hasDerivAt (t : ℝ)
    (centeredEquations_forward_hasDerivAt hP hfg t ht)

/-- A continuous environment-L² field has locally square integrable spatial
sections on one event for all compact sets. The jointly measurable
representative is supplied explicitly; no measurability of L² evaluation is
assumed. -/
private theorem clock_joint_l2_local {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {u : Vec d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) {V : Vec d × FieldPair d → ℂ} (hV : Measurable V)
    (hrep : ∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q] u x) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => V (x, ω)) 2 (volume.restrict K) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hball (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun x => V (x, ω)) 2
        (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))) := by
    let K := Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
    have hi : Integrable (fun p => ‖V p‖ ^ 2)
        ((volume.restrict K).prod (reducedLaw Q)) := by
      apply (integrable_prod_iff (hV.norm.pow_const 2).aestronglyMeasurable).mpr
      refine ⟨ae_of_all _ (fun x => ((Lp.memLp (u x)).norm.integrable_sq).congr
        ((hrep x).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)), ?_⟩
      apply ((hu.norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Vec d) ((n : ℝ) + 1))).congr
      filter_upwards with x
      have hn : ‖u x‖ ^ 2 = ∫ ω, ‖(u x) ω‖ ^ 2 ∂reducedLaw Q := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        simp only [real_inner_self_eq_norm_sq]
      change ‖u x‖ ^ 2 = _
      rw [hn]
      apply integral_congr_ae
      filter_upwards [hrep x] with ω hx
      simp only [hx, Real.norm_eq_abs]
      exact (abs_of_nonneg (sq_nonneg ‖(u x) ω‖)).symm
    filter_upwards [hi.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hV.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hω
  filter_upwards [ae_all_iff.mpr hball] with ω hω
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hsubset : K ⊆ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (by linarith))
  exact (hω n).mono_measure (Measure.restrict_mono_set volume hsubset)

/-- The actual conditional-error orbit admits a joint spatial realization
with all compact local L² bounds simultaneously. -/
private theorem clock_projection_error_joint_representative {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ V : Vec d × FieldPair d → ℂ, Measurable V ∧
      (∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q]
        clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => V (x, ω)) 2 (volume.restrict K) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hc : Continuous (fun x => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  obtain ⟨V, hV, hrep⟩ :=
    EinsteinFull.StronglyMeasurable.exists_joint_l2_representative hc.stronglyMeasurable
  exact ⟨V, hV, hrep, clock_joint_l2_local Q hc hV hrep⟩

private theorem clock_projection_error_test_coe {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q))
    {V : Vec d × FieldPair d → ℂ} (hV : Measurable V)
    (hrep : ∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q]
      clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, φ x • clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) =ᵐ[reducedLaw Q]
        fun ω => ∫ x : Vec d, V (x, ω) * (φ x : ℂ) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hc : Continuous (fun x => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hi : Integrable (fun x : Vec d => φ x • clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) :=
    (hφ.smul hc).integrable_of_hasCompactSupport hφc.smul_right
  apply coeFn_integral_joint_l2_representative hi
    (hV.mul (Complex.measurable_ofReal.comp (hφ.measurable.comp measurable_fst)))
  intro x
  filter_upwards [hrep x, Lp.coeFn_smul (φ x)
    (clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))] with ω hx hs
  rw [hs]
  simp only [Pi.smul_apply, Pi.mul_apply, Function.comp_apply, ← hx, Complex.real_smul,
    mul_comm]

/-- Every real scalar projection of the conditional error has its physical
weak derivative on one event shared by all compact smooth tests. -/
private theorem clock_projection_error_scalar_weak_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (j : Fin d)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    {V W : Vec d × FieldPair d → ℂ} (hV : Measurable V) (hW : Measurable W)
    (hVrep : ∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q]
      clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))
    (hWrep : ∀ x, (fun ω => W (x, ω)) =ᵐ[reducedLaw Q]
      clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g))
    (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂reducedLaw Q, HasWeakPartialDerivative Set.univ j
      (fun x => L (V (x, ω))) (fun x => L (W (x, ω))) := by
  have hc (v : Lp ℂ 2 (reducedLaw Q)) : Continuous (fun x => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hVl := clock_joint_l2_local Q (hc f) hV hVrep
  have hWl := clock_joint_l2_local Q (hc g) hW hWrep
  apply EinsteinRelation.Correctors.SpatialScalar.ae_hasWeakPartialDerivative_of_ae_fixedTest
    (reducedLaw Q) (fun ω x => L (V (x, ω))) (fun ω x => L (W (x, ω))) j
  · filter_upwards [hVl, hWl] with ω hv hw
    exact fun K hK => ⟨L.comp_memLp' (hv K hK), L.comp_memLp' (hw K hK)⟩
  · intro ψ
    have hψ' : Continuous (coordinateDerivative j ψ) :=
      (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψ'c : HasCompactSupport (coordinateDerivative j ψ) :=
      ψ.hasCompactSupport.fderiv_apply ℝ (unitVector j)
    have ht := clock_projection_error_spatial_weak_gradient Q U j f g hfg
      ψ ψ.contDiff ψ.hasCompactSupport
    filter_upwards [hVl, hWl,
      clock_projection_error_test_coe Q U f hV hVrep
        (coordinateDerivative j ψ) hψ' hψ'c,
      clock_projection_error_test_coe Q U g hW hWrep ψ ψ.contDiff.continuous
        ψ.hasCompactSupport,
      Lp.coeFn_neg (∫ x : Vec d, ψ x • clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g))]
      with ω hv hw hleft hright hneg
    have he : (∫ x, V (x, ω) * (coordinateDerivative j ψ x : ℂ)) =
        -(∫ x, W (x, ω) * (ψ x : ℂ)) := by
      rw [← hleft, ht, hneg]
      simp only [Pi.neg_apply, hright]
    have hi := integrable_spatial_mul_test hv hψ' hψ'c
    have hj := integrable_spatial_mul_test hw ψ.contDiff.continuous ψ.hasCompactSupport
    have heL := congrArg L he
    rw [map_neg, ← L.integral_comp_comm hi, ← L.integral_comp_comm hj] at heL
    have hp (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
      rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul, mul_comm]
    simpa only [hp] using heL

/-- The projected error and its actual translated horizontal gradient have
a common locally H¹ realization, ready for spatial cutoff energy testing. -/
private theorem clock_projection_error_spatial_realization {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∃ (V : Vec d × FieldPair d → ℂ) (W : Fin d → Vec d × FieldPair d → ℂ),
      Measurable V ∧ (∀ j, Measurable (W j)) ∧
      (∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) ∧
      (∀ j x, (fun ω => W j (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G j))) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        HasWeakGradient Set.univ (fun x => (V (x, ω)).re) (fun x j => (W j (x, ω)).re) ∧
        HasWeakGradient Set.univ (fun x => (V (x, ω)).im) (fun x j => (W j (x, ω)).im) ∧
        ∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => V (x, ω)) 2 (volume.restrict K) ∧
          ∀ j, MemLp (fun x => W j (x, ω)) 2 (volume.restrict K) := by
  classical
  obtain ⟨V, hV, hVrep, hVl⟩ := clock_projection_error_joint_representative Q U f
  choose W hW hWrep hWl using fun j => clock_projection_error_joint_representative Q U (G j)
  refine ⟨V, W, hV, hW, hVrep, hWrep, ?_⟩
  have hre (j : Fin d) := clock_projection_error_scalar_weak_gradient Q U j f (G j)
    (hG j) hV (hW j) hVrep (hWrep j) Complex.reCLM
  have him (j : Fin d) := clock_projection_error_scalar_weak_gradient Q U j f (G j)
    (hG j) hV (hW j) hVrep (hWrep j) Complex.imCLM
  filter_upwards [hVl, ae_all_iff.mpr hWl, ae_all_iff.mpr hre, ae_all_iff.mpr him]
    with ω hv hw hre him
  exact ⟨hre, him, fun K hK => ⟨hv K hK, fun j => hw j K hK⟩⟩

/-- The global error flux and generator source admit one samplewise
divergence identity for every compact smooth spatial test simultaneously. -/
private theorem clock_projection_error_divergence_realization {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∃ (Z : Vec d × FieldPair d → ℂ) (F : Fin d → Vec d × FieldPair d → ℂ),
      Measurable Z ∧ (∀ j, Measurable (F j)) ∧
      (∀ x, (fun ω => Z (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) ∧
      (∀ j x, (fun ω => F j (x, ω)) =ᵐ[reducedLaw Q]
        clockProjectionError Q U (clockPhysicalFlux Q G x j)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        (∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => Z (x, ω)) 2 (volume.restrict K) ∧
          ∀ j, MemLp (fun x => F j (x, ω)) 2 (volume.restrict K)) ∧
        ∀ ψ : EinsteinRelation.Correctors.StationaryCurlRealization.SpatialTest d,
          (∑ j, ∫ x, F j (x, ω) * (coordinateDerivative j ψ x : ℂ)) +
            (∫ x, (2 : ℂ) * Z (x, ω) * (ψ x : ℂ)) = 0 := by
  classical
  let q (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
    (memLp_complex_coefficient_flux Q G j).toLp
      (fun ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω)
  obtain ⟨Z, hZ, hZrep, hZl⟩ := clock_projection_error_joint_representative Q U g
  choose F hF hFrep hFl using fun j => clock_projection_error_joint_representative Q U (q j)
  have hfixed (ψ : EinsteinRelation.Correctors.StationaryCurlRealization.SpatialTest d) : ∀ᵐ ω ∂reducedLaw Q,
      (∑ j, ∫ x, F j (x, ω) * (coordinateDerivative j ψ x : ℂ)) +
        (∫ x, (2 : ℂ) * Z (x, ω) * (ψ x : ℂ)) = 0 := by
    have hψ' (j : Fin d) : Continuous (coordinateDerivative j ψ) :=
      (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψ'c (j : Fin d) : HasCompactSupport (coordinateDerivative j ψ) :=
      ψ.hasCompactSupport.fderiv_apply ℝ (unitVector j)
    let I (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
      ∫ x : Vec d, coordinateDerivative j ψ x • clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (q j))
    have hi (j : Fin d) : Integrable (fun x : Vec d =>
        coordinateDerivative j ψ x • clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (q j))) :=
      ((hψ' j).smul ((clockProjectionError Q U).continuous.comp
        ((continuous_complexTranslation _ _).comp
          (continuous_id.prodMk continuous_const)))).integrable_of_hasCompactSupport
            (hψ'c j).smul_right
    have he := clock_projection_error_global_divergence Q U hfg hG
      ψ ψ.contDiff ψ.hasCompactSupport
    simp_rw [clockPhysicalFlux_eq_translation] at he
    rw [integral_finsetSum _ (fun j _ => hi j)] at he
    filter_upwards [hZl,
      clock_projection_error_test_coe Q U g hZ hZrep
        ψ ψ.contDiff.continuous ψ.hasCompactSupport,
      ae_all_iff.mpr (fun j => clock_projection_error_test_coe Q U (q j)
        (hF j) (hFrep j) (coordinateDerivative j ψ) (hψ' j) (hψ'c j)),
      Lp.coeFn_smul (-1 / 2 : ℂ) (∑ j, I j),
      Lp.coeFn_finsetSum Finset.univ I] with ω hz hztest hftest hsmul hsum
    have heω : (∫ x, Z (x, ω) * (ψ x : ℂ)) =
        (-1 / 2 : ℂ) * ∑ j, ∫ x, F j (x, ω) * (coordinateDerivative j ψ x : ℂ) := by
      rw [← hztest, he, hsmul]
      simp only [Pi.smul_apply, smul_eq_mul, hsum, Finset.sum_apply]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hftest j)
    have hiZ := integrable_spatial_mul_test hz ψ.contDiff.continuous ψ.hasCompactSupport
    rw [show (fun x => (2 : ℂ) * Z (x, ω) * (ψ x : ℂ)) =
      (fun x => (2 : ℂ) * (Z (x, ω) * (ψ x : ℂ))) by ext x; ring,
      integral_const_mul, heω]
    ring
  have hall := EinsteinFull.MassiveSpatial.ae_allTests_of_fixedTest (reducedLaw Q)
    (fun ω j x => F j (x, ω)) (fun ω x => (2 : ℂ) * Z (x, ω))
    (by
      filter_upwards [hZl, ae_all_iff.mpr hFl] with ω hz hf
      intro K hK
      exact ⟨fun j => hf j K hK, (hz K hK).const_mul 2⟩) hfixed
  refine ⟨Z, F, hZ, hF, hZrep, ?_, ?_⟩
  · intro j x
    simpa only [clockPhysicalFlux_eq_translation] using hFrep j x
  · filter_upwards [hZl, ae_all_iff.mpr hFl, hall] with ω hz hf hall
    exact ⟨fun K hK => ⟨hz K hK, fun j => hf j K hK⟩, hall⟩

/-- On the retained region, the projected actual flux is exactly the
actual anisotropic coefficient matrix applied to the error gradient. -/
private theorem clock_projection_error_flux_eq {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (x : Vec d) (hx : x ∈ U) (j : Fin d) :
    clockProjectionError Q U (clockPhysicalFlux Q G x j) =
      ∑ k, clockCoefficientMulAt Q x j k (clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))) := by
  simp only [clockPhysicalFlux, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [clockProjectionError, sub_apply, ContinuousLinearMap.id_apply, map_sub,
    clockLocalProjection_coefficient_commute Q U x hx]

/-- Joint representatives identify the local physical coefficient flux
after interchanging the environment and spatial almost-everywhere events. -/
private theorem clock_projection_error_flux_coe_local {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d)
    {F : Vec d × FieldPair d → ℂ} {W : Fin d → Vec d × FieldPair d → ℂ}
    (hF : Measurable F) (hW : ∀ k, Measurable (W k))
    (hFrep : ∀ x, (fun ω => F (x, ω)) =ᵐ[reducedLaw Q]
      clockProjectionError Q U (clockPhysicalFlux Q G x j))
    (hWrep : ∀ k x, (fun ω => W k (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k)))
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂volume.restrict K,
      F (x, ω) = ∑ k, (ω.1 x j k : ℂ) * W k (x, ω) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hcoeff (k : Fin d) : Measurable (fun p : Vec d × FieldPair d =>
      (p.2.1 p.1 j k : ℂ) * W k p) :=
    (Complex.continuous_ofReal.comp
      ((continuous_snd.fst.eval continuous_fst).matrix_elem j k)).measurable.mul (hW k)
  have hm : MeasurableSet {p : Vec d × FieldPair d |
      F p = ∑ k, (p.2.1 p.1 j k : ℂ) * W k p} :=
    measurableSet_eq_fun hF (Finset.measurable_sum Finset.univ (fun k _ => hcoeff k))
  apply (Measure.ae_ae_comm (μ := volume.restrict K) (ν := reducedLaw Q)
    (p := fun x ω => F (x, ω) = ∑ k, (ω.1 x j k : ℂ) * W k (x, ω)) hm).mp
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  filter_upwards [hFrep x, ae_all_iff.mpr (fun k => hWrep k x),
    Lp.coeFn_finsetSum Finset.univ (fun k => clockCoefficientMulAt Q x j k
      (clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k)))),
    ae_all_iff.mpr (fun k => clockCoefficientMulAt_coe Q x j k
      (clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))))]
    with ω hf hw hsum hmul
  rw [hf, clock_projection_error_flux_eq Q U G x (hKU hx) j, hsum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => by rw [hmul k, hw k])

/-- The common complex divergence identity gives the actual real weak
divergences, including their local integrability requirements. -/
private theorem clock_complex_divergence_to_weak {d : ℕ}
    (F : Fin d → Vec d → ℂ) (Z : Vec d → ℂ)
    (hF : ∀ j K, IsCompact K → MemLp (F j) 2 (volume.restrict K))
    (hZ : ∀ K, IsCompact K → MemLp Z 2 (volume.restrict K))
    (ht : ∀ ψ : EinsteinRelation.Correctors.StationaryCurlRealization.SpatialTest d,
      (∑ j, ∫ x, F j x * (coordinateDerivative j ψ x : ℂ)) +
        (∫ x, (2 : ℂ) * Z x * (ψ x : ℂ)) = 0)
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakDivergence Set.univ (fun x j => L ((1 / 2 : ℂ) * F j x))
      (fun x => L (Z x)) := by
  have hi (v : Vec d → ℂ)
      (hv : ∀ K, IsCompact K → MemLp v 2 (volume.restrict K)) :
      LocallyIntegrableOn (fun x => L (v x)) Set.univ volume := by
    apply locallyIntegrableOn_univ.mpr
    apply locallyIntegrable_iff.mpr
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (L.comp_memLp' (hv K hK)).integrable (by norm_num)
  refine ⟨fun j => hi _ (fun K hK => (hF j K hK).const_mul _), hi Z hZ, ?_⟩
  intro φ hφ
  let ψ : EinsteinRelation.Correctors.StationaryCurlRealization.SpatialTest d :=
    ⟨φ, hφ.1, hφ.2.1, Set.subset_univ _⟩
  have hd (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (j : Fin d) : HasCompactSupport (coordinateDerivative j φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector j)
  have hFi (j : Fin d) : Integrable (fun x =>
      ((1 / 2 : ℂ) * F j x) * (coordinateDerivative j φ x : ℂ)) :=
    integrable_spatial_mul_test (fun K hK => (hF j K hK).const_mul _)
      (hd j) (hdc j)
  have hZi := integrable_spatial_mul_test hZ hφ.1.continuous hφ.2.1
  have hs : (∫ x, ∑ j, ((1 / 2 : ℂ) * F j x) *
      (coordinateDerivative j φ x : ℂ)) =
      (1 / 2 : ℂ) * ∑ j, ∫ x, F j x * (coordinateDerivative j φ x : ℂ) := by
    rw [integral_finsetSum _ (fun j _ => hFi j)]
    simp_rw [mul_assoc, integral_const_mul]
    exact (Finset.mul_sum _ _ _).symm
  have htφ := ht ψ
  change (∑ j, ∫ x, F j x * (coordinateDerivative j φ x : ℂ)) +
    (∫ x, (2 : ℂ) * Z x * (φ x : ℂ)) = 0 at htφ
  simp_rw [mul_assoc] at htφ
  rw [integral_const_mul] at htφ
  have he : (∫ x, ∑ j, ((1 / 2 : ℂ) * F j x) *
      (coordinateDerivative j φ x : ℂ)) = -(∫ x, Z x * (φ x : ℂ)) := by
    rw [hs]
    linear_combination (1 / 2 : ℂ) * htφ
  have heL := congrArg L he
  rw [map_neg, ← L.integral_comp_comm (integrable_finsetSum _ (fun j _ => hFi j)),
    ← L.integral_comp_comm hZi] at heL
  have hp (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul, mul_comm]
  simpa only [Measure.restrict_univ, map_sum, hp, dot, gradient] using heL

/-- On any relatively compact open subset of the retained region, actual
joint error representatives satisfy the physical coefficient PDE. -/
private theorem clock_projection_error_local_pde {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U O : Set (Vec d)) (hO : IsOpen O)
    (hcO : IsCompact (closure O)) (hOU : closure O ⊆ U) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∃ (V Z : Vec d × FieldPair d → ℂ) (W : Fin d → Vec d × FieldPair d → ℂ),
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (W j)) ∧
      (∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) ∧
      (∀ x, (fun ω => Z (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)) ∧
      (∀ j x, (fun ω => W j (x, ω)) =ᵐ[reducedLaw Q] clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G j))) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        HasWeakGradient Set.univ (fun x => (V (x, ω)).re) (fun x j => (W j (x, ω)).re) ∧
        HasWeakGradient Set.univ (fun x => (V (x, ω)).im) (fun x j => (W j (x, ω)).im) ∧
        (∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => V (x, ω)) 2 (volume.restrict K) ∧
          MemLp (fun x => Z (x, ω)) 2 (volume.restrict K) ∧
          ∀ j, MemLp (fun x => W j (x, ω)) 2 (volume.restrict K)) ∧
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence O
          (fun x j => L ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * W k (x, ω)))
          (fun x => L (Z (x, ω))) := by
  classical
  obtain ⟨V, W, hV, hW, hVrep, hWrep, hVloc⟩ :=
    clock_projection_error_spatial_realization Q U f G hG
  obtain ⟨Z, F, hZ, hF, hZrep, hFrep, hZloc⟩ :=
    clock_projection_error_divergence_realization Q U hfg hG
  have hflux (j : Fin d) := clock_projection_error_flux_coe_local Q U G j
    (hF j) hW (hFrep j) hWrep (closure O) hcO hOU
  refine ⟨V, Z, W, hV, hZ, hW, hVrep, hZrep, hWrep, ?_⟩
  filter_upwards [hVloc, hZloc, ae_all_iff.mpr hflux] with ω hv hz hf
  refine ⟨hv.1, hv.2.1, fun K hK =>
    ⟨(hv.2.2 K hK).1, (hz.1 K hK).1, (hv.2.2 K hK).2⟩, ?_⟩
  intro L
  have hdiv := clock_complex_divergence_to_weak
    (fun j x => F j (x, ω)) (fun x => Z (x, ω))
    (fun j K hK => (hz.1 K hK).2 j) (fun K hK => (hz.1 K hK).1) hz.2 L
  apply Correctors.hasWeakDivergence_congr_ae hO
    (Correctors.hasWeakDivergence_mono (Set.subset_univ O) hdiv) ?_ Filter.EventuallyEq.rfl
  have hfO (j : Fin d) := (hf j).filter_mono
    (ae_mono (Measure.restrict_mono_set volume (subset_closure : O ⊆ closure O)))
  filter_upwards [ae_all_iff.mpr hfO] with x hx
  funext j
  rw [hx j]

/-- The physical-image support gives simultaneous ellipticity at every spatial
point, which is needed for samplewise cutoff testing. -/
private theorem clock_reduced_global_ellipticity {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    ∀ᵐ ω ∂reducedLaw Q, IsElliptic (sourceReducedBound Λ) ω.1 := by
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hω
  obtain ⟨η, hη, rfl⟩ := hω
  exact (sourceReducedBound_support Q.ellipticity_parameter hη).2.1

/-- The actual coefficient multiplier has the structural L² operator bound. -/
private theorem clock_coefficient_mul_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (x : Vec d) (j k : Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖clockCoefficientMulAt Q x j k f‖ ≤ sourceReducedBound Λ * ‖f‖ := by
  have hK : 0 < sourceReducedBound Λ := by
    dsimp [sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg Λ, Q.ellipticity_parameter]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [clock_reduced_global_ellipticity Q, clockCoefficientMulAt_coe Q x j k f]
    with ω hell hrep
  have hentry : |ω.1 x j k| ≤ sourceReducedBound Λ := by
    apply abs_entry_le_of_quadratic_bounds hK.le (ω.1 x) (hell x).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hK.le) (euclideanSq_nonneg_coords ξ)).trans
        ((hell x).2 ξ).1
    · exact fun ξ => ((hell x).2 ξ).2
  rw [hrep, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hentry

/-- The complementary projection commutes with a retained coefficient. -/
private theorem clock_projection_error_coefficient_mul {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (x : Vec d) (hx : x ∈ U)
    (j k : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    clockProjectionError Q U (clockCoefficientMulAt Q x j k f) =
      clockCoefficientMulAt Q x j k (clockProjectionError Q U f) := by
  change clockCoefficientMulAt Q x j k f - clockLocalProjection Q U
    (clockCoefficientMulAt Q x j k f) =
    clockCoefficientMulAt Q x j k (f - clockLocalProjection Q U f)
  rw [clockLocalProjection_coefficient_commute Q U x hx j k f, map_sub]

/-- Locality of the actual anisotropic flux is controlled by locality of its
actual horizontal gradient, without any translation-projection identity. -/
private theorem clock_projection_error_physical_flux {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (x : Vec d) (hx : x ∈ U) (j : Fin d) :
    ‖clockProjectionError Q U (clockPhysicalFlux Q G x j)‖ ^ 2 ≤
      (d : ℝ) * (sourceReducedBound Λ) ^ 2 *
        ∑ k, ‖clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))‖ ^ 2 := by
  classical
  let w (k : Fin d) := clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G k))
  let K := sourceReducedBound Λ
  have heq : clockProjectionError Q U (clockPhysicalFlux Q G x j) =
      ∑ k, clockCoefficientMulAt Q x j k (w k) := by
    unfold clockPhysicalFlux
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => clock_projection_error_coefficient_mul Q U x hx j k _)
  have hn : ‖clockProjectionError Q U (clockPhysicalFlux Q G x j)‖ ≤ K * ∑ k, ‖w k‖ := by
    rw [heq, Finset.mul_sum]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun k _ => clock_coefficient_mul_norm_le Q x j k (w k)))
  have hc : (∑ k, ‖w k‖) ^ 2 ≤ (d : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖w k‖))
  calc
    _ ≤ (K * ∑ k, ‖w k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = K ^ 2 * (∑ k, ‖w k‖) ^ 2 := mul_pow _ _ _
    _ ≤ K ^ 2 * ((d : ℝ) * ∑ k, ‖w k‖ ^ 2) := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = _ := by dsimp only [K, w]; ring

/-- Deterministic cutoff energy for the samplewise conditional-error PDE.
Only compact local square integrability is used. -/
private theorem clock_error_cutoff_energy {d : ℕ} {O : Set (Vec d)}
    (hO : IsOpen O) (ω : FieldPair d) (K : ℝ) (hK : 0 < K)
    (hell : IsElliptic K ω.1) (i : Fin d)
    {u z : Vec d → ℂ} {w : Vec d → Fin d → ℂ}
    (hloc : ∀ S : Set (Vec d), IsCompact S →
      MemLp u 2 (volume.restrict S) ∧ MemLp z 2 (volume.restrict S) ∧
      ∀ j, MemLp (fun x => w x j) 2 (volume.restrict S))
    (hre : HasWeakGradient Set.univ (fun x => (u x).re) (fun x j => (w x j).re))
    (him : HasWeakGradient Set.univ (fun x => (u x).im) (fun x j => (w x j).im))
    (hdiv : ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence O
      (fun x j => L ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * w x k))
      (fun x => L (z x)))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest O φ) :
    (K⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖w x j‖ ^ 2)) ≤
      (∫ x, (φ x : ℂ) ^ 2 * star (u x) * (-z x)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) *
        (∫ x, (∑ j, (coordinateDerivative j φ x) ^ 2) * ‖u x‖ ^ 2) := by
  have hentry (x : Vec d) (j k : Fin d) : |ω.1 x j k| ≤ K := by
    apply abs_entry_le_of_quadratic_bounds hK.le (ω.1 x) (hell x).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hK.le) (euclideanSq_nonneg_coords ξ)).trans
        ((hell x).2 ξ).1
    · exact fun ξ => ((hell x).2 ξ).2
  have ha (j k : Fin d) :
      MemLp (fun x => (ω.1 x j k : ℂ)) ∞ (volume.restrict O) := by
    apply memLp_top_of_bound (by fun_prop) K
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hentry x j k)
  have hzero (S : Set (Vec d)) :
      MemLp (fun _ : Vec d => (0 : ℂ)) 2 (volume.restrict S) := MemLp.zero
  have he := physicalLocalEnergy_locallyH1 hO ω.1 ha K⁻¹ K (inv_pos.mpr hK)
    (Filter.Eventually.of_forall (fun x ξ => ((hell x).2 ξ).1))
    (Filter.Eventually.of_forall hentry) i 0
    (fun S hS _ => (hloc S hS).1) (fun S hS _ => (hloc S hS).2.2)
    (fun S hS _ => (hloc S hS).2.1) (fun S _ _ => hzero S)
    (Correctors.hasWeakGradient_mono (Set.subset_univ O) hre)
    (Correctors.hasWeakGradient_mono (Set.subset_univ O) him)
    (by simpa using hdiv Complex.reCLM) (by simpa using hdiv Complex.imCLM) hφ
  simpa only [zero_sub, sub_zero, zero_mul, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_add] using he

/-- The expected cutoff energy differentiates in the environment Hilbert
space. This does not differentiate a representative at a fixed environment. -/
private theorem clock_error_energy_hasDerivAt {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (S : Set (Vec d)) (hS : IsCompact S) (φ : Vec d → ℝ) (hφ : Continuous φ)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x in S, φ x ^ 2 *
      ‖clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (P s.toNNReal f))‖ ^ 2)
      (∫ x in S, φ x ^ 2 * (2 * inner ℝ
        (clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (P t.toNNReal f)))
        (clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (P t.toNNReal g))))) t := by
  let e (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) := clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  have hec (v : Lp ℂ 2 (reducedLaw Q)) : Continuous (e v) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hb (v : Lp ℂ 2 (reducedLaw Q)) (s : ℝ≥0) (x : Vec d) :
      ‖e (P s v) x‖ ≤ ‖v‖ := by
    have hp := hP.norm_le s
    simp only [complexForceShift, norm_zero, zero_mul,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero] at hp
    calc
      _ ≤ ‖P s v‖ := (clock_projection_error_norm_le Q U _).trans_eq
        (norm_complexTranslation _ _ _ _)
      _ ≤ ‖v‖ := ((P s).le_opNorm v).trans
        ((mul_le_mul_of_nonneg_right hp (norm_nonneg v)).trans_eq (one_mul _))
  let F (s : ℝ) (x : Vec d) := φ x ^ 2 * ‖e (P s.toNNReal f) x‖ ^ 2
  let F' (s : ℝ) (x : Vec d) := φ x ^ 2 *
    (2 * inner ℝ (e (P s.toNNReal f) x) (e (P s.toNNReal g) x))
  have hFc (s : ℝ) : Continuous (F s) := (hφ.pow 2).mul ((hec _).norm.pow 2)
  have hF'c (s : ℝ) : Continuous (F' s) :=
    (hφ.pow 2).mul (continuous_const.mul ((hec _).inner (hec _)))
  have hbound (x : Vec d) (s : ℝ) :
      ‖F' s x‖ ≤ φ x ^ 2 * (2 * (‖f‖ * ‖g‖)) := by
    calc
      _ = φ x ^ 2 * (2 * ‖inner ℝ (e (P s.toNNReal f) x)
          (e (P s.toNNReal g) x)‖) := by
        simp only [F', norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (φ x)),
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ φ x ^ 2 * (2 * (‖f‖ * ‖g‖)) := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (mul_le_mul (hb f _ x) (hb g _ x)
          (norm_nonneg _) (norm_nonneg _))
  have hdiff (x : Vec d) (s : ℝ) (hs : 0 < s) :
      HasDerivAt (fun s => F s x) (F' s x) s := by
    have hd := clock_projection_error_hasDerivAt Q U hP hfg x s.toNNReal
      (by simpa only [Real.coe_toNNReal s hs.le] using hs)
    simpa only [Real.coe_toNNReal s hs.le, F, F', e] using
      hd.norm_sq.const_mul (φ x ^ 2)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioi_mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (hFc s).aestronglyMeasurable))
    ((hFc t).continuousOn.integrableOn_compact hS) (hF'c t).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x s _ => hbound x s))
    (((hφ.pow 2).mul continuous_const).continuousOn.integrableOn_compact hS)
    (Filter.Eventually.of_forall (fun x s hs => hdiff x s hs))).2

/-- Fubini identifies the spatial cutoff energy of a joint representative
with its environment-L2 energy. -/
private theorem clock_joint_cutoff_energy {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {u : Vec d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) {V : Vec d × FieldPair d → ℂ} (hV : Measurable V)
    (hrep : ∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q] u x)
    (S : Set (Vec d)) (hS : IsCompact S) (φ : Vec d → ℝ) (hφ : Continuous φ) :
    Integrable (fun p => φ p.1 ^ 2 * ‖V p‖ ^ 2)
      ((volume.restrict S).prod (reducedLaw Q)) ∧
    (∫ ω, (∫ x in S, φ x ^ 2 * ‖V (x, ω)‖ ^ 2) ∂reducedLaw Q) =
      ∫ x in S, φ x ^ 2 * ‖u x‖ ^ 2 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hs (x : Vec d) : Integrable (fun ω => φ x ^ 2 * ‖V (x, ω)‖ ^ 2)
      (reducedLaw Q) :=
    (((Lp.memLp (u x)).norm.integrable_sq).congr
      ((hrep x).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)).const_mul _
  have he (x : Vec d) : (∫ ω, φ x ^ 2 * ‖V (x, ω)‖ ^ 2 ∂reducedLaw Q) =
      φ x ^ 2 * ‖u x‖ ^ 2 := by
    rw [integral_const_mul]
    congr 1
    have hn : ‖u x‖ ^ 2 = ∫ ω, ‖(u x) ω‖ ^ 2 ∂reducedLaw Q := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    rw [hn]
    exact integral_congr_ae ((hrep x).mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)
  have hi : Integrable (fun p : Vec d × FieldPair d => φ p.1 ^ 2 * ‖V p‖ ^ 2)
      ((volume.restrict S).prod (reducedLaw Q)) := by
    apply (integrable_prod_iff
      (((hφ.measurable.comp measurable_fst).pow_const 2).mul
        (hV.norm.pow_const 2)).aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hs, ?_⟩
    apply (((hφ.pow 2).mul (hu.norm.pow 2)).continuousOn.integrableOn_compact hS).congr
    filter_upwards with x
    change φ x ^ 2 * ‖u x‖ ^ 2 = ∫ ω, ‖φ x ^ 2 * ‖V (x, ω)‖ ^ 2‖ ∂reducedLaw Q
    have hn (ω : FieldPair d) : 0 ≤ φ x ^ 2 * ‖V (x, ω)‖ ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hn _)]
    exact (he x).symm
  refine ⟨hi, ?_⟩
  rw [← integral_integral_swap hi]
  exact integral_congr_ae (Filter.Eventually.of_forall he)

/-- The corresponding joint pairing is integrable, and Fubini recovers the
environment Hilbert inner product. -/
private theorem clock_joint_cutoff_pairing {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {u v : Vec d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    {V Z : Vec d × FieldPair d → ℂ} (hV : Measurable V) (hZ : Measurable Z)
    (hVrep : ∀ x, (fun ω => V (x, ω)) =ᵐ[reducedLaw Q] u x)
    (hZrep : ∀ x, (fun ω => Z (x, ω)) =ᵐ[reducedLaw Q] v x)
    (S : Set (Vec d)) (hS : IsCompact S) (φ : Vec d → ℝ) (hφ : Continuous φ) :
    Integrable (fun p => (φ p.1 : ℂ) ^ 2 * (Z p * star (V p)))
      ((volume.restrict S).prod (reducedLaw Q)) ∧
    (∫ ω, (∫ x in S, (φ x : ℂ) ^ 2 * (Z (x, ω) * star (V (x, ω))))
      ∂reducedLaw Q) = ∫ x in S, (φ x : ℂ) ^ 2 * inner ℂ (u x) (v x) := by
  have hE := ((clock_joint_cutoff_energy Q hu hV hVrep S hS φ hφ).1).add
    (clock_joint_cutoff_energy Q hv hZ hZrep S hS φ hφ).1
  have hi : Integrable (fun p : Vec d × FieldPair d =>
      (φ p.1 : ℂ) ^ 2 * (Z p * star (V p)))
      ((volume.restrict S).prod (reducedLaw Q)) := by
    apply hE.mono' (by fun_prop)
    filter_upwards with p
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_star,
      Pi.add_apply]
    nlinarith [mul_nonneg (sq_nonneg (φ p.1)) (sq_nonneg (‖V p‖ - ‖Z p‖)),
      mul_nonneg (sq_nonneg (φ p.1)) (sq_nonneg ‖V p‖),
      mul_nonneg (sq_nonneg (φ p.1)) (sq_nonneg ‖Z p‖)]
  refine ⟨hi, ?_⟩
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hVrep x, hZrep x] with ω hv hz
  simp only [hv, hz, RCLike.inner_apply]
  rfl

/-- Taking expectation in the actual conditional-error PDE gives a cutoff
energy estimate entirely in the environment Hilbert space. -/
private theorem clock_error_expected_cutoff_energy {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U O : Set (Vec d)) (hO : IsOpen O)
    (hcO : IsCompact (closure O)) (hOU : closure O ⊆ U) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest O φ) :
    let K := sourceReducedBound Λ
    let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
    (K⁻¹ / 4) * (∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G j) x‖ ^ 2) ≤
      -(∫ x in closure O, (φ x : ℂ) ^ 2 * inner ℂ (e f x) (e g x)).re +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) *
        (∑ j, ∫ x in closure O, (coordinateDerivative j φ x) ^ 2 * ‖e f x‖ ^ 2) := by
  classical
  let K := sourceReducedBound Λ
  let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  have hec (v : Lp ℂ 2 (reducedLaw Q)) : Continuous (e v) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg Λ, Q.ellipticity_parameter]
  obtain ⟨V, Z, W, hV, hZ, hW, hVr, hZr, hWr, hlocal⟩ :=
    clock_projection_error_local_pde Q U O hO hcO hOU hfg hG
  have hD (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    (Correctors.isSpatialTest_coordinateDerivative hφ j).1.continuous
  have hE (j : Fin d) := clock_joint_cutoff_energy Q (hec (G j)) (hW j) (hWr j)
    (closure O) hcO φ hφ.1.continuous
  have hM (j : Fin d) := clock_joint_cutoff_energy Q (hec f) hV hVr
    (closure O) hcO (coordinateDerivative j φ) (hD j)
  have hB := clock_joint_cutoff_pairing Q (hec f) (hec g) hV hZ hVr hZr
    (closure O) hcO φ hφ.1.continuous
  let E (ω : FieldPair d) := ∑ j, ∫ x in closure O, φ x ^ 2 * ‖W j (x, ω)‖ ^ 2
  let M (ω : FieldPair d) := ∑ j, ∫ x in closure O,
    (coordinateDerivative j φ x) ^ 2 * ‖V (x, ω)‖ ^ 2
  let B (ω : FieldPair d) := ∫ x in closure O,
    (φ x : ℂ) ^ 2 * (Z (x, ω) * star (V (x, ω)))
  let A := 2 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹
  have hEi : Integrable E (reducedLaw Q) :=
    integrable_finsetSum Finset.univ (fun j _ => (hE j).1.integral_prod_right)
  have hMi : Integrable M (reducedLaw Q) :=
    integrable_finsetSum Finset.univ (fun j _ => (hM j).1.integral_prod_right)
  have hBi : Integrable B (reducedLaw Q) := hB.1.integral_prod_right
  have hzero {x : Vec d} (hx : x ∉ closure O) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (subset_closure (hφ.2.2 h)))
  have hDzero {x : Vec d} (hx : x ∉ closure O) (j : Fin d) :
      coordinateDerivative j φ x = 0 := by
    have hxφ : x ∉ tsupport φ := fun h => hx (subset_closure (hφ.2.2 h))
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxφ,
      ContinuousLinearMap.zero_apply]
  have hpoint : ∀ᵐ ω ∂reducedLaw Q,
      (K⁻¹ / 4) * E ω ≤ -(B ω).re + A * M ω := by
    filter_upwards [hlocal, clock_reduced_global_ellipticity Q,
      ae_all_iff.mpr (fun j => (hE j).1.prod_left_ae),
      ae_all_iff.mpr (fun j => (hM j).1.prod_left_ae)] with ω hl hell he hm
    have henergy := clock_error_cutoff_energy hO ω K hK hell i
      hl.2.2.1 hl.1 hl.2.1 hl.2.2.2 hφ
    have hEg : (∫ x, φ x ^ 2 * (∑ j, ‖W j (x, ω)‖ ^ 2)) = E ω := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := closure O) (fun x hx => by simp only [hzero hx, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul])]
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum Finset.univ (fun j _ => he j)
    have hMg : (∫ x, (∑ j, (coordinateDerivative j φ x) ^ 2) * ‖V (x, ω)‖ ^ 2) = M ω := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := closure O) (fun x hx => by simp only [hDzero hx,
          zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_mul])]
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum Finset.univ (fun j _ => hm j)
    have hBg : (∫ x, (φ x : ℂ) ^ 2 * star (V (x, ω)) * (-Z (x, ω))) = -B ω := by
      calc
        _ = -(∫ x, (φ x : ℂ) ^ 2 * (Z (x, ω) * star (V (x, ω)))) := by
          rw [← integral_neg]
          congr 1
          funext x
          ring
        _ = -B ω := by
          congr 1
          exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := closure O)
            (fun x hx => by simp only [hzero hx, Complex.ofReal_zero,
              zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul])).symm
    simpa only [hEg, hMg, hBg, Complex.neg_re] using henergy
  have hi := integral_mono_ae (hEi.const_mul (K⁻¹ / 4))
    (hBi.re.neg.add (hMi.const_mul A)) hpoint
  simp only [Pi.add_apply, Pi.neg_apply, RCLike.re_eq_complex_re] at hi
  have hsum : (∫ ω, -(B ω).re + A * M ω ∂reducedLaw Q) =
      (∫ ω, -(B ω).re ∂reducedLaw Q) + ∫ ω, A * M ω ∂reducedLaw Q := by
    simpa only [Pi.neg_apply, RCLike.re_eq_complex_re] using
      integral_add hBi.re.neg (hMi.const_mul A)
  have hBr : (∫ ω, (B ω).re ∂reducedLaw Q) = (∫ ω, B ω ∂reducedLaw Q).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hBi
  rw [integral_const_mul, hsum, integral_neg, hBr, integral_const_mul] at hi
  have hEI : (∫ ω, E ω ∂reducedLaw Q) =
      ∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G j) x‖ ^ 2 := by
    rw [show E = _ from rfl, integral_finsetSum Finset.univ
      (fun j _ => (hE j).1.integral_prod_right)]
    exact Finset.sum_congr rfl (fun j _ => (hE j).2)
  have hMI : (∫ ω, M ω ∂reducedLaw Q) =
      ∑ j, ∫ x in closure O, (coordinateDerivative j φ x) ^ 2 * ‖e f x‖ ^ 2 := by
    rw [show M = _ from rfl, integral_finsetSum Finset.univ
      (fun j _ => (hM j).1.integral_prod_right)]
    exact Finset.sum_congr rfl (fun j _ => (hM j).2)
  rw [hEI, hMI, hB.2] at hi
  exact hi

/-- Integrate a scalar dissipation inequality without a derivative at the
initial endpoint. All derivatives are ordinary derivatives at positive times. -/
private theorem clock_integrated_dissipation {E E' D M : ℝ → ℝ}
    (hE : Continuous E) (hE' : Continuous E') (hD : Continuous D) (hM : Continuous M)
    {c A t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ s, 0 < s → HasDerivAt E (E' s) s)
    (hb : ∀ s, 0 < s → E' s + c * D s ≤ A * M s) :
    E t + c * (∫ s in (0 : ℝ)..t, D s) ≤ E 0 + A * (∫ s in (0 : ℝ)..t, M s) := by
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    hE.continuousOn (fun s hs => hd s hs.1) (hE'.intervalIntegrable 0 t)
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) ht
    ((hE'.add (continuous_const.mul hD)).intervalIntegrable 0 t)
    ((continuous_const.mul hM).intervalIntegrable 0 t)
    (fun s hs => hb s hs.1)
  change (∫ s in (0 : ℝ)..t, E' s + c * D s) ≤ ∫ s in (0 : ℝ)..t, A * M s at hi
  have hci : IntervalIntegrable (fun s => c * D s) volume 0 t :=
    (continuous_const.mul hD).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add (hE'.intervalIntegrable 0 t) hci,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hft] at hi
  linarith only [hi]

/-- Expected conditional-error energy and dissipation are controlled by the
initial energy and the cutoff-gradient error along the actual unforced orbit. -/
private theorem clock_error_integrated_cutoff_energy {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U O : Set (Vec d)) (hO : IsOpen O)
    (hcO : IsCompact (closure O)) (hOU : closure O ⊆ U) {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hGc : Continuous G) (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q)
      (reducedLaw_stationary Q) (P s.toNNReal f) (G s))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest O φ) (t : ℝ) (ht : 0 ≤ t) :
    let K := sourceReducedBound Λ
    let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
    (∫ x in closure O, φ x ^ 2 * ‖e (P t.toNNReal f) x‖ ^ 2) +
      (K⁻¹ / 2) * (∫ s in (0 : ℝ)..t,
        ∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G s j) x‖ ^ 2) ≤
    (∫ x in closure O, φ x ^ 2 * ‖e f x‖ ^ 2) +
      (4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) *
        (∫ s in (0 : ℝ)..t,
          ∑ j, ∫ x in closure O, (coordinateDerivative j φ x) ^ 2 *
            ‖e (P s.toNNReal f) x‖ ^ 2) := by
  classical
  let K := sourceReducedBound Λ
  let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  have hec {v : ℝ → Lp ℂ 2 (reducedLaw Q)} (hv : Continuous v) :
      Continuous (fun p : ℝ × Vec d => e (v p.1) p.2) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp
        (continuous_snd.prodMk (hv.comp continuous_fst)))
  have hPc (v : Lp ℂ 2 (reducedLaw Q)) : Continuous (fun s : ℝ => P s.toNNReal v) :=
    (hP.2.2.1 v).comp continuous_real_toNNReal
  have hef := hec (hPc f)
  have heg := hec (hPc g)
  have heG (j : Fin d) := hec ((PiLp.continuous_apply 2 _ j).comp hGc)
  let E (s : ℝ) := ∫ x in closure O, φ x ^ 2 * ‖e (P s.toNNReal f) x‖ ^ 2
  let B (s : ℝ) := ∫ x in closure O,
    (φ x : ℂ) ^ 2 * inner ℂ (e (P s.toNNReal f) x) (e (P s.toNNReal g) x)
  let D (s : ℝ) := ∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G s j) x‖ ^ 2
  let M (s : ℝ) := ∑ j, ∫ x in closure O,
    (coordinateDerivative j φ x) ^ 2 * ‖e (P s.toNNReal f) x‖ ^ 2
  let A := 2 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹
  have hEc : Continuous E := continuous_parametric_integral_of_continuous
    (((hφ.1.continuous.comp continuous_snd).pow 2).mul (hef.norm.pow 2)) hcO
  have hBc : Continuous B := continuous_parametric_integral_of_continuous
    (((Complex.continuous_ofReal.comp
      (hφ.1.continuous.comp continuous_snd)).pow 2).mul (hef.inner heg)) hcO
  have hDc : Continuous D := by
    apply continuous_finsetSum
    intro j _
    exact continuous_parametric_integral_of_continuous
      (((hφ.1.continuous.comp continuous_snd).pow 2).mul ((heG j).norm.pow 2)) hcO
  have hMc : Continuous M := by
    apply continuous_finsetSum
    intro j _
    have hj := (Correctors.isSpatialTest_coordinateDerivative hφ j).1.continuous
    exact continuous_parametric_integral_of_continuous
      (((hj.comp continuous_snd).pow 2).mul (hef.norm.pow 2)) hcO
  have hder (s : ℝ) (hs : 0 < s) : HasDerivAt E (2 * (B s).re) s := by
    have hh := clock_error_energy_hasDerivAt Q U hP hfg (closure O) hcO φ
      hφ.1.continuous s hs
    have hi : IntegrableOn (fun x => (φ x : ℂ) ^ 2 *
        inner ℂ (e (P s.toNNReal f) x) (e (P s.toNNReal g) x)) (closure O) := by
      exact (((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2).mul
        ((hef.comp (continuous_const.prodMk continuous_id)).inner
          (heg.comp (continuous_const.prodMk continuous_id)))).continuousOn.integrableOn_compact hcO
    have hreal : (B s).re = ∫ x in closure O, φ x ^ 2 *
        inner ℝ (e (P s.toNNReal f) x) (e (P s.toNNReal g) x) := by
      change (∫ x in closure O, (φ x : ℂ) ^ 2 *
        inner ℂ (e (P s.toNNReal f) x) (e (P s.toNNReal g) x)).re = _
      have hbr := integral_re hi
      simp only [RCLike.re_eq_complex_re] at hbr
      rw [← hbr]
      apply integral_congr_ae
      filter_upwards with x
      have hinner (v w : Lp ℂ 2 (reducedLaw Q)) : inner ℝ v w = (inner ℂ v w).re := by
        rw [L2.inner_def, L2.inner_def]
        exact integral_re (L2.integrable_inner (𝕜 := ℂ) v w)
      simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hinner]
    rw [hreal, ← integral_const_mul]
    convert hh using 1
    congr 1
    ext x
    ring
  have hb (s : ℝ) (_hs : 0 < s) :
      2 * (B s).re + (K⁻¹ / 2) * D s ≤ (2 * A) * M s := by
    have hh := clock_error_expected_cutoff_energy Q U O hO hcO hOU
      (hP.map_generator hfg s.toNNReal) (hG s) hφ
    change (K⁻¹ / 4) * D s ≤ -(B s).re + A * M s at hh
    linarith only [hh]
  have hi := clock_integrated_dissipation hEc
    (continuous_const.mul (Complex.continuous_re.comp hBc)) hDc hMc ht hder hb
  have hE0 : E 0 = ∫ x in closure O, φ x ^ 2 * ‖e f x‖ ^ 2 := by
    simp only [E, Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply]
  rw [hE0] at hi
  convert hi using 1 <;> dsimp only [E, D, M, A] <;> congr 1 <;> ring

/-- The actual smooth clock starts with zero conditional error throughout
the retained region. Its interior cutoff energy is generated only by the
cutoff-gradient error, with the actual continuous gradient orbit. -/
private theorem clock_actual_integrated_cutoff_energy {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (U O : Set (Vec d)) (hO : IsOpen O) (hcO : IsCompact (closure O))
    (hOU : closure O ⊆ U) (i : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P s.toNNReal μ) (G s)) ∧
      ∀ (φ : Vec d → ℝ), IsSpatialTest O φ → ∀ (t : ℝ), 0 ≤ t →
      let K := sourceReducedBound D.ellipticity
      let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
      (∫ x in closure O, φ x ^ 2 * ‖e (P t.toNNReal μ) x‖ ^ 2) +
        (K⁻¹ / 2) * (∫ s in (0 : ℝ)..t,
          ∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G s j) x‖ ^ 2) ≤
      (4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) *
        (∫ s in (0 : ℝ)..t,
          ∑ j, ∫ x in closure O, (coordinateDerivative j φ x) ^ 2 *
            ‖e (P s.toNNReal μ) x‖ ^ 2) := by
  obtain ⟨g, hμg⟩ := centeredEquations_clock_initial_generator (i := i) (ζ := 0) hQ hμ
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hμg
  refine ⟨G, hGc, hG, fun φ hφ t ht => ?_⟩
  have hi := clock_error_integrated_cutoff_energy Q U O hO hcO hOU hP hμg hGc hG hφ t ht
  have hz : (∫ x in closure O, φ x ^ 2 * ‖clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x μ)‖ ^ 2) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [clock_projection_error_initial Q U x (hOU hx) μ hμ, norm_zero]
    ring
  dsimp only at hi ⊢
  rw [hz, zero_add] at hi
  exact hi

/-- A bound on the derivatives of an inner cutoff converts the boundary
error term into the energy of an outer cutoff. -/
private theorem clock_cutoff_gradient_energy_le {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] {S O : Set (Vec d)} (hS : IsCompact S)
    {u : Vec d → H} (hu : Continuous u) {φ ψ : Vec d → ℝ}
    (hφ : IsSpatialTest O φ) (hψ : Continuous ψ) {L : ℝ}
    (hb : ∀ x ∈ S, (∑ j, (coordinateDerivative j φ x) ^ 2) ≤ L * ψ x ^ 2) :
    (∑ j, ∫ x in S, (coordinateDerivative j φ x) ^ 2 * ‖u x‖ ^ 2) ≤
      L * (∫ x in S, ψ x ^ 2 * ‖u x‖ ^ 2) := by
  classical
  have hi (j : Fin d) : IntegrableOn
      (fun x => (coordinateDerivative j φ x) ^ 2 * ‖u x‖ ^ 2) S :=
    (((Correctors.isSpatialTest_coordinateDerivative hφ j).1.continuous.pow 2).mul
      (hu.norm.pow 2)).continuousOn.integrableOn_compact hS
  have hc : Continuous (fun x => (∑ j, (coordinateDerivative j φ x) ^ 2) * ‖u x‖ ^ 2) := by
    apply Continuous.mul _ (hu.norm.pow 2)
    apply continuous_finsetSum
    intro j _
    exact (Correctors.isSpatialTest_coordinateDerivative hφ j).1.continuous.pow 2
  have hs : (∑ j, ∫ x in S, (coordinateDerivative j φ x) ^ 2 * ‖u x‖ ^ 2) =
      ∫ x in S, (∑ j, (coordinateDerivative j φ x) ^ 2) * ‖u x‖ ^ 2 := by
    rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
    apply integral_congr_ae
    filter_upwards with x
    exact (Finset.sum_mul _ _ _).symm
  rw [hs, ← integral_const_mul]
  apply setIntegral_mono_on (hc.continuousOn.integrableOn_compact hS)
    ((continuous_const.mul ((hψ.pow 2).mul (hu.norm.pow 2))).continuousOn.integrableOn_compact hS)
    hS.measurableSet
  intro x hx
  simpa only [Pi.mul_apply, Pi.pow_apply, mul_assoc] using
    mul_le_mul_of_nonneg_right (hb x hx) (sq_nonneg ‖u x‖)

/-- The actual conditional clock error satisfies the cutoff recursion used
to obtain arbitrary fixed orders of interior decay. -/
private theorem clock_actual_cutoff_recursion {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (U O : Set (Vec d)) (hO : IsOpen O) (hcO : IsCompact (closure O))
    (hOU : closure O ⊆ U) (i : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    {φ ψ : Vec d → ℝ} (hφ : IsSpatialTest O φ) (hψ : Continuous ψ)
    {L : ℝ} (hb : ∀ x ∈ closure O,
      (∑ j, (coordinateDerivative j φ x) ^ 2) ≤ L * ψ x ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    let K := sourceReducedBound D.ellipticity
    let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
    (∫ x in closure O, φ x ^ 2 * ‖e (P t.toNNReal μ) x‖ ^ 2) ≤
      (4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * L *
        (∫ s in (0 : ℝ)..t, ∫ x in closure O, ψ x ^ 2 * ‖e (P s.toNNReal μ) x‖ ^ 2) := by
  classical
  let K := sourceReducedBound D.ellipticity
  let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  let C := 4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg D.ellipticity, Q.ellipticity_parameter]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hec (v : Lp ℂ 2 (reducedLaw Q)) : Continuous (e v) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hejoint : Continuous (fun p : ℝ × Vec d => e (P p.1.toNNReal μ) p.2) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp
        (continuous_snd.prodMk
          (((hP.2.2.1 μ).comp continuous_real_toNNReal).comp continuous_fst)))
  let M (s : ℝ) := ∑ j, ∫ x in closure O,
    (coordinateDerivative j φ x) ^ 2 * ‖e (P s.toNNReal μ) x‖ ^ 2
  let E (s : ℝ) := ∫ x in closure O, ψ x ^ 2 * ‖e (P s.toNNReal μ) x‖ ^ 2
  have hMc : Continuous M := by
    apply continuous_finsetSum
    intro j _
    exact continuous_parametric_integral_of_continuous
      ((((Correctors.isSpatialTest_coordinateDerivative hφ j).1.continuous.comp
        continuous_snd).pow 2).mul (hejoint.norm.pow 2)) hcO
  have hEc : Continuous E := continuous_parametric_integral_of_continuous
    (((hψ.comp continuous_snd).pow 2).mul (hejoint.norm.pow 2)) hcO
  have hm (s : ℝ) : M s ≤ L * E s :=
    clock_cutoff_gradient_energy_le hcO (hec _) hφ hψ hb
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht
    (hMc.intervalIntegrable 0 t) ((continuous_const.mul hEc).intervalIntegrable 0 t)
    (fun s _ => hm s)
  change (∫ s in (0 : ℝ)..t, M s) ≤ ∫ s in (0 : ℝ)..t, L * E s at hi
  rw [intervalIntegral.integral_const_mul] at hi
  obtain ⟨G, _hGc, _hG, hbound⟩ :=
    clock_actual_integrated_cutoff_energy D Q hQ U O hO hcO hOU i hP μ hμ
  have hdiss : 0 ≤ (K⁻¹ / 2) * (∫ s in (0 : ℝ)..t,
      ∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G s j) x‖ ^ 2) := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg ht
    intro s _
    apply Finset.sum_nonneg
    intro j _
    apply integral_nonneg
    intro x
    positivity
  have hfull := hbound φ hφ t ht
  change (∫ x in closure O, φ x ^ 2 * ‖e (P t.toNNReal μ) x‖ ^ 2) +
    (K⁻¹ / 2) * (∫ s in (0 : ℝ)..t,
      ∑ j, ∫ x in closure O, φ x ^ 2 * ‖e (G s j) x‖ ^ 2) ≤
    C * (∫ s in (0 : ℝ)..t, M s) at hfull
  change (∫ x in closure O, φ x ^ 2 * ‖e (P t.toNNReal μ) x‖ ^ 2) ≤
    C * L * (∫ s in (0 : ℝ)..t, E s)
  calc
    _ ≤ C * (∫ s in (0 : ℝ)..t, M s) := by linarith only [hfull, hdiss]
    _ ≤ C * (L * (∫ s in (0 : ℝ)..t, E s)) := mul_le_mul_of_nonneg_left hi hC
    _ = _ := by ring

/-- A finite chain of Volterra inequalities gains one factor of the time
horizon at each step. No derivative or positivity of the intermediate energies
is needed. -/
private theorem clock_cutoff_chain_le {E : ℕ → ℝ → ℝ} {A T M : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hc : ∀ k, k ≤ n → Continuous (E k))
    (hstep : ∀ k, k < n → ∀ t ∈ Set.Icc 0 T,
      E k t ≤ A * (∫ s in (0 : ℝ)..t, E (k + 1) s))
    (htop : ∀ t ∈ Set.Icc 0 T, E n t ≤ M) :
    ∀ t ∈ Set.Icc 0 T, E 0 t ≤ (A * T) ^ n * M := by
  have hall (m : ℕ) : ∀ k, k + m = n → ∀ t ∈ Set.Icc 0 T,
      E k t ≤ (A * T) ^ m * M := by
    induction m with
    | zero =>
      intro k hk t ht
      have hkn : k = n := by omega
      simpa only [hkn, pow_zero, one_mul] using htop t ht
    | succ m ih =>
      intro k hk t ht
      have hkn : k < n := by omega
      have hnext : ∀ s ∈ Set.Icc 0 T, E (k + 1) s ≤ (A * T) ^ m * M :=
        ih (k + 1) (by omega)
      have hi := intervalIntegral.integral_mono_on (μ := volume) ht.1
        ((hc (k + 1) (by omega)).intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t)
        (fun s hs => hnext s ⟨hs.1, hs.2.trans ht.2⟩)
      have hi' : (∫ s in (0 : ℝ)..t, E (k + 1) s) ≤
          t * ((A * T) ^ m * M) := by
        simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hi
      have hbound : 0 ≤ (A * T) ^ m * M := by positivity
      calc
        E k t ≤ A * (∫ s in (0 : ℝ)..t, E (k + 1) s) := hstep k hkn t ht
        _ ≤ A * (t * ((A * T) ^ m * M)) := mul_le_mul_of_nonneg_left hi' hA
        _ ≤ A * (T * ((A * T) ^ m * M)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht.2 hbound) hA
        _ = (A * T) ^ (m + 1) * M := by rw [pow_succ]; ring
  exact hall n 0 (by omega)

/-- Iterating the actual clock cutoff recursion yields every fixed order of
spatial decay once the cutoff derivatives supply the inverse-radius factor. -/
private theorem clock_actual_cutoff_chain_energy {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (U O : Set (Vec d)) (hO : IsOpen O) (hcO : IsCompact (closure O))
    (hOU : closure O ⊆ U) (i : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (φ : ℕ → Vec d → ℝ) (n : ℕ)
    (hφ : ∀ k, k ≤ n → IsSpatialTest O (φ k)) {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hb : ∀ k, k < n → ∀ x ∈ closure O,
      (∑ j, (coordinateDerivative j (φ k) x) ^ 2) ≤ L * φ (k + 1) x ^ 2)
    (htop : ∀ x ∈ closure O, φ n x ^ 2 ≤ 1) :
    ∀ t ∈ Set.Icc 0 T,
    let K := sourceReducedBound D.ellipticity
    let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
    (∫ x in closure O, φ 0 x ^ 2 * ‖e (P t.toNNReal μ) x‖ ^ 2) ≤
      ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * L * T) ^ n *
        ((volume (closure O)).toReal * ‖μ‖ ^ 2) := by
  classical
  let K := sourceReducedBound D.ellipticity
  let C := 4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹
  let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  let E (k : ℕ) (s : ℝ) :=
    ∫ x in closure O, φ k x ^ 2 * ‖e (P s.toNNReal μ) x‖ ^ 2
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg D.ellipticity, Q.ellipticity_parameter]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hej : Continuous (fun p : ℝ × Vec d => e (P p.1.toNNReal μ) p.2) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp
        (continuous_snd.prodMk
          (((hP.2.2.1 μ).comp continuous_real_toNNReal).comp continuous_fst)))
  have hEc (k : ℕ) (hk : k ≤ n) : Continuous (E k) :=
    continuous_parametric_integral_of_continuous
      ((((hφ k hk).1.continuous.comp continuous_snd).pow 2).mul (hej.norm.pow 2)) hcO
  have he (s : ℝ) (x : Vec d) : ‖e (P s.toNNReal μ) x‖ ≤ ‖μ‖ := by
    have hp := hP.norm_le s.toNNReal
    simp only [complexForceShift, norm_zero, zero_mul,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero] at hp
    calc
      _ ≤ ‖P s.toNNReal μ‖ := (clock_projection_error_norm_le Q U _).trans_eq
        (norm_complexTranslation _ _ _ _)
      _ ≤ ‖μ‖ := ((P s.toNNReal).le_opNorm μ).trans
        ((mul_le_mul_of_nonneg_right hp (norm_nonneg μ)).trans_eq (one_mul _))
  have hterminal (t : ℝ) (_ht : t ∈ Set.Icc 0 T) :
      E n t ≤ (volume (closure O)).toReal * ‖μ‖ ^ 2 := by
    have hxcont : Continuous (fun x => φ n x ^ 2 * ‖e (P t.toNNReal μ) x‖ ^ 2) :=
      ((hφ n le_rfl).1.continuous.pow 2).mul
        ((hej.comp (continuous_const.prodMk continuous_id)).norm.pow 2)
    calc
      E n t ≤ ∫ _x in closure O, ‖μ‖ ^ 2 :=
        setIntegral_mono_on (hxcont.continuousOn.integrableOn_compact hcO)
          (integrableOn_const hcO.measure_ne_top) hcO.measurableSet (fun x hx => by
            have hh := mul_le_mul (htop x hx)
              (pow_le_pow_left₀ (norm_nonneg _) (he t x) 2) (sq_nonneg _) zero_le_one
            simpa only [one_mul] using hh)
      _ = _ := by
        simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
        rfl
  apply clock_cutoff_chain_le (E := E) (mul_nonneg hC hL) hT
    (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) hEc
    (fun k hk t ht => clock_actual_cutoff_recursion D Q hQ U O hO hcO hOU i hP μ hμ
      (hφ k (by omega)) (hφ (k + 1) (by omega)).1.continuous (hb k hk) t ht.1)
    hterminal

/-- The same cutoff chain controls the time integral of the actual gradient
error. The gradient is obtained from the actual clock generator domain. -/
private theorem clock_actual_cutoff_chain_dissipation {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (U O : Set (Vec d)) (hO : IsOpen O) (hcO : IsCompact (closure O))
    (hOU : closure O ⊆ U) (i : Fin d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (φ : ℕ → Vec d → ℝ) (n : ℕ)
    (hφ : ∀ k, k ≤ n + 1 → IsSpatialTest O (φ k)) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ k, k < n + 1 → ∀ x ∈ closure O,
      (∑ j, (coordinateDerivative j (φ k) x) ^ 2) ≤ L * φ (k + 1) x ^ 2)
    (htop : ∀ x ∈ closure O, φ (n + 1) x ^ 2 ≤ 1) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P s.toNNReal μ) (G s)) ∧
      ∀ T : ℝ, 0 ≤ T →
      let K := sourceReducedBound D.ellipticity
      let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
      (K⁻¹ / 2) * (∫ s in (0 : ℝ)..T,
        ∑ j, ∫ x in closure O, φ 0 x ^ 2 * ‖e (G s j) x‖ ^ 2) ≤
        ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * L * T) ^ (n + 1) *
          ((volume (closure O)).toReal * ‖μ‖ ^ 2) := by
  classical
  obtain ⟨G, hGc, hG, hfull⟩ :=
    clock_actual_integrated_cutoff_energy D Q hQ U O hO hcO hOU i hP μ hμ
  refine ⟨G, hGc, hG, ?_⟩
  intro T hT
  let K := sourceReducedBound D.ellipticity
  let C := 4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹
  let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  let M (s : ℝ) := ∑ j, ∫ x in closure O,
    (coordinateDerivative j (φ 0) x) ^ 2 * ‖e (P s.toNNReal μ) x‖ ^ 2
  let E (s : ℝ) := ∫ x in closure O, φ 1 x ^ 2 * ‖e (P s.toNNReal μ) x‖ ^ 2
  let H := (C * L * T) ^ n * ((volume (closure O)).toReal * ‖μ‖ ^ 2)
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg D.ellipticity, Q.ellipticity_parameter]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hec (v : Lp ℂ 2 (reducedLaw Q)) : Continuous (e v) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hej : Continuous (fun p : ℝ × Vec d => e (P p.1.toNNReal μ) p.2) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp
        (continuous_snd.prodMk
          (((hP.2.2.1 μ).comp continuous_real_toNNReal).comp continuous_fst)))
  have hMc : Continuous M := by
    apply continuous_finsetSum
    intro j _
    exact continuous_parametric_integral_of_continuous
      ((((Correctors.isSpatialTest_coordinateDerivative (hφ 0 (by omega)) j).1.continuous.comp
        continuous_snd).pow 2).mul (hej.norm.pow 2)) hcO
  have hEc : Continuous E := continuous_parametric_integral_of_continuous
    (((((hφ 1 (by omega)).1.continuous).comp continuous_snd).pow 2).mul
      (hej.norm.pow 2)) hcO
  have hstep (s : ℝ) : M s ≤ L * E s :=
    clock_cutoff_gradient_energy_le hcO (hec _) (hφ 0 (by omega))
      (hφ 1 (by omega)).1.continuous (hb 0 (by omega))
  have hchain (s : ℝ) (hs : s ∈ Set.Icc 0 T) : E s ≤ H := by
    exact clock_actual_cutoff_chain_energy D Q hQ U O hO hcO hOU i hP μ hμ
      (fun k => φ (k + 1)) n (fun k hk => hφ (k + 1) (by omega)) hL hT
      (fun k hk => hb (k + 1) (by omega)) htop s hs
  have hiM := intervalIntegral.integral_mono_on (μ := volume) hT
    (hMc.intervalIntegrable 0 T) ((continuous_const.mul hEc).intervalIntegrable 0 T)
    (fun s _ => hstep s)
  change (∫ s in (0 : ℝ)..T, M s) ≤ ∫ s in (0 : ℝ)..T, L * E s at hiM
  rw [intervalIntegral.integral_const_mul] at hiM
  have hiE := intervalIntegral.integral_mono_on (μ := volume) hT
    (hEc.intervalIntegrable 0 T) (continuous_const.intervalIntegrable 0 T)
    hchain
  change (∫ s in (0 : ℝ)..T, E s) ≤ ∫ _s in (0 : ℝ)..T, H at hiE
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hiE
  have hi := hfull (φ 0) (hφ 0 (by omega)) T hT
  have hEnonneg : 0 ≤ ∫ x in closure O, φ 0 x ^ 2 * ‖e (P T.toNNReal μ) x‖ ^ 2 :=
    integral_nonneg (fun x => by positivity)
  change (∫ x in closure O, φ 0 x ^ 2 * ‖e (P T.toNNReal μ) x‖ ^ 2) +
    (K⁻¹ / 2) * (∫ s in (0 : ℝ)..T,
      ∑ j, ∫ x in closure O, φ 0 x ^ 2 * ‖e (G s j) x‖ ^ 2) ≤
    C * (∫ s in (0 : ℝ)..T, M s) at hi
  calc
    _ ≤ C * (∫ s in (0 : ℝ)..T, M s) := by linarith only [hi, hEnonneg]
    _ ≤ C * (L * (∫ s in (0 : ℝ)..T, E s)) := mul_le_mul_of_nonneg_left hiM hC
    _ ≤ C * (L * (T * H)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hiE hL) hC
    _ = _ := by dsimp [H]; rw [pow_succ]; ring

private theorem clock_continuous_euclideanNorm {d : ℕ} :
    Continuous (fun x : Vec d => euclideanNorm x) := by
  apply Real.continuous_sqrt.comp
  change Continuous (fun x : Vec d => ∑ k : Fin d, x k * x k)
  apply continuous_finsetSum
  intro k _
  exact (continuous_apply k).mul (continuous_apply k)

/-- Compactness of Euclidean coordinate balls, without importing the
parabolic prescribed-gradient implementation. -/
private theorem clock_isCompact_closure_originBall (d : ℕ) (R : ℝ) :
    IsCompact (closure (External.AKM.originBall d R)) := by
  let F : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  have hc : IsCompact (F '' Metric.closedBall 0 R) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R).image
      (PiLp.continuous_ofLp 2 _)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  refine ⟨WithLp.toLp 2 x, ?_, rfl⟩
  change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) - 0‖ ≤ R
  rw [sub_zero, ← TimeChange.euclideanNorm_eq_norm_toLp]
  exact le_of_lt hx

/-- A finite family of Euclidean cutoffs with a uniform derivative comparison.
The outer support grows geometrically, while the derivative factor uses only
its innermost radius. -/
private theorem clock_exists_nested_cutoffs (d : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
      ∃ φ : ℕ → Vec d → ℝ,
        (∀ k, k ≤ n → IsSpatialTest
          (External.AKM.originBall d (8 * ((2 : ℝ) ^ n * R))) (φ k)) ∧
        (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧
        (∀ x ∈ External.AKM.originBall d (2 * R), φ 0 x = 1) ∧
        ∀ k, k < n → ∀ x,
          (∑ j, (coordinateDerivative j (φ k) x) ^ 2) ≤
            (B / R) ^ 2 * φ (k + 1) x ^ 2 := by
  obtain ⟨χ, B, hB, hχ, hχb, hχ1, hD⟩ :=
    Correctors.exists_nonnegative_reference_spatial_cutoff d
  refine ⟨B, hB, ?_⟩
  intro R hR n
  let r (k : ℕ) := (2 : ℝ) ^ k * R
  let φ (k : ℕ) (x : Vec d) := χ ((2 * r k)⁻¹ • x)
  have hr (k : ℕ) : 0 < r k := mul_pos (by positivity) hR
  have hscale (k : ℕ) := Correctors.rescale_reference_spatial_cutoff
    (hr k) hχ hχb hχ1 hD
  have htest (k : ℕ) : IsSpatialTest (External.AKM.originBall d (4 * r k)) (φ k) :=
    (hscale k).1
  have hgrad (k : ℕ) (x : Vec d) :
      (∑ j, (coordinateDerivative j (φ k) x) ^ 2) ≤ (B / R) ^ 2 := by
    have hrR : R ≤ r k := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
    have hdiv : B / r k ≤ B / R := div_le_div_of_nonneg_left hB.le hR hrR
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ B / r k) hdiv 2
    have hg := (hscale k).2.2.2 x
    have hg' : (∑ j, (coordinateDerivative j (φ k) x) ^ 2) ≤ (B / r k) ^ 2 := by
      simpa only [euclideanSq, dot, gradient, pow_two] using hg
    exact hg'.trans hpow
  refine ⟨φ, ?_, fun k => (hscale k).2.1, ?_, ?_⟩
  · intro k hk
    refine ⟨(htest k).1, (htest k).2.1, ?_⟩
    intro x hx
    have hx' : euclideanNorm x < 4 * r k := (htest k).2.2 hx
    have hkn : r k ≤ r n := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) hR.le
    change euclideanNorm x < 8 * ((2 : ℝ) ^ n * R)
    change euclideanNorm x < 8 * r n
    nlinarith [hr n]
  · simpa only [φ, r, pow_zero, one_mul] using (hscale 0).2.2.1
  · intro k _hk x
    by_cases hx : x ∈ tsupport (φ k)
    · have hx' : x ∈ External.AKM.originBall d (2 * r (k + 1)) := by
        have hh : euclideanNorm x < 4 * r k := (htest k).2.2 hx
        change euclideanNorm x < 2 * r (k + 1)
        dsimp [r] at hh ⊢
        rw [pow_succ]
        nlinarith
      have hplateau : φ (k + 1) x = 1 := (hscale (k + 1)).2.2.1 x hx'
      rw [hplateau, one_pow, mul_one]
      exact hgrad k x
    · have hz : ∀ j, coordinateDerivative j (φ k) x = 0 := by
        intro j
        unfold coordinateDerivative
        rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
        rfl
      simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
      positivity

/-- The actual clock has arbitrarily high fixed polynomial locality order
in an interior spatial L² norm on every bounded time interval. -/
private theorem clock_actual_interior_energy {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : ℝ), 0 < R → ∀ (n : ℕ) (T : ℝ), 0 ≤ T →
      ∀ t ∈ Set.Icc 0 T,
      let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ n * R))
      let K := sourceReducedBound D.ellipticity
      (∫ x in External.AKM.originBall d (2 * R),
        ‖clockProjectionError Q (closure O)
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
            (P t.toNNReal μ))‖ ^ 2) ≤
        ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ n *
          ((volume (closure O)).toReal * ‖μ‖ ^ 2) := by
  obtain ⟨B, hB, hcut⟩ := clock_exists_nested_cutoffs d
  refine ⟨B, hB, ?_⟩
  intro R hR n T hT t ht
  let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ n * R))
  let S := External.AKM.originBall d (2 * R)
  let e (x : Vec d) := clockProjectionError Q (closure O)
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (P t.toNNReal μ))
  obtain ⟨φ, hφ, hφb, hφ1, hφD⟩ := hcut R hR n
  have hO : IsOpen O := isOpen_lt clock_continuous_euclideanNorm continuous_const
  have hS : IsOpen S := isOpen_lt clock_continuous_euclideanNorm continuous_const
  have hcO : IsCompact (closure O) := clock_isCompact_closure_originBall d _
  have hSO : S ⊆ closure O := by
    intro x hx
    apply subset_closure
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hr : R ≤ (2 : ℝ) ^ n * R := by nlinarith
    change euclideanNorm x < 2 * R at hx
    change euclideanNorm x < 8 * ((2 : ℝ) ^ n * R)
    nlinarith
  have he : Continuous e := (clockProjectionError Q (closure O)).continuous.comp
    ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hweighted : IntegrableOn (fun x => φ 0 x ^ 2 * ‖e x‖ ^ 2) (closure O) :=
    (((hφ 0 (Nat.zero_le n)).1.continuous.pow 2).mul
      (he.norm.pow 2)).continuousOn.integrableOn_compact hcO
  calc
    (∫ x in S, ‖e x‖ ^ 2) = ∫ x in S, φ 0 x ^ 2 * ‖e x‖ ^ 2 := by
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      change ‖e x‖ ^ 2 = φ 0 x ^ 2 * ‖e x‖ ^ 2
      rw [hφ1 x hx, one_pow, one_mul]
    _ ≤ ∫ x in closure O, φ 0 x ^ 2 * ‖e x‖ ^ 2 :=
      setIntegral_mono_set hweighted (ae_of_all _ (fun x => by positivity))
        (ae_of_all _ hSO)
    _ ≤ _ := clock_actual_cutoff_chain_energy D Q hQ (closure O) O hO hcO
      (fun _ hx => hx) i hP μ hμ φ n hφ (sq_nonneg _) hT
      (fun k hk x _hx => hφD k hk x)
      (fun x _hx => by
        have h := hφb n x
        exact pow_le_one₀ h.1 h.2) t ht

/-- Restricting a space-time energy to a compact interior plateau decreases
its time integral. -/
private theorem clock_interior_cutoff_dissipation_le {d : ℕ} {H : Type*}
    [NormedAddCommGroup H] {S V : Set (Vec d)} (hcS : IsCompact S)
    (hcV : IsCompact V) (hSV : S ⊆ V) {φ : Vec d → ℝ} (hφ : Continuous φ)
    (hφ1 : ∀ x ∈ S, φ x = 1) {u : ℝ → Vec d → Fin d → H}
    (hu : ∀ j, Continuous (fun p : ℝ × Vec d => u p.1 p.2 j))
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, ∑ j, ∫ x in S, ‖u s x j‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..T, ∑ j, ∫ x in V, φ x ^ 2 * ‖u s x j‖ ^ 2 := by
  have hi : IntervalIntegrable
      (fun s => ∑ j, ∫ x in S, ‖u s x j‖ ^ 2) volume 0 T :=
    (continuous_finsetSum _ (fun j _ =>
      continuous_parametric_integral_of_continuous ((hu j).norm.pow 2) hcS)).intervalIntegrable 0 T
  have ho : IntervalIntegrable
      (fun s => ∑ j, ∫ x in V, φ x ^ 2 * ‖u s x j‖ ^ 2) volume 0 T :=
    (continuous_finsetSum _ (fun j _ =>
      continuous_parametric_integral_of_continuous
        (((hφ.comp continuous_snd).pow 2).mul ((hu j).norm.pow 2)) hcV)).intervalIntegrable 0 T
  apply intervalIntegral.integral_mono_on hT hi ho
  intro s _
  apply Finset.sum_le_sum
  intro j _
  have hec : Continuous (fun x => u s x j) :=
    (hu j).comp (continuous_const.prodMk continuous_id)
  calc
    (∫ x in S, ‖u s x j‖ ^ 2) = ∫ x in S, φ x ^ 2 * ‖u s x j‖ ^ 2 := by
      apply setIntegral_congr_fun hcS.measurableSet
      intro x hx
      change ‖u s x j‖ ^ 2 = φ x ^ 2 * ‖u s x j‖ ^ 2
      rw [hφ1 x hx, one_pow, one_mul]
    _ ≤ _ := setIntegral_mono_set
      (((hφ.pow 2).mul (hec.norm.pow 2)).continuousOn.integrableOn_compact hcV)
      (ae_of_all _ (fun x => by positivity)) (ae_of_all _ hSV)

/-- The interior estimate uses a fixed geometric cutoff constant, chosen
independently of the environment law. -/
private theorem clock_interior_dissipation_from_cutoffs {d : ℕ} (B : ℝ)
    (hcut : ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
      ∃ φ : ℕ → Vec d → ℝ,
        (∀ k, k ≤ n → IsSpatialTest
          (External.AKM.originBall d (8 * ((2 : ℝ) ^ n * R))) (φ k)) ∧
        (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧
        (∀ x ∈ External.AKM.originBall d (2 * R), φ 0 x = 1) ∧
        ∀ k, k < n → ∀ x,
          (∑ j, (coordinateDerivative j (φ k) x) ^ 2) ≤
            (B / R) ^ 2 * φ (k + 1) x ^ 2)
    (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
      let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ (n + 1) * R))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T →
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (∫ s in (0 : ℝ)..T, ∑ j,
          ∫ x in closure (External.AKM.originBall d R),
            ‖clockProjectionError Q (closure O)
              (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
                (G s j))‖ ^ 2) ≤
          ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
            ((volume (closure O)).toReal * ‖μ‖ ^ 2) := by
  classical
  intro R hR n
  let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ (n + 1) * R))
  let S := closure (External.AKM.originBall d R)
  obtain ⟨φ, hφ, hφb, hφ1, hφD⟩ := hcut R hR (n + 1)
  have hO : IsOpen O := isOpen_lt clock_continuous_euclideanNorm continuous_const
  have hcO : IsCompact (closure O) := clock_isCompact_closure_originBall d _
  have hcS : IsCompact S := clock_isCompact_closure_originBall d R
  have hSbound (x : Vec d) (hx : x ∈ S) : euclideanNorm x ≤ R := by
    have hh : S ⊆ {y : Vec d | euclideanNorm y ≤ R} := by
      apply closure_minimal _ (isClosed_le clock_continuous_euclideanNorm continuous_const)
      intro y hy
      change euclideanNorm y < R at hy
      exact hy.le
    exact hh hx
  have hSinner : S ⊆ External.AKM.originBall d (2 * R) := by
    intro x hx
    change euclideanNorm x < 2 * R
    linarith [hSbound x hx]
  have hSO : S ⊆ closure O := by
    intro x hx
    apply subset_closure
    have hp : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hr : R ≤ (2 : ℝ) ^ (n + 1) * R := by nlinarith
    change euclideanNorm x < 8 * ((2 : ℝ) ^ (n + 1) * R)
    nlinarith [hSbound x hx]
  obtain ⟨G, hGc, hG, hbound⟩ := clock_actual_cutoff_chain_dissipation D Q hQ
    (closure O) O hO hcO (fun _ hx => hx) i hP μ hμ φ n hφ (sq_nonneg _)
    (fun k hk x _hx => hφD k hk x)
    (fun x _hx => pow_le_one₀ (hφb (n + 1) x).1 (hφb (n + 1) x).2)
  refine ⟨G, hGc, hG, ?_⟩
  intro T hT
  let e := fun (v : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) => clockProjectionError Q (closure O)
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x v)
  have hej (j : Fin d) : Continuous (fun p : ℝ × Vec d => e (G p.1 j) p.2) :=
    (clockProjectionError Q (closure O)).continuous.comp
      ((continuous_complexTranslation _ _).comp
        (continuous_snd.prodMk
          (((PiLp.continuous_apply 2 _ j).comp hGc).comp continuous_fst)))
  have hmono := clock_interior_cutoff_dissipation_le (u := fun s x j => e (G s j) x) hcS hcO hSO
    (hφ 0 (by omega)).1.continuous (fun x hx => hφ1 x (hSinner hx)) hej hT
  have hK : 0 < sourceReducedBound D.ellipticity := by
    dsimp [sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg D.ellipticity, Q.ellipticity_parameter]
  have hfactor : 0 ≤ (sourceReducedBound D.ellipticity)⁻¹ / 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hmono hfactor
  exact hm.trans (hbound T hT)

/-- Arbitrary fixed locality order for the time-integrated actual clock
weak gradient, on a compact Euclidean interior ball. -/
private theorem clock_actual_interior_dissipation {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
      let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ (n + 1) * R))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T →
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (∫ s in (0 : ℝ)..T, ∑ j,
          ∫ x in closure (External.AKM.originBall d R),
            ‖clockProjectionError Q (closure O)
              (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
                (G s j))‖ ^ 2) ≤
          ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
            ((volume (closure O)).toReal * ‖μ‖ ^ 2) := by
  obtain ⟨B, hB, hcut⟩ := clock_exists_nested_cutoffs d
  exact ⟨B, hB, clock_interior_dissipation_from_cutoffs B hcut D Q hQ i hP μ hμ⟩

/-- The locality constant is structural: it is fixed before the law,
the semigroup, and the actual clock observation. -/
private theorem clock_actual_interior_dissipation_uniform {d : ℕ} (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
      let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ (n + 1) * R))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T →
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (∫ s in (0 : ℝ)..T, ∑ j,
          ∫ x in closure (External.AKM.originBall d R),
            ‖clockProjectionError Q (closure O)
              (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
                (G s j))‖ ^ 2) ≤
          ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
            ((volume (closure O)).toReal * ‖μ‖ ^ 2) := by
  obtain ⟨B, hB, hcut⟩ := clock_exists_nested_cutoffs d
  refine ⟨B, hB, ?_⟩
  intro Q hQ i P hP μ hμ
  exact clock_interior_dissipation_from_cutoffs B hcut D Q hQ i hP μ hμ

/-- Translation preserves literal joint locality when the translated observation
window is contained in the retained window. -/
private theorem clock_translation_local {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W : Set (Vec d)} (x : Vec d)
    (hx : ∀ y ∈ U, x + y ∈ W) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : AEStronglyMeasurable[localSigma U] (⇑f) (reducedLaw Q)) :
    AEStronglyMeasurable[localSigma W]
      (⇑(complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))
      (reducedLaw Q) := by
  obtain ⟨g, hg, heq⟩ := hf
  refine ⟨g ∘ translate x,
    hg.comp_measurable (measurable_translate_localSigma x hx), ?_⟩
  exact (coeFn_complexTranslation _ _ x f).trans
    ((measurePreserving_translate (reducedLaw Q)
      (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae heq)

/-- The complementary projection has the best-approximation bound against
any genuinely joint-local observation. -/
private theorem clock_projection_error_le_local {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d))
    (f v : Lp ℂ 2 (reducedLaw Q))
    (hv : AEStronglyMeasurable[localSigma U] (⇑v) (reducedLaw Q)) :
    ‖clockProjectionError Q U f‖ ≤ ‖f - v‖ := by
  have hz : clockProjectionError Q U v = 0 := by
    change v - clockLocalProjection Q U v = 0
    rw [clockLocalProjection_eq_self Q U v hv, sub_self]
  have heq : clockProjectionError Q U f = clockProjectionError Q U (f - v) := by
    rw [map_sub, hz, sub_zero]
  rw [heq]
  exact clock_projection_error_norm_le Q U (f - v)

/-- A translated local approximation gives an error comparison. This derives
the needed transport inequality without a projection-translation identity. -/
private theorem clock_projection_error_translate_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W : Set (Vec d)} (x : Vec d)
    (hx : ∀ y ∈ U, -x + y ∈ W) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖clockProjectionError Q W f‖ ≤
      ‖clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)‖ := by
  let v := clockLocalProjection Q U
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  have hv : AEStronglyMeasurable[localSigma U] (⇑v) (reducedLaw Q) :=
    lpMeas.aestronglyMeasurable
      (condExpL2 ℂ ℂ (Probability.localSigma_le_borel U)
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f))
  have hb := clock_projection_error_le_local Q W f
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) v)
    (clock_translation_local Q (-x) hx v hv)
  have heq : f - complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) v =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x)
        (clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) := by
    change f - _ = complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f - v)
    rw [map_sub, complexTranslation_neg_cancel]
  rw [heq, norm_complexTranslation] at hb
  exact hb

private theorem clock_primitive_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : Continuous f)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖∫ s in (0 : ℝ)..t, f s‖ ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2 := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    simp only [intervalIntegral.integral_same, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, le_refl]
  let I := ∫ s in (0 : ℝ)..t, ‖f s‖
  let c := I / t
  have hn : IntervalIntegrable (fun s => ‖f s‖) volume 0 t :=
    hf.norm.intervalIntegrable 0 t
  have hs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 t :=
    (hf.norm.pow 2).intervalIntegrable 0 t
  have hexp : (fun s => (‖f s‖ - c) ^ 2) =
      (fun s => (‖f s‖ ^ 2 - (2*c) * ‖f s‖) + c^2) := by
    funext s
    ring
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, (‖f s‖ - c)^2 :=
    intervalIntegral.integral_nonneg ht (fun _ _ => sq_nonneg _)
  rw [hexp, intervalIntegral.integral_add (hs.sub (hn.const_mul _))
    (intervalIntegrable_const), intervalIntegral.integral_sub hs (hn.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hnonneg
  simp only [sub_zero, smul_eq_mul] at hnonneg
  have hid : t * ((∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) - 2*c*I + t*c^2) =
      t * (∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) - I^2 := by
    dsimp only [c]
    field_simp
    ring
  have hsq : I^2 ≤ t * ∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2 := by
    have hh := mul_nonneg ht hnonneg
    change 0 ≤ t * ((∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) - 2*c*I + t*c^2) at hh
    rw [hid] at hh
    exact sub_nonneg.mp hh
  exact (pow_le_pow_left₀ (norm_nonneg _) (intervalIntegral.norm_integral_le_integral_norm ht) 2).trans hsq

/-- Comparison with every translated local approximation can be averaged on
a compact spatial region. The volume factor will cancel the energy volume. -/
private theorem clock_projection_error_spatial_average {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W S : Set (Vec d)} (hcS : IsCompact S)
    (hshift : ∀ x ∈ S, ∀ y ∈ U, -x + y ∈ W)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (volume S).toReal * ‖clockProjectionError Q W f‖ ^ 2 ≤
      ∫ x in S, ‖clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)‖ ^ 2 := by
  have hc : Continuous (fun x => clockProjectionError Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  calc
    _ = ∫ _x in S, ‖clockProjectionError Q W f‖ ^ 2 := by
      simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      rfl
    _ ≤ _ := setIntegral_mono_on
      (integrableOn_const hcS.measure_lt_top.ne)
      ((hc.norm.pow 2).continuousOn.integrableOn_compact hcS) hcS.measurableSet
      (fun x hx => pow_le_pow_left₀ (norm_nonneg _)
        (clock_projection_error_translate_le Q x (hshift x hx) f) 2)

/-- A time primitive of the actual weak gradient inherits the averaged
locality estimate. All integrals are in environment L² before evaluation. -/
private theorem clock_gradient_primitive_locality {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W S : Set (Vec d)} (hcS : IsCompact S)
    (hshift : ∀ x ∈ S, ∀ y ∈ U, -x + y ∈ W)
    (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (hG : Continuous G) (T : ℝ) (hT : 0 ≤ T) :
    (volume S).toReal *
      (∑ j, ‖clockProjectionError Q W (∫ s in (0 : ℝ)..T, G s j)‖ ^ 2) ≤
      T * ∫ s in (0 : ℝ)..T, ∑ j,
        ∫ x in S, ‖clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G s j))‖ ^ 2 := by
  have hGj (j : Fin d) : Continuous (fun s => G s j) :=
    (PiLp.continuous_apply 2 _ j).comp hG
  have he (j : Fin d) : Continuous (fun p : ℝ × Vec d =>
      clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) p.2 (G p.1 j))) :=
    (clockProjectionError Q U).continuous.comp
      ((continuous_complexTranslation _ _).comp
        (continuous_snd.prodMk ((hGj j).comp continuous_fst)))
  have hi (j : Fin d) : Continuous (fun s => ∫ x in S,
      ‖clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G s j))‖ ^ 2) :=
    continuous_parametric_integral_of_continuous ((he j).norm.pow 2) hcS
  rw [Finset.mul_sum, intervalIntegral.integral_finsetSum
    (fun j _ => (hi j).intervalIntegrable 0 T), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hpoint : ∀ s, (volume S).toReal * ‖clockProjectionError Q W (G s j)‖ ^ 2 ≤
      ∫ x in S, ‖clockProjectionError Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G s j))‖ ^ 2 :=
    fun s => clock_projection_error_spatial_average Q hcS hshift (G s j)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hT
    (((clockProjectionError Q W).continuous.comp (hGj j)).norm.pow 2 |>.const_mul
      (volume S).toReal |>.intervalIntegrable 0 T)
    ((hi j).intervalIntegrable 0 T) (fun s _ => hpoint s)
  have hcs := clock_primitive_norm_sq_le
    (fun s => clockProjectionError Q W (G s j))
    ((clockProjectionError Q W).continuous.comp (hGj j)) T hT
  rw [(clockProjectionError Q W).intervalIntegral_comp_comm
    ((hGj j).intervalIntegrable 0 T)] at hcs
  rw [intervalIntegral.integral_const_mul] at hmono
  calc
    _ ≤ (volume S).toReal *
        (T * ∫ s in (0 : ℝ)..T, ‖clockProjectionError Q W (G s j)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs ENNReal.toReal_nonneg
    _ = T * ((volume S).toReal *
        ∫ s in (0 : ℝ)..T, ‖clockProjectionError Q W (G s j)‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hT

/-- A closed Euclidean ball retains all limits of points in the open ball. -/
private theorem clock_norm_le_of_mem_closure_ball {d : ℕ} {R : ℝ} {x : Vec d}
    (hx : x ∈ closure (External.AKM.originBall d R)) : euclideanNorm x ≤ R := by
  have hh : closure (External.AKM.originBall d R) ⊆ {y : Vec d | euclideanNorm y ≤ R} := by
    apply closure_minimal _ (isClosed_le clock_continuous_euclideanNorm continuous_const)
    intro y hy
    change euclideanNorm y < R at hy
    exact hy.le
  exact hh hx

/-- The flux estimate follows from the already derived actual dissipation
bound with the same geometric constant. -/
private theorem clock_primitive_flux_locality_of_dissipation {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (μ : Lp ℂ 2 (reducedLaw Q)) (B : ℝ)
    (hlocal : ∀ (R : ℝ), 0 < R → ∀ n : ℕ,
      let O := External.AKM.originBall d (8 * ((2 : ℝ) ^ (n + 1) * R))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T →
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (∫ s in (0 : ℝ)..T, ∑ j,
          ∫ x in closure (External.AKM.originBall d R),
            ‖clockProjectionError Q (closure O)
              (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
                (G s j))‖ ^ 2) ≤
          ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
            ((volume (closure O)).toReal * ‖μ‖ ^ 2)) :
    ∀ R : ℝ, 0 < R → ∀ n : ℕ,
      let L := 8 * ((2 : ℝ) ^ (n + 1) * R)
      let U := closure (External.AKM.originBall d L)
      let W := closure (External.AKM.originBall d (3 * L))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ j : Fin d,
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (volume (closure (External.AKM.originBall d R))).toReal *
          ‖clockProjectionError Q W
            (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ^ 2 ≤
          (d : ℝ) * K ^ 2 * T *
            ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
              ((volume U).toReal * ‖μ‖ ^ 2) := by
  classical
  intro R hR n
  let L := 8 * ((2 : ℝ) ^ (n + 1) * R)
  let U := closure (External.AKM.originBall d L)
  let W := closure (External.AKM.originBall d (3 * L))
  let S := closure (External.AKM.originBall d R)
  let K := sourceReducedBound D.ellipticity
  have hL : 0 < L := by dsimp [L]; positivity
  have hRL : R ≤ L := by
    have hp : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    dsimp [L]
    nlinarith
  have hshift : ∀ x ∈ S, ∀ y ∈ U, -x + y ∈ W := by
    intro x hx y hy
    apply subset_closure
    change euclideanNorm (-x + y) < 3 * L
    have hxR := clock_norm_le_of_mem_closure_ball hx
    have hyL := clock_norm_le_of_mem_closure_ball hy
    have hn : euclideanNorm (-x) = euclideanNorm x := by
      simp only [euclideanNorm, euclideanSq, dot, Pi.neg_apply, neg_mul_neg]
    have htri := TimeChange.euclideanNorm_add_le (-x) y
    rw [hn] at htri
    linarith
  have hz : (0 : Vec d) ∈ W := by
    apply subset_closure
    change euclideanNorm (0 : Vec d) < 3 * L
    simpa [euclideanNorm, euclideanSq, dot] using (mul_pos (by norm_num : (0 : ℝ) < 3) hL)
  obtain ⟨G, hGc, hG, hbound⟩ := hlocal R hR n
  refine ⟨G, hGc, hG, ?_⟩
  intro T hT j
  let H := fun k => ∫ s in (0 : ℝ)..T, G s k
  have hp := clock_gradient_primitive_locality Q (U := U) (W := W)
    (clock_isCompact_closure_originBall d R) hshift G hGc T hT
  have hf := clock_projection_error_physical_flux Q W H 0 hz j
  simp only [complexTranslation_zero] at hf
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg D.ellipticity, Q.ellipticity_parameter]
  have hc : 0 ≤ K⁻¹ / 2 := by positivity
  have hv : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
  have hdK : 0 ≤ (d : ℝ) * K ^ 2 := by positivity
  have hp' := mul_le_mul_of_nonneg_left hp hc
  have hf' := mul_le_mul_of_nonneg_left hf (mul_nonneg hc hv)
  have hb := mul_le_mul_of_nonneg_left (hbound T hT)
    (mul_nonneg hdK hT)
  change (K⁻¹ / 2) * (volume S).toReal *
    ‖clockProjectionError Q W (clockPhysicalFlux Q H 0 j)‖ ^ 2 ≤ _
  calc
    _ ≤ (K⁻¹ / 2) * (volume S).toReal *
        ((d : ℝ) * K ^ 2 * ∑ k, ‖clockProjectionError Q W (H k)‖ ^ 2) := hf'
    _ = ((d : ℝ) * K ^ 2) *
        ((K⁻¹ / 2) * ((volume S).toReal * ∑ k, ‖clockProjectionError Q W (H k)‖ ^ 2)) := by ring
    _ ≤ ((d : ℝ) * K ^ 2) *
        ((K⁻¹ / 2) * (T * ∫ s in (0 : ℝ)..T, ∑ k, ∫ x in S,
          ‖clockProjectionError Q U
            (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G s k))‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hp' hdK
    _ = ((d : ℝ) * K ^ 2 * T) * ((K⁻¹ / 2) *
        ∫ s in (0 : ℝ)..T, ∑ k, ∫ x in S, ‖clockProjectionError Q U
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G s k))‖ ^ 2) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using hb

/-- Integrated weak flux is quantitatively local at the origin. The local
approximation is taken in the actual joint coefficient-clock sigma algebra. -/
private theorem clock_actual_primitive_flux_locality {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 0 < R → ∀ n : ℕ,
      let L := 8 * ((2 : ℝ) ^ (n + 1) * R)
      let U := closure (External.AKM.originBall d L)
      let W := closure (External.AKM.originBall d (3 * L))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ j : Fin d,
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (volume (closure (External.AKM.originBall d R))).toReal *
          ‖clockProjectionError Q W
            (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ^ 2 ≤
          (d : ℝ) * K ^ 2 * T *
            ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
              ((volume U).toReal * ‖μ‖ ^ 2) := by
  obtain ⟨B, hB, hlocal⟩ := clock_actual_interior_dissipation D Q hQ i hP μ hμ
  exact ⟨B, hB, clock_primitive_flux_locality_of_dissipation D Q μ B hlocal⟩

/-- A single structural constant controls integrated flux locality for all
admissible environment laws and all actual unforced clock evolutions. -/
private theorem clock_actual_primitive_flux_locality_uniform {d : ℕ} (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ R : ℝ, 0 < R → ∀ n : ℕ,
      let L := 8 * ((2 : ℝ) ^ (n + 1) * R)
      let U := closure (External.AKM.originBall d L)
      let W := closure (External.AKM.originBall d (3 * L))
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ j : Fin d,
        let K := sourceReducedBound D.ellipticity
        (K⁻¹ / 2) * (volume (closure (External.AKM.originBall d R))).toReal *
          ‖clockProjectionError Q W
            (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ^ 2 ≤
          (d : ℝ) * K ^ 2 * T *
            ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
              ((volume U).toReal * ‖μ‖ ^ 2) := by
  obtain ⟨B, hB, hlocal⟩ := clock_actual_interior_dissipation_uniform D
  refine ⟨B, hB, ?_⟩
  intro Q hQ i P hP μ hμ
  exact clock_primitive_flux_locality_of_dissipation D Q μ B
    (hlocal Q hQ i P hP μ hμ)

/-- The fixed-point physical flux commutes with time integration as a
bounded linear operation on the actual environment L² gradient components. -/
private theorem clock_physical_flux_primitive {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (hG : Continuous G) (x : Vec d) (j : Fin d) (a b : ℝ) :
    clockPhysicalFlux Q (fun k => ∫ s in a..b, G s k) x j =
      ∫ s in a..b, clockPhysicalFlux Q (fun k => G s k) x j := by
  classical
  have hc (k : Fin d) : Continuous (fun s =>
      clockCoefficientMulAt Q x j k
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (G s k))) :=
    (clockCoefficientMulAt Q x j k).continuous.comp
      ((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).continuous.comp
        ((PiLp.continuous_apply 2 _ k).comp hG))
  unfold clockPhysicalFlux
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hc k).intervalIntegrable a b)]
  apply Finset.sum_congr rfl
  intro k _
  let T := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
  have hti : IntervalIntegrable (fun s => T (G s k)) volume a b :=
    (T.continuous.comp ((PiLp.continuous_apply 2 _ k).comp hG)).intervalIntegrable a b
  calc
    _ = clockCoefficientMulAt Q x j k (∫ s in a..b, T (G s k)) := by
      rw [T.intervalIntegral_comp_comm (fun s => G s k)]
    _ = _ := ((clockCoefficientMulAt Q x j k).intervalIntegral_comp_comm hti).symm


/-- Literal joint finite range applies to arbitrary local L² observations,
including local projections of the integrated physical flux. -/
private theorem clock_joint_local_independent {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W : Set (Vec d)}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hsep : ∃ s : ℝ, r < s ∧ ∀ x ∈ U, ∀ y ∈ W, s ≤ euclideanNorm (x - y))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hf : AEStronglyMeasurable[localSigma U] (⇑f) (reducedLaw Q))
    (hg : AEStronglyMeasurable[localSigma W] (⇑g) (reducedLaw Q)) :
    ProbabilityTheory.IndepFun (⇑f) (⇑g) (reducedLaw Q) := by
  obtain ⟨F, hF, heF⟩ := hf
  obtain ⟨G, hG, heG⟩ := hg
  have hi := reducedLaw_hasFiniteRange Q U W hU hW hsep
  have hiFG : ProbabilityTheory.IndepFun F G (reducedLaw Q) := by
    change ProbabilityTheory.Indep _ _ _
    rw [ProbabilityTheory.Indep_iff] at hi ⊢
    intro s t hs ht
    exact hi s t (hF.measurable.comap_le s hs) (hG.measurable.comap_le t ht)
  exact hiFG.congr heF.symm heG.symm

/-- Centered local observations in separated retained regions are orthogonal
in the actual complex environment L² space. -/
private theorem clock_joint_local_inner_zero {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W : Set (Vec d)}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hsep : ∃ s : ℝ, r < s ∧ ∀ x ∈ U, ∀ y ∈ W, s ≤ euclideanNorm (x - y))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hf : AEStronglyMeasurable[localSigma U] (⇑f) (reducedLaw Q))
    (hg : AEStronglyMeasurable[localSigma W] (⇑g) (reducedLaw Q))
    (hf0 : (∫ ω, f ω ∂reducedLaw Q) = 0) :
    inner ℂ f g = 0 := by
  have hi := (clock_joint_local_independent Q hU hW hsep f g hf hg).comp
    (continuous_star : Continuous (star : ℂ → ℂ)).measurable measurable_id
  rw [L2.inner_def]
  simp only [RCLike.inner_apply']
  change (∫ ω, star (f ω) * g ω ∂reducedLaw Q) = 0
  have hp := hi.integral_fun_mul_eq_mul_integral (Lp.aestronglyMeasurable f).star
    (Lp.aestronglyMeasurable g)
  change (∫ ω, star (f ω) * g ω ∂reducedLaw Q) =
    (∫ ω, star (f ω) ∂reducedLaw Q) * (∫ ω, g ω ∂reducedLaw Q) at hp
  have hs : (∫ ω, star (f ω) ∂reducedLaw Q) =
      star (∫ ω, f ω ∂reducedLaw Q) := by
    simpa only [starRingEnd_apply] using
      (integral_conj (f := fun ω => f ω) (μ := reducedLaw Q))
  rw [hp, hs, hf0, star_zero, zero_mul]

/-- Conditioning on the retained joint fields preserves the actual mean. -/
private theorem clock_local_projection_integral {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, clockLocalProjection Q U f ω ∂reducedLaw Q) =
      ∫ ω, f ω ∂reducedLaw Q := by
  let := reducedLaw_probability Q
  rw [integral_congr_ae (clockLocalProjection_ae_condExp Q U f),
    integral_condExp (Probability.localSigma_le_borel U)]

/-- The covariance between separated observations is bounded by their two
actual joint-local projection errors. -/
private theorem clock_covariance_le_projection_errors {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {U W : Set (Vec d)}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hsep : ∃ s : ℝ, r < s ∧ ∀ x ∈ U, ∀ y ∈ W, s ≤ euclideanNorm (x - y))
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hf0 : (∫ ω, f ω ∂reducedLaw Q) = 0) :
    ‖inner ℂ f g‖ ≤
      ‖clockProjectionError Q U f‖ * ‖g‖ + ‖f‖ * ‖clockProjectionError Q W g‖ := by
  have hf : AEStronglyMeasurable[localSigma U]
      (⇑(clockLocalProjection Q U f)) (reducedLaw Q) :=
    lpMeas.aestronglyMeasurable (condExpL2 ℂ ℂ (Probability.localSigma_le_borel U) f)
  have hg : AEStronglyMeasurable[localSigma W]
      (⇑(clockLocalProjection Q W g)) (reducedLaw Q) :=
    lpMeas.aestronglyMeasurable (condExpL2 ℂ ℂ (Probability.localSigma_le_borel W) g)
  have hzero := clock_joint_local_inner_zero Q hU hW hsep
    (clockLocalProjection Q U f) (clockLocalProjection Q W g) hf hg
    ((clock_local_projection_integral Q U f).trans hf0)
  have heq : inner ℂ f g =
      inner ℂ (clockProjectionError Q U f) g +
        inner ℂ (clockLocalProjection Q U f) (clockProjectionError Q W g) := by
    change inner ℂ f g = inner ℂ (f - clockLocalProjection Q U f) g +
      inner ℂ (clockLocalProjection Q U f) (g - clockLocalProjection Q W g)
    rw [inner_sub_left, inner_sub_right, hzero]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right
        (clockLocalProjection_norm_le Q U f) (norm_nonneg _)) _))

private theorem clock_euclideanNorm_neg {d : ℕ} (x : Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  simp only [euclideanNorm, euclideanSq, dot, Pi.neg_apply, neg_mul_neg]

private theorem clock_euclideanNorm_sub_comm {d : ℕ} (x y : Vec d) :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  rw [← neg_sub y x, clock_euclideanNorm_neg]

/-- Widely separated translates of a centered observation have covariance
controlled by its actual error of conditioning on one Euclidean ball. -/
private theorem clock_covariance_le_local_error {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (R : ℝ) (x : Vec d)
    (hsep : 2 * R + r < euclideanNorm x)
    (f : Lp ℂ 2 (reducedLaw Q))
    (hf0 : (∫ ω, f ω ∂reducedLaw Q) = 0) :
    ‖inner ℂ f (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)‖ ≤
      2 * ‖f‖ * ‖clockProjectionError Q
        (closure (External.AKM.originBall d R)) f‖ := by
  let U := closure (External.AKM.originBall d R)
  let W := (fun y : Vec d => -x + y) ⁻¹' U
  have hW : IsClosed W := isClosed_closure.preimage
    (continuous_const.add continuous_id)
  have hdist : ∀ u ∈ U, ∀ v ∈ W,
      euclideanNorm x - 2 * R ≤ euclideanNorm (u - v) := by
    intro u hu v hv
    have huR := clock_norm_le_of_mem_closure_ball hu
    have hvR := clock_norm_le_of_mem_closure_ball hv
    have hid : x = u + ((v - u) + (x - v)) := by abel
    have ht₁ := TimeChange.euclideanNorm_add_le u ((v - u) + (x - v))
    have ht₂ := TimeChange.euclideanNorm_add_le (v - u) (x - v)
    rw [← hid] at ht₁
    rw [clock_euclideanNorm_sub_comm v u] at ht₂
    have hn : euclideanNorm (x - v) = euclideanNorm (-x + v) := by
      rw [clock_euclideanNorm_sub_comm]
      congr 1
      abel
    rw [hn] at ht₂
    linarith
  have hs : ∃ s : ℝ, r < s ∧ ∀ u ∈ U, ∀ v ∈ W,
      s ≤ euclideanNorm (u - v) := by
    refine ⟨(r + (euclideanNorm x - 2 * R)) / 2, by linarith, ?_⟩
    intro u hu v hv
    linarith [hdist u hu v hv]
  let g := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  have hb := clock_covariance_le_projection_errors Q isClosed_closure.measurableSet
    hW.measurableSet hs f g hf0
  have he := clock_projection_error_translate_le Q (U := U) (W := W) (-x)
    (fun y hy => by change -x + (-(-x) + y) ∈ U; simpa only [neg_neg, neg_add_cancel_left] using hy) g
  have hc : complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g = f :=
    complexTranslation_neg_cancel _ _ x f
  rw [hc] at he
  have hn : ‖g‖ = ‖f‖ := norm_complexTranslation _ _ x f
  rw [hn] at hb
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg f)])

/-- Euclidean retained windows scale literally on the coordinate carrier. -/
private theorem clock_originBall_smul (d : ℕ) (c R : ℝ) (hc : 0 < c) :
    External.AKM.originBall d (c * R) = c • External.AKM.originBall d R := by
  ext x
  constructor
  · intro hx
    refine ⟨c⁻¹ • x, ?_, smul_inv_smul₀ hc.ne' x⟩
    change euclideanNorm (c⁻¹ • x) < R
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    exact (inv_mul_lt_iff₀ hc).mpr hx
  · rintro ⟨y, hy, rfl⟩
    change euclideanNorm (c • y) < c * R
    rw [TimeChange.euclideanNorm_smul, abs_of_pos hc]
    exact mul_lt_mul_of_pos_left hy hc

/-- The ratio of the two locality volumes is a structural power of the
radius ratio, with no replacement of the Euclidean balls. -/
private theorem clock_volume_closure_ball_smul (d : ℕ) (c R : ℝ) (hc : 0 < c) :
    (volume (closure (External.AKM.originBall d (c * R)))).toReal =
      c ^ d * (volume (closure (External.AKM.originBall d R))).toReal := by
  rw [clock_originBall_smul d c R hc, closure_smul₀,
    Measure.addHaar_smul_of_nonneg volume hc.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc.le _)]
  simp only [Module.finrank_pi, Fintype.card_fin]

private theorem clock_volume_closure_ball_pos (d : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < (volume (closure (External.AKM.originBall d R))).toReal := by
  have ho : IsOpen (External.AKM.originBall d R) :=
    clock_continuous_euclideanNorm.isOpen_preimage _ isOpen_Iio
  have hn : (External.AKM.originBall d R).Nonempty := by
    refine ⟨0, ?_⟩
    simpa only [External.AKM.originBall, Set.mem_ofPred_eq, euclideanNorm, euclideanSq,
      dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.sqrt_zero] using hR
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((ho.measure_pos volume hn).trans_le (measure_mono subset_closure))
  · exact (clock_isCompact_closure_originBall d R).measure_ne_top

/-- The locality estimate concerns the actual gradient orbit: uniqueness
identifies every cutoff construction with any continuous chosen orbit. -/
private theorem clock_actual_fixed_gradient_primitive_flux_locality {d : ℕ}
    (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))),
        Continuous G →
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) →
      ∀ R : ℝ, 0 < R → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → ∀ j : Fin d,
        let K := sourceReducedBound D.ellipticity
        let c := 8 * (2 : ℝ) ^ (n + 1)
        ‖clockProjectionError Q (closure (External.AKM.originBall d (3 * (c * R))))
            (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ^ 2 ≤
          2 * K * ((d : ℝ) * K ^ 2 * T *
            ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
              (c ^ d * ‖μ‖ ^ 2)) := by
  classical
  obtain ⟨B, hB, hb⟩ := clock_actual_primitive_flux_locality_uniform D
  refine ⟨B, hB, ?_⟩
  intro Q hQ i P hP μ hμ G _hGc hG R hR n T hT j
  obtain ⟨G', _, hG', hh⟩ := hb Q hQ i P hP μ hμ R hR n
  have heq : G' = G := by
    funext s
    apply PiLp.ext
    intro k
    exact congrFun ((hG' s).unique (hG s)) k
  subst G'
  have h := hh T hT j
  let c := 8 * (2 : ℝ) ^ (n + 1)
  let K := sourceReducedBound D.ellipticity
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg D.ellipticity, Q.ellipticity_parameter]
  have hv := clock_volume_closure_ball_pos d hR
  have hvol := clock_volume_closure_ball_smul d c R hc
  have hreshape : 8 * ((2 : ℝ) ^ (n + 1) * R) = c * R := by dsimp [c]; ring
  dsimp only at h
  rw [hreshape] at h
  change (K⁻¹ / 2) * (volume (closure (External.AKM.originBall d R))).toReal *
    ‖clockProjectionError Q (closure (External.AKM.originBall d (3 * (c * R))))
      (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ^ 2 ≤
    (d : ℝ) * K ^ 2 * T *
      ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
        ((volume (closure (External.AKM.originBall d (c * R)))).toReal * ‖μ‖ ^ 2) at h
  rw [hvol] at h
  have hh' := (mul_le_mul_iff_right₀ hv).mp (show
      (volume (closure (External.AKM.originBall d R))).toReal *
        ((K⁻¹ / 2) * ‖clockProjectionError Q
          (closure (External.AKM.originBall d (3 * (c * R))))
          (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ^ 2) ≤
      (volume (closure (External.AKM.originBall d R))).toReal *
        ((d : ℝ) * K ^ 2 * T *
          ((4 * (d : ℝ) * ((d : ℝ) + 1) * K ^ 2 / K⁻¹) * (B / R) ^ 2 * T) ^ (n + 1) *
            (c ^ d * ‖μ‖ ^ 2)) by nlinarith only [h])
  have hi := mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ 2 * K)
  have hcancel : (2 * K) * (K⁻¹ / 2) = 1 := by field_simp
  simp only [← mul_assoc, hcancel, one_mul] at hi
  simpa only [c, K, ← mul_assoc] using hi

/-- Conditional projection supplies an actual joint-local representative. -/
private theorem clock_projection_isLocal {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ρ : ℝ) (f : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexLocalObservation Q ρ
      (clockLocalProjection Q {x : Vec d | euclideanNorm x < ρ} f) := by
  have ha := aestronglyMeasurable_condExpL2 (𝕜 := ℂ)
    (Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}) f
  exact ⟨ha.mk _, ha.stronglyMeasurable_mk.measurable, ha.ae_eq_mk.symm⟩

/-- Finite-range Gaussian averaging extends to local L² observations by density.
The constant is independent of any pointwise bound used in the approximation. -/
private theorem clock_local_gaussian_l2_bound (d : ℕ) (Λ r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ}
      (Q : EnvironmentLaw d Λ r₀), HasFiniteRange r (reducedLaw Q) →
      ∀ (ρ : ℝ) (N : ℕ) [NeZero N], r < (N : ℝ) - 1 - 2 * ρ →
      ∀ f : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ f →
      (∫ ω, f ω ∂reducedLaw Q) = 0 → ∀ s : ℝ, ∀ hs : 0 < s,
      ‖gaussianAverage hd Q s hs f‖ ≤
        C * (N : ℝ) ^ d * ‖f‖ * s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := UnitInitialization.exists_gaussian_average_local_L2_bound d Λ r
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr ρ N _ hgap f hlocal hmean s hs
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let U : Set (Vec d) := {x | euclideanNorm x < ρ}
  let T := (centeredComplexLpCLM Q).comp (clockLocalProjection Q U)
  let A := homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
  have hA (v : Lp ℂ 2 (reducedLaw Q)) : A v = gaussianAverage hd Q s hs v := rfl
  have hT (v : Lp ℂ 2 (reducedLaw Q)) :
      T v = centeredComplexLp Q (clockLocalProjection Q U v) := by
    simp only [T, ContinuousLinearMap.comp_apply, centeredComplexLpCLM_apply]
  have hall (v : Lp ℂ 2 (reducedLaw Q)) :
      ‖A (T v)‖ ≤ C * (N : ℝ) ^ d * ‖T v‖ * s ^ (-(d : ℝ) / 4) := by
    refine (Lp.simpleFunc.denseRange (E := ℂ) (μ := reducedLaw Q)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).induction_on v ?_ ?_
    · exact isClosed_le ((A.continuous.comp T.continuous).norm)
        ((continuous_const.mul T.continuous.norm).mul continuous_const)
    · intro g
      obtain ⟨B, hgB⟩ := (Lp.simpleFunc.toSimpleFunc g).exists_forall_norm_le
      have hg : ∀ᵐ ω ∂reducedLaw Q, ‖(g : Lp ℂ 2 (reducedLaw Q)) ω‖ ≤ max 0 B := by
        filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun g] with ω he
        rw [← he]
        exact (hgB ω).trans (le_max_right _ _)
      have hp : ∀ᵐ ω ∂reducedLaw Q,
          ‖clockLocalProjection Q U (g : Lp ℂ 2 (reducedLaw Q)) ω‖ ≤ max 0 B := by
        filter_upwards [clockLocalProjection_ae_condExp Q U (g : Lp ℂ 2 (reducedLaw Q)),
          ae_bdd_norm_condExp_of_ae_bdd_norm (m := localSigma U) hg] with ω he hb
        exact he ▸ hb
      rw [hA, hT]
      exact hb hd Q hfr ρ N hgap (2 * max 0 B) (by positivity) _
        (isComplexLocal_centered Q (clock_projection_isLocal Q ρ _))
        (UnitInitialization.ae_norm_centered_le Q _ hp) (integral_centeredComplexLp Q _) s hs
  have hfix : clockLocalProjection Q U f = f := by
    obtain ⟨g, hg, he⟩ := hlocal
    exact clockLocalProjection_eq_self Q U f
      (hg.stronglyMeasurable.aestronglyMeasurable.congr he)
  have hTf : T f = f := by
    rw [hT, hfix, centeredComplexLp, hmean, map_zero, sub_zero]
  simpa only [hTf, hA] using hall f

/-- Summing local approximants with geometric errors preserves the full
Gaussian concentration exponent. All numerical data precede the law. -/
private theorem clock_gaussian_dyadic_l2_approximants
    (d : ℕ) (Λ r R B L q : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hq : 0 ≤ q) (hq1 : q < 1) (hqd : (2 : ℝ) ^ d * q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ}
      (Q : EnvironmentLaw d Λ r₀), HasFiniteRange r (reducedLaw Q) →
      ∀ (H : Lp ℂ 2 (reducedLaw Q)) (K : ℕ → Lp ℂ 2 (reducedLaw Q)),
      ‖K 0‖ ≤ B →
      (∀ n : ℕ, IsComplexLocalObservation Q (R * (2 : ℝ)^n) (K n)) →
      (∀ n, (∫ ω, K n ω ∂reducedLaw Q) = 0) →
      (∀ n, ‖H-K n‖ ≤ L * q^n) → ∀ (s : ℝ) (hs : 0 < s),
      ‖gaussianAverage hd Q s hs H‖ ≤ C * s ^ (-(d : ℝ)/4) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (|r| + 2 * |R| + 4)
  have hMpos : (0 : ℝ) < M := by linarith [abs_nonneg r, abs_nonneg R]
  have hMne : M ≠ 0 := by exact_mod_cast hMpos.ne'
  let N : ℕ → ℕ := fun n => M * 2^n
  let e : ℕ → ℝ := fun n => L * q^n
  let w : ℕ → ℝ := fun n => (N (n+1) : ℝ)^d * (e n + e (n+1))
  have hw : Summable w := by
    have hs := (summable_geometric_of_lt_one (mul_nonneg (by positivity) hq) hqd).mul_left
      ((M : ℝ)^d * (2 : ℝ)^d * L * (1+q))
    convert hs using 1
    ext n
    dsimp only [w, N, e]
    push_cast
    simp only [pow_succ, mul_pow, ← pow_mul]
    rw [Nat.mul_comm n d]
    ring
  obtain ⟨C, hC, hb⟩ := clock_local_gaussian_l2_bound d Λ r
  refine ⟨C * ((M : ℝ)^d * B + ∑' n, w n), ?_, ?_⟩
  · exact mul_nonneg hC (add_nonneg (mul_nonneg (by positivity) hB)
      (tsum_nonneg fun n => by dsimp only [w, e]; positivity))
  intro hd r₀ Q hfr H K hK0 hlocal hmean herr s hs
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let (n : ℕ) : NeZero (N n) := ⟨Nat.mul_ne_zero hMne (pow_ne_zero n (by decide))⟩
  have hgap (n : ℕ) : r < (N n : ℝ) - 1 - 2 * (R * (2 : ℝ)^n) := by
    have ht : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    have hm : 0 < (M : ℝ) - 2*R := by linarith [le_abs_self R, abs_nonneg r]
    have hmul := mul_le_mul_of_nonneg_left ht hm.le
    dsimp only [N]
    push_cast
    nlinarith [le_abs_self r, le_abs_self R, abs_nonneg R]
  let F : ℕ → Lp ℂ 2 (reducedLaw Q)
    | 0 => K 0
    | n+1 => K (n+1) - K n
  let b : ℕ → ℝ
    | 0 => B
    | n+1 => e n + e (n+1)
  have hloc (n : ℕ) : IsComplexLocalObservation Q (R * (2 : ℝ)^n) (F n) := by
    cases n with
    | zero => exact hlocal 0
    | succ n =>
      obtain ⟨g₁, hg₁, he₁⟩ := hlocal (n+1)
      obtain ⟨g₀, hg₀, he₀⟩ := hlocal n
      have hrad : R * (2 : ℝ)^n ≤ R * (2 : ℝ)^(n+1) := by
        apply mul_le_mul_of_nonneg_left _ hR
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]
      have hg₀' : Measurable[localSigma
          {x : Vec d | euclideanNorm x < R * (2 : ℝ)^(n+1)}] g₀ :=
        hg₀.mono (Probability.localSigma_mono (fun x hx => hx.trans_le hrad)) le_rfl
      exact ⟨fun ω => g₁ ω-g₀ ω, hg₁.sub hg₀',
        (he₁.sub he₀).trans (Lp.coeFn_sub _ _).symm⟩
  have hnorm (n : ℕ) : ‖F n‖ ≤ b n := by
    cases n with
    | zero => exact hK0
    | succ n =>
      change ‖K (n+1)-K n‖ ≤ e n + e (n+1)
      have hh := norm_sub_le_norm_sub_add_norm_sub (K (n+1)) H (K n)
      rw [norm_sub_rev (K (n+1)) H] at hh
      exact hh.trans ((add_le_add (herr (n+1)) (herr n)).trans_eq (add_comm _ _))
  have hmeanF (n : ℕ) : (∫ ω, F n ω ∂reducedLaw Q) = 0 := by
    cases n with
    | zero => exact hmean 0
    | succ n =>
      rw [show F (n+1) = K (n+1)-K n from rfl, integral_congr_ae (Lp.coeFn_sub _ _)]
      change (∫ ω, K (n+1) ω-K n ω ∂reducedLaw Q) = 0
      rw [integral_sub ((Lp.memLp (K (n+1))).integrable (by norm_num))
        ((Lp.memLp (K n)).integrable (by norm_num)), hmean, hmean, sub_self]
  have he : Summable e := (summable_geometric_of_lt_one hq hq1).mul_left L
  have hF : HasSum F H := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa only [F, Finset.sum_range_one] using
      UnitInitialization.hasSum_localization_differences K H e he herr
  have hw' : Summable (fun n => (N n : ℝ)^d * b n) := by
    apply (summable_nat_add_iff 1).mp
    exact hw
  let A := homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
  have hA (v : Lp ℂ 2 (reducedLaw Q)) : A v = gaussianAverage hd Q s hs v := rfl
  have hpiece (n : ℕ) : ‖A (F n)‖ ≤
      C * ((N n : ℝ)^d * b n) * s ^ (-(d : ℝ)/4) := by
    rw [hA]
    exact (hb hd Q hfr _ (N n) (hgap n) (F n) (hloc n) (hmeanF n) s hs).trans
      (by
        have hn := mul_le_mul_of_nonneg_left (hnorm n)
          (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg (N n)) d))
        have hn' := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hs.le (-(d : ℝ)/4))
        simpa only [mul_assoc] using hn')
  have hbound := (A.hasSum hF).norm_le_of_bounded
    (((hw'.mul_left C).mul_right (s ^ (-(d : ℝ)/4))).hasSum) hpiece
  have hweight : (∑' n, (N n : ℝ)^d * b n) = (M : ℝ)^d * B + ∑' n, w n := by
    simpa only [Finset.sum_range_one, b, N, Nat.zero_add, pow_zero, Nat.mul_one, w] using
      (hw'.sum_add_tsum_nat_add 1).symm
  rw [tsum_mul_right, tsum_mul_left, hweight, hA] at hbound
  exact hbound

/-- The literal reduced clock has a structural L² bound. -/
private theorem clock_actual_clock_norm_bound {d : ℕ} (D : StructuralData d) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ → ‖μ‖ ≤ M := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨L, lt_of_lt_of_le zero_lt_one hL, ?_⟩
  intro Q μ hμ
  letI := reducedLaw_probability Q
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ L := by
    filter_upwards [hμ, (hb d D.dependenceRange Q).2.2] with ω he hω
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((inv_nonneg.mpr (zero_le_one.trans hL)).trans (hω.2.1 0).1)]
    exact (hω.2.1 0).2
  simpa only [Lp.norm_def] using
    AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp μ).aestronglyMeasurable
      (zero_le_one.trans hL) (p := 2) hbound

/-- Actual primitive-flux projection errors decay to any fixed polynomial
order. The radius multiplier and amplitude are structural, at each fixed time. -/
private theorem clock_actual_flux_polynomial_error {d : ℕ} (D : StructuralData d)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    ∃ R₀ L : ℝ, 0 < R₀ ∧ 0 < L ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))),
        Continuous G →
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) →
      ∀ R : ℝ, 0 < R → ∀ j : Fin d,
        ‖clockProjectionError Q {x : Vec d | euclideanNorm x < R₀ * R}
            (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j)‖ ≤
          L / R^(n+1) := by
  obtain ⟨B, hB, hb⟩ := clock_actual_fixed_gradient_primitive_flux_locality D
  obtain ⟨M, hM, hm⟩ := clock_actual_clock_norm_bound D
  let K := sourceReducedBound D.ellipticity
  let c := 8 * (2 : ℝ)^(n+1)
  let A := 2*K*((d : ℝ)*K^2*T *
    ((4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*B^2*T)^(n+1) * (c^d*M^2))
  have hK : 0 < K := Clock.sourceReducedBound_pos D.one_le_ellipticity
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨4*c, A+1, by positivity, by positivity, ?_⟩
  intro Q hQ i P hP μ hμ G hGc hG R hR j
  let F := clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j
  let U := closure (External.AKM.originBall d (3*(c*R)))
  let W : Set (Vec d) := {x | euclideanNorm x < (4*c)*R}
  have hUW : U ⊆ W := by
    intro x hx
    have hn := clock_norm_le_of_mem_closure_ball hx
    change euclideanNorm x < (4*c)*R
    nlinarith
  have hcomp : ‖clockProjectionError Q W F‖ ≤ ‖clockProjectionError Q U F‖ := by
    have hp := aestronglyMeasurable_condExpL2 (𝕜 := ℂ)
      (Probability.localSigma_le_borel U) F
    have hw := hp.mono (Probability.localSigma_mono hUW)
    exact clock_projection_error_le_local Q W F (clockLocalProjection Q U F) hw
  have hraw := hb Q hQ i P hP μ hμ G hGc hG R hR n T hT j
  change ‖clockProjectionError Q U F‖^2 ≤
    2*K*((d : ℝ)*K^2*T *
      ((4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*(B/R)^2*T)^(n+1) * (c^d*‖μ‖^2)) at hraw
  have hμM : ‖μ‖^2 ≤ M^2 := pow_le_pow_left₀ (norm_nonneg _) (hm Q μ hμ) 2
  have hscale :
      ((4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*(B/R)^2*T)^(n+1) =
      ((4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*B^2*T)^(n+1) / (R^(n+1))^2 := by
    rw [div_pow]
    have he : (4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*(B^2/R^2)*T =
        ((4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*B^2*T)/R^2 := by ring
    rw [he, div_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (n+1)]
  rw [hscale] at hraw
  have hbound : ‖clockProjectionError Q W F‖^2 ≤ A/(R^(n+1))^2 := by
    calc
      _ ≤ ‖clockProjectionError Q U F‖^2 := pow_le_pow_left₀ (norm_nonneg _) hcomp 2
      _ ≤ _ := hraw
      _ ≤ 2*K*((d : ℝ)*K^2*T *
          (((4*(d : ℝ)*((d : ℝ)+1)*K^2/K⁻¹)*B^2*T)^(n+1)/(R^(n+1))^2) *
          (c^d*M^2)) := by gcongr
      _ = _ := by dsimp only [A]; ring
  have hden : 0 < R^(n+1) := pow_pos hR _
  have hsq : A/(R^(n+1))^2 ≤ ((A+1)/R^(n+1))^2 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [sq_nonneg A]
  have hle : ‖clockProjectionError Q W F‖ ≤ (A+1)/R^(n+1) := by
    have hh := hbound.trans hsq
    have hp : 0 ≤ (A+1)/R^(n+1) := by positivity
    nlinarith [norm_nonneg (clockProjectionError Q W F)]
  exact hle

/-- Graph coercivity bounds the actual primitive gradient, including time zero. -/
private theorem clock_primitive_gradient_size
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) {i : Fin d}
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (b : ℝ≥0) :
    ‖∫ u in Icc (0 : ℝ) (b : ℝ), hP.gradientOrbit μ u‖ ^ 2 ≤
      8 * (Real.exp (2 * Λ) * Λ) * (b : ℝ) * ‖μ‖ ^ 2 := by
  let M := Real.exp (2 * Λ) * Λ
  have hM : 0 < M := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hcontract (t : ℝ≥0) : ‖P t μ‖ ≤ ‖μ‖ := by
    have ht := hP.norm_le t
    simp only [complexForceShift, norm_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, Real.exp_zero] at ht
    exact ((P t).le_opNorm μ).trans
      ((mul_le_mul_of_nonneg_right ht (norm_nonneg μ)).trans_eq (one_mul _))
  have hp : ‖∫ u in Icc (0 : ℝ) (b : ℝ), P u.toNNReal μ‖ ≤ ‖μ‖ * (b : ℝ) := by
    have hn : ‖∫ u in Icc (0 : ℝ) (b : ℝ), P u.toNNReal μ‖ ≤
        ‖μ‖ * volume.real (Icc (0 : ℝ) (b : ℝ)) :=
      norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top (μ := volume))
        (fun (u : ℝ) _ => hcontract u.toNNReal)
    rw [Real.volume_real_Icc, sub_zero] at hn
    have hv : max (b : ℝ) 0 = (b : ℝ) := max_eq_left b.property
    exact hn.trans_eq (congrArg (fun x : ℝ => ‖μ‖ * x) hv)
  have hi : ‖P b μ - μ‖ ≤ 2 * ‖μ‖ := by
    calc
      _ ≤ ‖P b μ‖ + ‖μ‖ := norm_sub_le _ _
      _ ≤ ‖μ‖ + ‖μ‖ := add_le_add (hcontract b) le_rfl
      _ = _ := by ring
  have he := (hP.integral_orbit_graph_forced μ b).gradient_sq_le
    (hP.integral_orbit_gradient μ b)
  simp only [complexForceShift, norm_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, add_zero] at he
  have hb := he.trans (mul_le_mul hp hi (norm_nonneg _) (by positivity))
  have hid : (4 * M) * (M⁻¹ / 4) = 1 := by
    field_simp
  calc
    _ = (4 * M) * ((M⁻¹ / 4) *
        ‖∫ u in Icc (0 : ℝ) (b : ℝ), hP.gradientOrbit μ u‖ ^ 2) := by
      rw [← mul_assoc, hid, one_mul]
    _ ≤ (4 * M) * ((‖μ‖ * (b : ℝ)) * (2 * ‖μ‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by dsimp only [M]; ring

/-- A continuous actual gradient and the canonical positive-time gradient
have the same Bochner primitive. Their value at zero is immaterial. -/
private theorem clock_gradient_primitive_eq_canonical {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q))
    (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal μ) (G s)) (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, G s) =
      ∫ s in Set.Icc (0 : ℝ) T, hP.gradientOrbit μ s := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [volume.ae_ne (0 : ℝ)] with s hs ht
  apply PiLp.ext
  intro k
  exact congrFun ((hG s).unique (hP.gradientOrbit_spec μ
    (lt_of_le_of_ne ht.1 (Ne.symm hs)))) k

/-- The full actual primitive flux has a structural L² size at each fixed time. -/
private theorem clock_actual_primitive_flux_size {d : ℕ} (D : StructuralData d)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))),
        Continuous G →
        (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P s.toNNReal μ) (G s)) → ∀ j : Fin d,
        ‖clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j‖ ≤ B := by
  classical
  obtain ⟨M, hM, hm⟩ := clock_actual_clock_norm_bound D
  let K := sourceReducedBound D.ellipticity
  let A := ((d : ℝ)*K)^2 * (8*(Real.exp (2*D.ellipticity)*D.ellipticity)*T*M^2)
  have hK : 0 < K := Clock.sourceReducedBound_pos D.one_le_ellipticity
  have hA : 0 ≤ A := by dsimp [A]; have := D.one_le_ellipticity; positivity
  refine ⟨A+1, by positivity, ?_⟩
  intro Q i P hP μ hμ G hGc hG j
  let V := ∫ s in (0 : ℝ)..T, G s
  have hVk (k : Fin d) : (∫ s in (0 : ℝ)..T, G s k) = V k :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k).intervalIntegral_comp_comm (hGc.intervalIntegrable 0 T)
  have hnorm : ‖clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j‖ ≤
      (d : ℝ)*K*‖V‖ := by
    unfold clockPhysicalFlux
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ k : Fin d, K*‖V‖ := by
        apply Finset.sum_le_sum
        intro k _
        have hh := clock_coefficient_mul_norm_le Q 0 j k
          (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) 0
            (∫ s in (0 : ℝ)..T, G s k))
        rw [norm_complexTranslation, hVk] at hh
        simpa only [hVk] using
          hh.trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le V k) hK.le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]
  have hV : ‖V‖^2 ≤ 8*(Real.exp (2*D.ellipticity)*D.ellipticity)*T*‖μ‖^2 := by
    have he := clock_primitive_gradient_size Q P hP μ ⟨T,hT⟩
    change ‖∫ u in Set.Icc (0 : ℝ) T, hP.gradientOrbit μ u‖^2 ≤
      8*(Real.exp (2*D.ellipticity)*D.ellipticity)*T*‖μ‖^2 at he
    simpa only [V, clock_gradient_primitive_eq_canonical Q hP μ G hG T hT] using he
  have hFsq : ‖clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j‖^2 ≤ A := by
    calc
      _ ≤ ((d : ℝ)*K*‖V‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = ((d : ℝ)*K)^2 * ‖V‖^2 := mul_pow _ _ _
      _ ≤ ((d : ℝ)*K)^2 * (8*(Real.exp (2*D.ellipticity)*D.ellipticity)*T*‖μ‖^2) :=
        mul_le_mul_of_nonneg_left hV (sq_nonneg _)
      _ ≤ A := by
        dsimp only [A]
        have he := pow_le_pow_left₀ (norm_nonneg _) (hm Q μ hμ) 2
        have := D.one_le_ellipticity
        gcongr
  nlinarith [norm_nonneg (clockPhysicalFlux Q (fun k => ∫ s in (0 : ℝ)..T, G s k) 0 j),
    sq_nonneg A]

private theorem clock_norm_centered_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖centeredComplexLp Q f‖ ≤ ‖f‖ := by
  letI := reducedLaw_probability Q
  let c := ∫ ω, f ω ∂reducedLaw Q
  have ho : inner ℂ (Lp.const 2 (reducedLaw Q) c) (centeredComplexLp Q f) = 0 := by
    rw [MeasureTheory.L2.inner_def]
    change (∫ ω, inner ℂ (Lp.const 2 (reducedLaw Q) c ω)
      (centeredComplexLp Q f ω) ∂reducedLaw Q) = 0
    rw [integral_congr_ae (Filter.Eventually.mono
      (Lp.coeFn_const 2 (reducedLaw Q) c) (fun ω h => by rw [h]))]
    simp only [Function.const_apply, RCLike.inner_apply]
    rw [integral_mul_const, integral_centeredComplexLp, zero_mul]
  have he : Lp.const 2 (reducedLaw Q) c + centeredComplexLp Q f = f := by
    change _ + (f - Lp.const 2 (reducedLaw Q) c) = f
    abel
  have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (Lp.const 2 (reducedLaw Q) c) (centeredComplexLp Q f) ho
  rw [he] at hh
  nlinarith [sq_nonneg ‖Lp.const 2 (reducedLaw Q) c‖, norm_nonneg f,
    norm_nonneg (centeredComplexLp Q f)]

/-- The actual centered time-integrated coefficient flux has Gaussian
L² concentration, using its derived joint-local approximations. -/
private theorem clock_actual_primitive_flux_gaussian_decay {d : ℕ}
    (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))),
        Continuous G →
        (∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P t.toNNReal μ) (G t)) → ∀ j : Fin d, ∀ (s : ℝ) (hs : 0 < s),
        ‖gaussianAverage hd Q s hs
          (centeredComplexLp Q
            (clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..T, G t k) 0 j))‖ ≤
          C * s^(-(d : ℝ)/4) := by
  obtain ⟨R, L, hR, hL, herr⟩ := clock_actual_flux_polynomial_error D T hT d
  obtain ⟨B, hB, hsize⟩ := clock_actual_primitive_flux_size D T hT
  let q := ((2 : ℝ)^(d+1))⁻¹
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [inv_eq_one_div]
    apply (div_lt_one (by positivity)).mpr
    rw [pow_succ]
    have he : (1 : ℝ) ≤ 2^d := one_le_pow₀ (by norm_num)
    nlinarith
  have hqd : (2 : ℝ)^d*q < 1 := by
    have he : (2 : ℝ)^d*q = 1/2 := by
      dsimp only [q]
      rw [pow_succ]
      field_simp
    rw [he]
    norm_num
  obtain ⟨C, hC, hb⟩ := clock_gaussian_dyadic_l2_approximants d
    D.ellipticity D.dependenceRange R B L q hR.le hB.le hL.le hq hq1 hqd
  refine ⟨C, hC, ?_⟩
  intro Q hQ i P hP μ hμ G hGc hG j s hs
  let F := clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..T, G t k) 0 j
  let K : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n => centeredComplexLp Q
    (clockLocalProjection Q {x : Vec d | euclideanNorm x < R*(2 : ℝ)^n} F)
  apply hb hd Q (reducedLaw_hasFiniteRange Q) (centeredComplexLp Q F) K
  · exact (clock_norm_centered_le Q _).trans ((clockLocalProjection_norm_le Q _ F).trans
      (hsize Q i P hP μ hμ G hGc hG j))
  · intro n
    exact isComplexLocal_centered Q (clock_projection_isLocal Q _ F)
  · intro n
    exact integral_centeredComplexLp Q _
  · intro n
    have heq := (centeredComplexLpCLM Q).map_sub F
      (clockLocalProjection Q {x : Vec d | euclideanNorm x < R*(2 : ℝ)^n} F)
    simp only [centeredComplexLpCLM_apply] at heq
    change ‖centeredComplexLp Q F - centeredComplexLp Q
      (clockLocalProjection Q {x : Vec d | euclideanNorm x < R*(2 : ℝ)^n} F)‖ ≤ L*q^n
    rw [← heq]
    have he := herr Q hQ i P hP μ hμ G hGc hG ((2 : ℝ)^n) (by positivity) j
    have hp : ((2 : ℝ)^n)^(d+1) = ((2 : ℝ)^(d+1))^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm n (d+1)]
    rw [hp, div_eq_mul_inv, ← inv_pow] at he
    exact (clock_norm_centered_le Q _).trans he

/-- Gaussian differentiation of the actual primitive flux gains a half power. -/
private theorem clock_actual_primitive_flux_derivative_decay {d : ℕ}
    (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (i : Fin d) (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q i 0 P →
      ∀ (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))),
        Continuous G →
        (∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P t.toNNReal μ) (G t)) → ∀ (s : ℝ) (hs : 0 < s),
        ‖∑ j : Fin d, gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
          (clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..T, G t k) 0 j)‖ ≤
          C * s^(-(1/2+(d : ℝ)/4)) := by
  obtain ⟨C₀, hC₀, havg⟩ := clock_actual_primitive_flux_gaussian_decay hd D T hT
  let E := (sourceReducedBound D.ellipticity+1)*C₀*
    (2 : ℝ)^((1 : ℝ)/2+(d : ℝ)/4)
  have hK := Clock.sourceReducedBound_pos D.one_le_ellipticity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨(d : ℝ)*E, by positivity, ?_⟩
  intro Q hQ i P hP μ hμ G hGc hG s hs
  have hj (j : Fin d) :
      ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
        (clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..T, G t k) 0 j)‖ ≤
        E * s^(-(1/2+(d : ℝ)/4)) := by
    let F := clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..T, G t k) 0 j
    rw [← UnitInitialization.gaussianDerivativeAverage_one_centered hd Q s hs F j,
      clock_gaussian_derivative_half_comp]
    have hg := havg Q hQ i P hP μ hμ G hGc hG j (s/2) (half_pos hs)
    calc
      _ ≤ ((sourceReducedBound D.ellipticity+1)*(s/2)^(-(1 : ℝ)/2))*
          (C₀*(s/2)^(-(d : ℝ)/4)) :=
        (clock_gaussian_derivative_norm_le hd Q (s/2) (half_pos hs) j _).trans
          (mul_le_mul_of_nonneg_left hg (by positivity))
      _ = _ := by
        dsimp only [E]
        rw [Real.div_rpow hs.le (by norm_num), Real.div_rpow hs.le (by norm_num)]
        simp only [neg_div]
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [div_inv_eq_mul]
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show -(1/2+(d : ℝ)/4) = -((1 : ℝ)/2) + -((d : ℝ)/4) by ring,
          Real.rpow_add hs]
        ring
  calc
    _ ≤ ∑ j : Fin d, ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
        (clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..T, G t k) 0 j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, E*s^(-(1/2+(d : ℝ)/4)) := Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp; ring

/-- The integrated generator graph gives the actual clock increment at a fixed
Gaussian smoothing time, with the coefficient flux retained explicitly. -/
private theorem clock_gaussian_increment_flux {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q))
    (G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
    (hGc : Continuous G)
    (hG : ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t.toNNReal μ) (G t))
    (b : ℝ≥0) (s : ℝ) (hs : 0 < s) :
    gaussianAverage hd Q s hs (P b μ-μ) =
      (1/2 : ℝ) • ∑ j : Fin d, gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
        (clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..(b : ℝ), G t k) 0 j) := by
  classical
  let F := fun j => clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..(b : ℝ), G t k) 0 j
  have hprim (k : Fin d) : (∫ t in Icc (0 : ℝ) (b : ℝ), hP.gradientOrbit μ t) k =
      ∫ t in (0 : ℝ)..(b : ℝ), G t k := by
    rw [← clock_gradient_primitive_eq_canonical Q hP μ G hG (b : ℝ) b.coe_nonneg]
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k).intervalIntegral_comp_comm
      (hGc.intervalIntegrable 0 (b : ℝ))).symm
  obtain ⟨H, hH, hw⟩ := hP.integral_orbit_graph_forced μ b
  have hH' := hH.unique (hP.integral_orbit_gradient μ b)
  rw [hH'] at hw
  apply UnitInitialization.endpointPairing_ext Q
  intro g
  let V := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 g
  have hV := homogeneousAverage_hasComplexHorizontalGradient_allData Q
    ⟨0, by omega⟩ s hs 0 g
  have he := hw (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g) V hV
  simp only [zero_mul, add_zero] at he
  have hF (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      F j ω = ∑ k, (ω.1 0 j k : ℂ)*
        ((∫ t in Icc (0 : ℝ) (b : ℝ), hP.gradientOrbit μ t) k) ω := by
    filter_upwards [clockPhysicalFlux_coe Q
      (fun k => ∫ t in (0 : ℝ)..(b : ℝ), G t k) 0 j] with ω hω
    simpa only [F, translate_zero, hprim] using hω
  have hi (j : Fin d) : Integrable (fun ω => F j ω*V j ω) (reducedLaw Q) :=
    (Lp.memLp (F j)).integrable_mul (Lp.memLp (V j))
  have hsum : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ)*
        ((∫ t in Icc (0 : ℝ) (b : ℝ), hP.gradientOrbit μ t) k) ω*V j ω ∂reducedLaw Q) =
      ∑ j, c4EndpointPairing Q (F j) (V j) := by
    simp only [c4EndpointPairing_apply]
    rw [← integral_finset_sum _ (fun j _ => hi j)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hF] with ω hω
    simp only [hω, Finset.sum_mul]
  rw [hsum] at he
  have hav := c4EndpointPairing_homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (P b μ-μ) g
  simp only [neg_zero] at hav
  change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (P b μ-μ)) g = _
  rw [hav]
  have hleft : c4EndpointPairing Q (P b μ-μ)
      (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g) =
      -(1/2 : ℂ)*∑ j, c4EndpointPairing Q (F j) (V j) := by
    simpa only [c4EndpointPairing_apply] using he
  rw [hleft]
  have hder (j : Fin d) : c4EndpointPairing Q
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)) g =
        -c4EndpointPairing Q (F j) (V j) := by
    rw [c3EndpointPairing_gaussianDerivativeAverage_one,
      c3GaussianDerivativeAverage_one_eq_gradient]
  change _ = c4EndpointPairing Q ((1/2 : ℝ) • ∑ j,
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)) g
  simp only [map_smul, map_sum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hder, Finset.sum_neg_distrib]
  norm_num [Complex.real_smul]

/-- The zero-force increment already has zero reduced-law mean. -/
private theorem clock_centered_increment_eq {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (μ : Lp ℂ 2 (reducedLaw Q)) (b : ℝ≥0) :
    centeredComplexLp Q (P b μ)-centeredComplexLp Q μ = P b μ-μ := by
  have hm := (hP.integral_orbit_graph_forced μ b).integral_eq_zero
  have he := (centeredComplexLpCLM Q).map_sub (P b μ) μ
  simp only [centeredComplexLpCLM_apply] at he
  rw [← he]
  change (P b μ-μ)-Lp.const 2 (reducedLaw Q) _ = _
  rw [hm, map_zero, sub_zero]

/-- At each fixed physical time the centered clock increment has an additional
half power of Gaussian decay, uniformly over all admissible reduced laws. -/
private theorem clock_fixed_initial_increment_decay {d : ℕ}
    (hd : 2 ≤ d) (D : StructuralData d) (b : ℝ≥0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
      ∀ (s : ℝ) (hs : 0 < s),
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P b μ)-centeredComplexLp Q μ)‖ ≤
          C*s^(-(1/2+(d : ℝ)/4)) := by
  obtain ⟨C, hC, hb⟩ := clock_actual_primitive_flux_derivative_decay hd D b b.coe_nonneg
  refine ⟨C+1, by positivity, ?_⟩
  intro Q hQ μ hμ P hP s hs
  obtain ⟨g, hμg⟩ := centeredEquations_clock_initial_generator
    (i := ⟨0, by omega⟩) (ζ := 0) hQ hμ
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hμg
  rw [clock_centered_increment_eq Q hP μ b,
    clock_gaussian_increment_flux hd Q hP μ G hGc hG b s hs, norm_smul]
  have hhalf : ‖(1/2 : ℝ)‖ ≤ 1 := by norm_num
  have hnorm := hb Q hQ ⟨0, by omega⟩ P hP μ hμ G hGc hG s hs
  calc
    _ ≤ 1*‖∑ j : Fin d, gaussianDerivativeAverage hd Q s hs 1 (fun _ => j)
      (clockPhysicalFlux Q (fun k => ∫ t in (0 : ℝ)..(b : ℝ), G t k) 0 j)‖ :=
        mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
    _ ≤ C*s^(-(1/2+(d : ℝ)/4)) := by simpa only [one_mul] using hnorm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs.le _)

/-- The homogeneous zero-force evolution contracts every Gaussian-smoothed L2
norm; the two actual translation averages commute. -/
private theorem clock_gaussian_homogeneous_contraction {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianAverage hd Q s hs (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t f)‖ ≤
      ‖gaussianAverage hd Q s hs f‖ := by
  have he : gaussianAverage hd Q s hs
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t f) =
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t (gaussianAverage hd Q s hs f) := by
    simpa only [c3GaussianDerivativeAverage_zero] using
      c3GaussianDerivativeAverage_homogeneousEvolution hd Q ⟨0, by omega⟩ 0 t
        s hs 0 (fun j => Fin.elim0 j) f
  rw [he]
  have hop := norm_homogeneousGaussianEvolution_le Q ⟨0, by omega⟩ 0 t
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_mul, zero_div, Real.exp_zero] at hop
  exact ((homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (one_mul _))

/-- Full unforced Gaussian smoothing for the actual reduced clock. -/
theorem clock_unforced_full_gaussian_smoothing
    : ∀ (havg : node_e_u3A_clock_u2D_averageStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) →
      ∀ (s : ℝ) (hs : 0 < s), 2*(τ : ℝ) ≤ s →
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
          centeredComplexLp Q μ)‖ ≤
          C * s ^ (-(d : ℝ)/4) * ((τ : ℝ)/s + Real.sqrt ((τ : ℝ)/s)) := by
  intro havg d hd D
  obtain ⟨Ctail, t₀, hCtail, ht₀, htail⟩ := clock_tail_gaussian_smoothing havg d hd D
  let b : ℝ≥0 := ⟨t₀, by linarith⟩
  obtain ⟨Cinit, hCinit, hinit⟩ := clock_fixed_initial_increment_decay hd D b
  obtain ⟨Chom, hChom, hhom⟩ := clock_gaussian_homogeneous_displacement d hd D
  refine ⟨Ctail+Cinit+Chom, t₀, by positivity, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP τ hτ s hs hτs
  have hbτ : b ≤ τ := by exact_mod_cast hτ
  have hτone : 1 ≤ (τ : ℝ) := ht₀.trans hτ
  have hratio : 0 ≤ (τ : ℝ)/s := div_nonneg τ.coe_nonneg hs.le
  have hscale : 0 ≤ s^(-(d : ℝ)/4) := Real.rpow_nonneg hs.le _
  let u := centeredComplexLp Q (P τ μ)
  let v := centeredComplexLp Q (P b μ)
  let w := centeredComplexLp Q μ
  let H := homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (τ-b)
  let A := homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
  have hsplit : u-w = (u-H v)+H (v-w)+(H w-w) := by rw [map_sub]; abel
  have h1 : ‖A (u-H v)‖ ≤
      Ctail*s^(-(d : ℝ)/4)*((τ : ℝ)/s+Real.sqrt ((τ : ℝ)/s)) :=
    htail Q hQ a μ ha hμ P hP b τ (by rfl) hbτ s hs hτs
  have hsroot : s^(-(1 : ℝ)/2) ≤ Real.sqrt ((τ : ℝ)/s) := by
    rw [show -(1 : ℝ)/2 = -((1 : ℝ)/2) by ring, Real.rpow_neg hs.le,
      ← Real.sqrt_eq_rpow, inv_eq_one_div, Real.sqrt_div τ.coe_nonneg s]
    exact div_le_div_of_nonneg_right (Real.one_le_sqrt.mpr hτone) (Real.sqrt_nonneg s)
  have hinit' := hinit Q hQ μ hμ P hP s hs
  have hexp : s^(-(1/2+(d : ℝ)/4)) = s^(-(d : ℝ)/4)*s^(-(1 : ℝ)/2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [hexp] at hinit'
  have h2 : ‖A (H (v-w))‖ ≤
      Cinit*s^(-(d : ℝ)/4)*((τ : ℝ)/s+Real.sqrt ((τ : ℝ)/s)) := by
    calc
      _ ≤ ‖A (v-w)‖ := clock_gaussian_homogeneous_contraction hd Q s hs (τ-b) (v-w)
      _ ≤ Cinit*(s^(-(d : ℝ)/4)*s^(-(1 : ℝ)/2)) := hinit'
      _ ≤ Cinit*s^(-(d : ℝ)/4)*Real.sqrt ((τ : ℝ)/s) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hsroot (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have htτ : ((τ-b : ℝ≥0) : ℝ) ≤ (τ : ℝ) := by
    exact_mod_cast (tsub_le_self : τ-b ≤ τ)
  have h3 : ‖A (H w-w)‖ ≤
      Chom*s^(-(d : ℝ)/4)*((τ : ℝ)/s+Real.sqrt ((τ : ℝ)/s)) := by
    calc
      _ ≤ Chom*s^(-(d : ℝ)/4)*(((τ-b : ℝ≥0) : ℝ)/s) := hhom Q hQ μ hμ (τ-b) s hs
      _ ≤ Chom*s^(-(d : ℝ)/4)*((τ : ℝ)/s) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htτ hs.le) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _))
        (by positivity)
  change ‖A (u-w)‖ ≤ _
  rw [hsplit, map_add, map_add]
  calc
    _ ≤ (‖A (u-H v)‖+‖A (H (v-w))‖)+‖A (H w-w)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Ctail*s^(-(d : ℝ)/4)*((τ : ℝ)/s+Real.sqrt ((τ : ℝ)/s))+
        Cinit*s^(-(d : ℝ)/4)*((τ : ℝ)/s+Real.sqrt ((τ : ℝ)/s)))+
        Chom*s^(-(d : ℝ)/4)*((τ : ℝ)/s+Real.sqrt ((τ : ℝ)/s)) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end
end EinsteinFull.Blueprint
