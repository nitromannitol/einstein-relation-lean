import EinsteinFull.Work.W4.HomogeneousHorizontalCalculusSupport
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Actual all-data horizontal smoothing from dense-core spatial integration
by parts and the closed strong horizontal derivative graph. -/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation
variable {d : ℕ} {Λ r : ℝ}
attribute [local instance] reducedLaw_probability

/-- Every positive-time kernel is Schwartz, by exact parabolic scaling of the
proved unit-time kernel. This assertion retains its literal coordinate carrier. -/
private theorem smoothing_kernel_schwartz (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    ∃ K : SchwartzMap (Vec d) ℂ, ∀ x, K x = homogenizedGaussianKernel Q i s hs ζ x := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  let L := (LinearEquiv.smulOfNeZero (M := Vec d) ℝ c⁻¹ (inv_ne_zero hc.ne')).toContinuousLinearEquiv
  let K := homogenizedGaussianSchwartz Q i 1 (by norm_num) (by norm_num) le_rfl
    (ζ * (c : ℂ))
  refine ⟨(((c ^ d)⁻¹ : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L K, fun x => ?_⟩
  change (((c ^ d)⁻¹ : ℝ) : ℂ) * K (c⁻¹ • x) = _
  have he := homogenizedGaussianKernel_scale Q i c 1 hc (by norm_num) ζ (c⁻¹ • x)
  simpa only [mul_one, hcs, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    K, homogenizedGaussianSchwartz_apply] using he.symm

/-- Coordinate integration by parts against the actual stationary translation
orbit. A Schwartz spatial kernel supplies all three integrability requirements. -/
private theorem smoothing_spatial_parts
    (Q : EnvironmentLaw d Λ r) (j : Fin d)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (K : SchwartzMap (Vec d) ℂ) :
    (∫ x : Vec d, K x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) =
      -(∫ x : Vec d, fderiv ℝ K x (unitVector j) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  have hD (x : Vec d) : D x = fderiv ℝ K x (unitVector j) := rfl
  have hg (x : Vec d) : HasLineDerivAt ℝ
      (fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) x (unitVector j) := by
    have hd := (((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0
      (hf.hasDerivAt_orbit 0)
    simp only [zero_smul, complexTranslation_zero] at hd
    change HasDerivAt (fun t : ℝ => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f))
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) 0 at hd
    simpa only [HasLineDerivAt, ← complexTranslation_add] using! hd

  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (by simpa only [hD] using! (integrable_kernel_complexTranslation _ _ D
      D.integrable D.continuous f))
    (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous g)
    (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous f)
    (fun x _ => (K.hasFDerivAt x).hasLineDerivAt (unitVector j)) (fun x _ => hg x)


private def smoothingIntegralCLM (Q : EnvironmentLaw d Λ r)
    (K : SchwartzMap (Vec d) ℂ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x : Vec d, K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        exact integral_add
          (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous f)
          (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous g)
      map_smul' := fun c f => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c, integral_smul] }
    (∫ x : Vec d, ‖K x‖) (fun f => by
      calc
        _ ≤ ∫ x : Vec d, ‖K x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ :=
          norm_integral_le_integral_norm _
        _ = _ := by
          simp_rw [norm_smul, norm_complexTranslation]
          rw [integral_mul_const])

/-- Literal coordinate gradients of the actual anisotropic complex-drift kernel.
The minus sign is forced by the stationary translation convention. -/
def homogeneousGaussianHorizontalGradient (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
  -(∫ x : Vec d, fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)

/-- The literal gradient is a bounded linear operator on every complex L2 datum. -/
theorem continuous_homogeneousGaussianHorizontalGradient (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (j : Fin d) :
    Continuous (fun f => homogeneousGaussianHorizontalGradient Q i s hs ζ f j) := by
  obtain ⟨K, hK⟩ := smoothing_kernel_schwartz Q i s hs ζ
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs ζ := funext hK
  have hD : (D : Vec d → ℂ) = fun x =>
      fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) := by
    change (fun x => fderiv ℝ K x (unitVector j)) = _
    rw [he]
  convert (smoothingIntegralCLM Q D).continuous.neg using 1
  funext f
  change -(∫ x : Vec d, _ • _) = -(∫ x : Vec d, _ • _)
  rw [hD]

/-- No initial H1 assumption: the actual Gaussian average has its literal
strong horizontal gradient for every L2 datum and every positive time. -/
theorem homogeneousAverage_hasComplexHorizontalGradient_allData
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (homogeneousAverage Q i s hs ζ f)
      (homogeneousGaussianHorizontalGradient Q i s hs ζ f) := by
  let S := {u : Lp ℂ 2 (reducedLaw Q) |
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (homogeneousAverage Q i s hs ζ u)
      (homogeneousGaussianHorizontalGradient Q i s hs ζ u)}
  have hclosed : IsClosed S :=
    (isClosed_complexHorizontalGradient_graph (reducedLaw Q) (reducedLaw_stationary Q)).preimage
      ((homogeneousAverageCLM Q i s hs ζ).continuous.prodMk
        (continuous_pi fun j => continuous_homogeneousGaussianHorizontalGradient Q i s hs ζ j))
  have hsub : {u | IsComplexHorizontallySmooth Q u} ⊆ S := by
    intro u hu
    obtain ⟨J, hJ0, hJ⟩ := hu
    have hgrad : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        u (fun j => J [j]) := by
      intro j
      simpa only [hJ0] using! hJ [] j
    have he (j : Fin d) : homogeneousGaussianHorizontalGradient Q i s hs ζ u j =
        homogeneousAverage Q i s hs ζ (J [j]) := by
      obtain ⟨K, hK⟩ := smoothing_kernel_schwartz Q i s hs ζ
      have hKe : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs ζ := funext hK
      have hp := smoothing_spatial_parts Q j u (J [j]) (hgrad j) K
      rw [hKe] at hp
      exact hp.symm
    change HasComplexHorizontalGradient _ _ _ _
    rw [show homogeneousGaussianHorizontalGradient Q i s hs ζ u =
      (fun j => homogeneousAverage Q i s hs ζ (J [j])) from funext he]
    exact hgrad.homogeneousAverage i s hs ζ
  exact hclosed.closure_subset (closure_mono hsub (dense_complexHorizontallySmooth Q f))

/-- The actual all-time evolution is in horizontal H1 at every positive time,
with the displayed literal kernel gradient, for arbitrary complex L2 data. -/
theorem homogeneousGaussianEvolution_hasComplexHorizontalGradient_allData
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (homogeneousGaussianEvolution Q i ζ t f)
      (homogeneousGaussianHorizontalGradient Q i t ht ζ f) := by
  rw [homogeneousGaussianEvolution_pos Q i ζ t ht]
  exact homogeneousAverage_hasComplexHorizontalGradient_allData Q i t ht ζ f


/-- Positive-time gradients propagate by the actual semigroup, including a
zero additional time. This identity follows from uniqueness in the full graph. -/
theorem homogeneousGaussianHorizontalGradient_add
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (s t : ℝ≥0)
    (ht : 0 < (t : ℝ)) (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    homogeneousGaussianHorizontalGradient Q i (s + t)
      (by exact add_pos_of_nonneg_of_pos s.coe_nonneg ht) ζ f j =
      homogeneousGaussianEvolution Q i ζ s
        (homogeneousGaussianHorizontalGradient Q i t ht ζ f j) := by
  have h := (homogeneousGaussianEvolution_hasComplexHorizontalGradient_allData Q i ζ t ht f j).homogeneousGaussianEvolution i ζ s
  have hsum := homogeneousGaussianEvolution_hasComplexHorizontalGradient_allData Q i ζ
    (s + t) (by exact add_pos_of_nonneg_of_pos s.coe_nonneg ht) f j
  rw [homogeneousGaussianEvolution_add, ContinuousLinearMap.comp_apply] at hsum
  exact hsum.unique h

/-- The literal gradient of every L2 orbit is strongly continuous at positive
times. No derivative or H1 regularity of the initial datum is assumed. -/
theorem continuous_positiveTime_homogeneousGaussianHorizontalGradient
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    Continuous (fun t : {t : ℝ≥0 // 0 < (t : ℝ)} =>
      homogeneousGaussianHorizontalGradient Q i t.val t.property ζ f j) := by
  rw [continuous_iff_continuousAt]
  intro t
  let a : ℝ≥0 := t.val / 2
  have ha : 0 < (a : ℝ) := by dsimp only [a]; exact half_pos t.property
  have hat : a < t.val := half_lt_self (NNReal.coe_pos.mp t.property)
  have hcont : Continuous (fun u : {t : ℝ≥0 // 0 < (t : ℝ)} =>
      homogeneousGaussianEvolution Q i ζ (u.val - a)
        (homogeneousGaussianHorizontalGradient Q i a ha ζ f j)) :=
    (continuous_homogeneousGaussianEvolution Q i ζ _).comp (continuous_subtype_val.sub continuous_const)
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_subtype_val).mem_nhds hat] with u hu
  have he := homogeneousGaussianHorizontalGradient_add Q i ζ (u.val - a) a ha f j
  simpa only [← NNReal.coe_add, tsub_add_cancel_of_le hu.le] using! he

/-- Exact parabolic scaling for each literal spatial derivative. -/
theorem homogenizedGaussianKernel_coordinateDerivative_scale
    (Q : EnvironmentLaw d Λ r) (i j : Fin d) (c : ℝ) (hc : 0 < c)
    (ζ : ℂ) (x : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i (c ^ 2) (sq_pos_of_pos hc) ζ)
      (c • x) (unitVector j) =
      (((c ^ d)⁻¹ * c⁻¹ : ℝ) : ℂ) *
        fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (c : ℂ)))
          x (unitVector j) := by
  have he := homogenizedGaussianKernel_scale Q i c 1 hc zero_lt_one ζ x
  simp only [mul_one] at he
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate, he]
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv]
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  field_simp
  simp only [Complex.ofReal_one, mul_one]
  ring

/-- Exact scaled integral for the all-data gradient; the signed tilt is zeta*sqrt(t). -/
theorem homogeneousGaussianHorizontalGradient_eq_scaled
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    homogeneousGaussianHorizontalGradient Q i s hs ζ f j =
      -(Real.sqrt s)⁻¹ • (∫ x : Vec d,
        fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)))
          x (unitVector j) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (Real.sqrt s • x) f) := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hd (x : Vec d) := homogenizedGaussianKernel_coordinateDerivative_scale Q i j c hc ζ x
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  have hK : homogenizedGaussianKernel Q i (c ^ 2) (sq_pos_of_pos hc) ζ =
      homogenizedGaussianKernel Q i s hs ζ := by
    funext x
    unfold homogenizedGaussianKernel
    rw [hcs]
  rw [hK] at hd
  have he := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) c
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _))] at he
  simp only [hd, Complex.ofReal_mul, mul_smul, Complex.coe_smul] at he
  erw [integral_smul, integral_smul] at he
  have hi := smul_right_injective _ (inv_ne_zero (pow_ne_zero d hc.ne')) he
  change -(∫ x : Vec d, _ • _) = _
  rw [← hi]
  simp only [neg_smul]
  rfl

private theorem smoothing_unit_derivative_bound (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r)
      (i j : Fin d) (ζ : ℂ),
      (∫ x : Vec d, ‖fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one ζ)
        x (unitVector j)‖) ≤ B * Real.exp (C * (1 + ‖ζ‖) ^ 2) := by
  let n := (volume : Measure (Vec d)).integrablePower
  let D := (2 : ℝ) ^ n * (∫ x : Vec d, (1 + ‖x‖) ^ (-(n : ℝ)))
  let C₀ := gaussianSchwartzBound d Λ 0
  let C₁ := gaussianSchwartzBound d Λ n
  have h₀ : 0 < C₀ := gaussianSchwartzBound_pos d Λ hΛ 0
  have h₁ : 0 < C₁ := gaussianSchwartzBound_pos d Λ hΛ n
  have hD : 0 ≤ D := mul_nonneg (by positivity)
    (integral_nonneg fun x => Real.rpow_nonneg (by positivity) _)
  refine ⟨D * (C₀ + C₁) + 1, C₀ + C₁, by positivity, by positivity, ?_⟩
  intro r Q i j ζ
  let E := Real.exp ((C₀ + C₁) * (1 + ‖ζ‖) ^ 2)
  have hb (m : ℕ) (hC : gaussianSchwartzBound d Λ m ≤ C₀ + C₁) (x : Vec d) :
      (1 + euclideanNorm x) ^ m *
        ‖fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one ζ) x (unitVector j)‖ ≤
          gaussianSchwartzBound d Λ m * E := by
    apply (homogenizedGaussianKernel_weighted_coordinate_bounds Q i 1 zero_lt_one
      (by norm_num) le_rfl ζ x m).2.1 j |>.trans
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC (sq_nonneg _)))
      (gaussianSchwartzBound_pos d Λ hΛ m).le
  have hb₀ (x : Vec d) :
      ‖fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one ζ) x (unitVector j)‖ ≤ C₀ * E := by
    simpa only [pow_zero, one_mul] using! hb 0 (by dsimp only [C₀]; linarith) x
  have hb₁ (x : Vec d) : ‖x‖ ^ n *
      ‖fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one ζ) x (unitVector j)‖ ≤ C₁ * E := by
    apply (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg x) ((norm_vec_le_euclideanNorm x).trans (le_add_of_nonneg_left zero_le_one)) n)
      (norm_nonneg _)).trans
    exact hb n (by dsimp only [C₁]; linarith) x
  have hi := integral_pow_mul_le_of_le_of_pow_mul_le (μ := (volume : Measure (Vec d)))
    (k := 0) hb₀ (by simpa only [zero_add] using! hb₁)
  simp only [pow_zero, one_mul] at hi
  calc
    _ ≤ D * (C₀ * E + C₁ * E) := hi
    _ ≤ (D * (C₀ + C₁) + 1) * E := by
      have hE : 0 ≤ E := (Real.exp_pos _).le
      nlinarith only [hE]

/-- Structural L2 gradient bounds on every compact complex-force disc at
all positive times. Both witnesses precede the law, force, time and datum. -/
theorem exists_homogeneousGaussianHorizontalGradient_bound
    (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r)
      (i j : Fin d) (R : ℝ), 0 ≤ R → ∀ (ζ : ℂ), ‖ζ‖ ≤ R →
      ∀ (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)),
      ‖homogeneousGaussianHorizontalGradient Q i s hs ζ f j‖ ≤
        (B / Real.sqrt s) * Real.exp (C * (1 + R * Real.sqrt s) ^ 2) * ‖f‖ := by
  obtain ⟨B, C, hB, hC, hb⟩ := smoothing_unit_derivative_bound d Λ hΛ
  refine ⟨B, C, hB, hC, ?_⟩
  intro r Q i j R hR ζ hζ s hs f
  rw [homogeneousGaussianHorizontalGradient_eq_scaled, norm_smul,
    Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hs))), neg_neg]
  have he : Real.exp (C * (1 + ‖ζ * (Real.sqrt s : ℂ)‖) ^ 2) ≤
      Real.exp (C * (1 + R * Real.sqrt s) ^ 2) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply pow_le_pow_left₀ (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hs)]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hζ (Real.sqrt_nonneg s)) 1
  calc
    _ ≤ (Real.sqrt s)⁻¹ * (∫ x : Vec d,
        ‖fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)))
          x (unitVector j) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
            (Real.sqrt s • x) f‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = (Real.sqrt s)⁻¹ * ((∫ x : Vec d,
        ‖fderiv ℝ (homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)))
          x (unitVector j)‖) * ‖f‖) := by
      simp_rw [norm_smul, norm_complexTranslation]
      rw [integral_mul_const]
    _ ≤ (Real.sqrt s)⁻¹ * ((B * Real.exp (C * (1 + R * Real.sqrt s) ^ 2)) * ‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      exact (hb r Q i j _).trans (mul_le_mul_of_nonneg_left he hB.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The literal differentiated-kernel translation integral is Bochner integrable
for every L2 datum, without any assumed horizontal derivative. -/
theorem integrable_homogeneousGaussianHorizontalGradient_integrand
    (Q : EnvironmentLaw d Λ r) (i j : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d =>
      fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  obtain ⟨K, hK⟩ := smoothing_kernel_schwartz Q i s hs ζ
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs ζ := funext hK
  have hD : (D : Vec d → ℂ) = fun x =>
      fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) := by
    change (fun x => fderiv ℝ K x (unitVector j)) = _
    rw [he]
  simpa only [hD] using! integrable_kernel_complexTranslation
    (reducedLaw Q) (reducedLaw_stationary Q) D D.integrable D.continuous f

/-- Explicit Euclidean aggregation of the coordinate L2 gradient bounds.
The default supremum norm of the coordinate carrier is not used. -/
theorem exists_homogeneousGaussianHorizontalGradient_euclidean_bound
    (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ (r : ℝ) (Q : EnvironmentLaw d Λ r)
      (i : Fin d) (R : ℝ), 0 ≤ R → ∀ (ζ : ℂ), ‖ζ‖ ≤ R →
      ∀ (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)),
      Real.sqrt (∑ j : Fin d, ‖homogeneousGaussianHorizontalGradient Q i s hs ζ f j‖ ^ 2) ≤
        Real.sqrt (d : ℝ) *
          ((B / Real.sqrt s) * Real.exp (C * (1 + R * Real.sqrt s) ^ 2) * ‖f‖) := by
  obtain ⟨B, C, hB, hC, hb⟩ := exists_homogeneousGaussianHorizontalGradient_bound d Λ hΛ
  refine ⟨B, C, hB, hC, ?_⟩
  intro r Q i R hR ζ hζ s hs f
  let M := (B / Real.sqrt s) * Real.exp (C * (1 + R * Real.sqrt s) ^ 2) * ‖f‖
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hh : (∑ j : Fin d, ‖homogeneousGaussianHorizontalGradient Q i s hs ζ f j‖ ^ 2) ≤
      (d : ℝ) * M ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, M ^ 2 := Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hb r Q i j R hR ζ hζ s hs f) 2
      _ = _ := by simp
  apply (Real.sqrt_le_sqrt hh).trans
  rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hM]

end EinsteinFull
