import EinsteinFull.Work.W3.GaussianSchwartzBoundsSupport
import EinsteinFull.Work.W3.ComplexGaussianProfileSupport
import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Frozen.JointCovariance

/-!
# Joint Gaussian tests and their exact bilinear covariance

Extracted from `GaussianProfileProof` so that deterministic Gaussian testing
and the frozen joint-covariance consumer depend only on adopted providers.
The physical endpoint comparison and stochastic covariance construction are
separate obligations. All products are bilinear, without complex conjugation.
-/

noncomputable section

namespace EinsteinFull

open EinsteinRelation MeasureTheory Filter
open scoped BigOperators Topology NNReal

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- Place a scalar Schwartz test in one coordinate of the actual joint carrier. -/
def jointCoordinateSchwartz (a : JointObservationIndex d) (ψ : SchwartzMap (Vec d) ℂ) :
    SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ)
    (Function.HasTemperateGrowth.const (EuclideanSpace.single a (1 : ℂ))) ψ

@[simp] theorem jointCoordinateSchwartz_apply (a b : JointObservationIndex d)
    (ψ : SchwartzMap (Vec d) ℂ) (x : Vec d) :
    jointCoordinateSchwartz a ψ x b = if b = a then ψ x else 0 := by
  simp [jointCoordinateSchwartz, EuclideanSpace.single_apply,
    PiLp.smul_apply, smul_eq_mul, mul_ite]

/-- The half-time Gaussian test for any complex force. -/
def profileGaussianSchwartz (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    SchwartzMap (Vec d) ℂ :=
  homogenizedGaussianSchwartz Q i (1 / 2) (by norm_num) le_rfl (by norm_num) ζ

@[simp] theorem profileGaussianSchwartz_apply (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (x : Vec d) :
    profileGaussianSchwartz Q i ζ x =
      homogenizedGaussianKernel Q i (1 / 2) (by norm_num) ζ x := rfl

/-- Actual first spatial derivatives, as scalar Schwartz tests. -/
def profileGaussianDerivativeSchwartz (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (ζ : ℂ) : SchwartzMap (Vec d) ℂ :=
  LineDeriv.lineDerivOp (unitVector j) (profileGaussianSchwartz Q i ζ)

@[simp] theorem profileGaussianDerivativeSchwartz_apply (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (ζ : ℂ) (x : Vec d) :
    profileGaussianDerivativeSchwartz Q i j ζ x =
      fderiv ℝ (homogenizedGaussianKernel Q i (1 / 2) (by norm_num) ζ) x
        (unitVector j) := rfl

/-- The transpose model test: its minus sign comes from the backward kernel. -/
def profileTransposeTest (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ) :
    SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
  (-1 / 2 : ℂ) • ∑ j : Fin d, jointCoordinateSchwartz (.inl (j, ⟨0, by omega⟩))
    (profileGaussianDerivativeSchwartz Q ⟨0, by omega⟩ j (-ζ))

/-- The velocity model test, retaining both divergence and force terms. -/
def profileVelocityTest (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) :
    SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
  (-1 / 2 : ℂ) • ∑ j : Fin d, jointCoordinateSchwartz (.inl (j, i))
    (profileGaussianDerivativeSchwartz Q ⟨0, by omega⟩ j ζ) +
    ζ • jointCoordinateSchwartz (.inl (⟨0, by omega⟩, i))
      (profileGaussianSchwartz Q ⟨0, by omega⟩ ζ)

/-- The clock model test in the literal clock coordinate of the joint field. -/
def profileClockTest (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ) :
    SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
  ζ • jointCoordinateSchwartz (.inr ()) (profileGaussianSchwartz Q ⟨0, by omega⟩ ζ)

/-- Evenness of the literal velocity profile needs no symmetry of the law. -/
theorem velocityGaussianProfile_neg (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (i : Fin d) (ζ : ℂ) :
    velocityGaussianProfile hd Q covariance i (-ζ) = velocityGaussianProfile hd Q covariance i ζ := by
  simp only [velocityGaussianProfile, neg_sq]

/-- Evenness of the literal clock profile needs no symmetry of the law. -/
theorem clockGaussianProfile_neg (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (ζ : ℂ) :
    clockGaussianProfile hd Q covariance (-ζ) = clockGaussianProfile hd Q covariance ζ := by
  simp only [clockGaussianProfile, neg_sq]

private lemma integrable_test_product
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (a b : JointObservationIndex d) : Integrable (fun x : Vec d => F x a * G x b) := by
  have hF : Integrable (fun x : Vec d => F x a) :=
    F.integrable.mono ((PiLp.continuous_apply 2 _ a).comp F.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => PiLp.norm_apply_le (F x) a))
  exact hF.mul_bdd ((PiLp.continuous_apply 2 _ b).comp G.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x =>
      (PiLp.norm_apply_le (G x) b).trans (G.norm_le_seminorm ℂ x)))

/-- The spatial bilinear covariance of actual joint Schwartz tests. -/
def jointTestCovariance
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) : ℂ :=
  ∑ a, ∑ b, (∫ x : Vec d, F x a * G x b) * (covariance a b : ℂ)

/-- This finite-sum implementation is exactly the frozen covariance contraction. -/
theorem jointTestCovariance_eq_integral
    (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    jointTestCovariance covariance F G =
      ∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
        F x a * (covariance a b : ℂ) * G x b := by
  have hi (a b : JointObservationIndex d) :
      Integrable (fun x : Vec d => (F x a * G x b) * (covariance a b : ℂ)) :=
    (integrable_test_product F G a b).mul_const _
  simp_rw [mul_right_comm (F _ _) (covariance _ _ : ℂ)]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hi a b))]
  simp_rw [integral_finset_sum _ (fun b _ => hi _ b), integral_mul_const]
  rfl

private lemma testCov_add_left (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    jointTestCovariance C (F + G) H = jointTestCovariance C F H + jointTestCovariance C G H := by
  unfold jointTestCovariance
  simp only [SchwartzMap.add_apply, PiLp.add_apply, add_mul,
    integral_add (integrable_test_product F H _ _) (integrable_test_product G H _ _),
    Finset.sum_add_distrib]

private lemma testCov_add_right (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G H : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    jointTestCovariance C F (G + H) = jointTestCovariance C F G + jointTestCovariance C F H := by
  unfold jointTestCovariance
  simp only [SchwartzMap.add_apply, PiLp.add_apply, mul_add,
    integral_add (integrable_test_product F G _ _) (integrable_test_product F H _ _),
    add_mul, Finset.sum_add_distrib]

private lemma testCov_smul_left (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (c : ℂ) :
    jointTestCovariance C (c • F) G = c * jointTestCovariance C F G := by
  simp only [jointTestCovariance, SchwartzMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, mul_assoc, integral_const_mul, Finset.mul_sum]

private lemma testCov_smul_right (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (c : ℂ) :
    jointTestCovariance C F (c • G) = c * jointTestCovariance C F G := by
  simp only [jointTestCovariance, SchwartzMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, mul_left_comm (F _ _) c, mul_assoc, integral_const_mul, Finset.mul_sum]

private lemma testCov_sum_left {ι : Type*} [Fintype ι]
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F : ι → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    jointTestCovariance C (∑ j, F j) G = ∑ j, jointTestCovariance C (F j) G := by
  classical
  induction Finset.univ (α := ι) using Finset.induction_on with
  | empty => simp [jointTestCovariance]
  | @insert j s hj ih => rw [Finset.sum_insert hj, testCov_add_left, ih, Finset.sum_insert hj]

private lemma testCov_sum_right {ι : Type*} [Fintype ι]
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (G : ι → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    jointTestCovariance C F (∑ j, G j) = ∑ j, jointTestCovariance C F (G j) := by
  classical
  induction Finset.univ (α := ι) using Finset.induction_on with
  | empty => simp [jointTestCovariance]
  | @insert j s hj ih => rw [Finset.sum_insert hj, testCov_add_right, ih, Finset.sum_insert hj]

private lemma testCov_coordinate
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (a b : JointObservationIndex d) (ψ φ : SchwartzMap (Vec d) ℂ) :
    jointTestCovariance C (jointCoordinateSchwartz a ψ) (jointCoordinateSchwartz b φ) =
      (∫ x : Vec d, ψ x * φ x) * (C a b : ℂ) := by
  have he (u v : JointObservationIndex d) :
      (∫ x : Vec d, jointCoordinateSchwartz a ψ x u * jointCoordinateSchwartz b φ x v) =
        if u = a then if v = b then ∫ x : Vec d, ψ x * φ x else 0 else 0 := by
    by_cases hu : u = a <;> by_cases hv : v = b <;>
      simp only [jointCoordinateSchwartz_apply, hu, hv, if_true, if_false,
        zero_mul, mul_zero, integral_zero]
  simp only [jointTestCovariance, he, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The covariance contraction of the genuine vector endpoint tests is the
literal velocity profile, for every complex force and every covariance matrix. -/
theorem jointTestCovariance_profile_velocity (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (i : Fin d) (ζ : ℂ) :
    jointTestCovariance C (profileTransposeTest hd Q ζ) (profileVelocityTest hd Q i ζ) =
      velocityGaussianProfile hd Q C i ζ := by
  rw [profileTransposeTest, profileVelocityTest, testCov_smul_left, testCov_add_right,
    testCov_smul_right, testCov_smul_right, testCov_sum_left, testCov_sum_left]
  simp only [testCov_sum_right, testCov_coordinate,
    profileGaussianSchwartz_apply, profileGaussianDerivativeSchwartz_apply]
  have h := velocityGaussianProfile_eq_bilinear_convolution hd Q C i ζ
  dsimp only at h
  rw [← h]
  ring

/-- The clock test uses the actual commutator-clock cross covariance. -/
theorem jointTestCovariance_profile_clock (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (ζ : ℂ) :
    jointTestCovariance C (profileTransposeTest hd Q ζ) (profileClockTest hd Q ζ) =
      clockGaussianProfile hd Q C ζ := by
  simp only [profileTransposeTest, profileClockTest, testCov_smul_left, testCov_smul_right,
    testCov_sum_left, testCov_coordinate, profileGaussianSchwartz_apply,
    profileGaussianDerivativeSchwartz_apply]
  have h := clockGaussianProfile_eq_bilinear_convolution hd Q C ζ
  dsimp only at h
  rw [← h]
  ring

/-- Literal frozen bilinear contraction of the transpose and velocity tests. -/
theorem integral_profileTransposeTest_velocity (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (i : Fin d) (ζ : ℂ) :
    (∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
      profileTransposeTest hd Q ζ x a * (C a b : ℂ) * profileVelocityTest hd Q i ζ x b) =
        velocityGaussianProfile hd Q C i ζ := by
  rw [← jointTestCovariance_eq_integral, jointTestCovariance_profile_velocity]

/-- Literal frozen bilinear contraction, including the commutator-clock entries. -/
theorem integral_profileTransposeTest_clock (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (ζ : ℂ) :
    (∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
      profileTransposeTest hd Q ζ x a * (C a b : ℂ) * profileClockTest hd Q ζ x b) =
        clockGaussianProfile hd Q C ζ := by
  rw [← jointTestCovariance_eq_integral, jointTestCovariance_profile_clock]

/-- The literal joint pairing is linear in its Schwartz test. -/
theorem scaledJointPairing_add (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    scaledJointPairing Q R hR Z (F + G) =
      scaledJointPairing Q R hR Z F + scaledJointPairing Q R hR Z G := by
  have hF := integrable_scaledJointPairing_integrand Q R hR Z F
  have hG := integrable_scaledJointPairing_integrand Q R hR Z G
  simp only [scaledJointPairing, SchwartzMap.add_apply, PiLp.add_apply,
    add_smul, Finset.sum_add_distrib, integral_add hF hG, smul_add]

/-- Complex scalar linearity, with the frozen scale normalization unchanged. -/
theorem scaledJointPairing_smul (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) (c : ℂ) :
    scaledJointPairing Q R hR Z (c • F) = c • scaledJointPairing Q R hR Z F := by
  simp only [scaledJointPairing, SchwartzMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, mul_smul, ← Finset.smul_sum, integral_smul]
  exact smul_comm _ _ _

/-- A coordinate test consumes precisely that coordinate of the joint field. -/
theorem scaledJointPairing_jointCoordinateSchwartz (Q : EnvironmentLaw d Λ₀ r₀)
    (R : ℝ) (hR : 0 < R) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (a : JointObservationIndex d) (ψ : SchwartzMap (Vec d) ℂ) :
    scaledJointPairing Q R hR Z (jointCoordinateSchwartz a ψ) =
      ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
        ∫ x : Vec d, ψ (R⁻¹ • x) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Z a) := by
  simp only [scaledJointPairing, jointCoordinateSchwartz_apply, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The actual frozen covariance characterization gives the velocity limit for
these genuine tests. No rate or uniform force window is asserted here. -/
theorem IsJointCovariance.tendsto_profile_velocity (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (hC : IsJointCovariance Q Z C) (i : Fin d) (ζ : ℂ) :
    Tendsto (fun R : ℝ≥0 =>
      ∫ ω, scaledJointPairing Q ((R : ℝ) + 2) (by positivity) Z (profileTransposeTest hd Q ζ) ω *
        scaledJointPairing Q ((R : ℝ) + 2) (by positivity) Z (profileVelocityTest hd Q i ζ) ω
        ∂reducedLaw Q) atTop (𝓝 (velocityGaussianProfile hd Q C i ζ)) := by
  rw [← jointTestCovariance_profile_velocity, jointTestCovariance_eq_integral]
  exact hC _ _

/-- The corresponding actual joint-covariance limit for the clock cross term. -/
theorem IsJointCovariance.tendsto_profile_clock (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (hC : IsJointCovariance Q Z C) (ζ : ℂ) :
    Tendsto (fun R : ℝ≥0 =>
      ∫ ω, scaledJointPairing Q ((R : ℝ) + 2) (by positivity) Z (profileTransposeTest hd Q ζ) ω *
        scaledJointPairing Q ((R : ℝ) + 2) (by positivity) Z (profileClockTest hd Q ζ) ω
        ∂reducedLaw Q) atTop (𝓝 (clockGaussianProfile hd Q C ζ)) := by
  rw [← jointTestCovariance_profile_clock, jointTestCovariance_eq_integral]
  exact hC _ _

end EinsteinFull
