import EinsteinFull.Blueprint.G3.GaussianFourierMoments
import EinsteinFull.Work.W3.GaussianJointProfileTestSupport
import EinsteinFull.Blueprint.G3.node_e_u3A_fourier
import EinsteinFull.Blueprint.Roots.node_p_u3A_covariance

/-! Exact Gaussian Fourier evaluation for graph node `e:fourier`.
The literal reflected endpoint tests agree with the adopted Schwartz tests.
Their spatial covariance and Fourier moments give the frozen profiles with
the actual anisotropic matrix and bilinear covariance, for every complex force. -/

noncomputable section
namespace EinsteinFull.Blueprint.GaussianFourier
open EinsteinRelation EinsteinFull MeasureTheory
open scoped BigOperators MatrixOrder

variable {d : ℕ}

lemma reflected_kernel_derivative {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (z : ℂ) (x : Vec d) :
    iteratedFDeriv ℝ 1 (homogenizedGaussianKernel Q i (1 / 2) (by norm_num) z)
      (-x) (fun _ => unitVector j) =
      -fderiv ℝ (homogenizedGaussianKernel Q i (1 / 2) (by norm_num) (-z)) x
        (unitVector j) := by
  rw [iteratedFDeriv_one_apply]
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    ← homogenizedGaussianKernel_neg_force]
  simp only [Matrix.mulVec_neg, Pi.neg_apply, Complex.ofReal_neg]
  ring

/-- The endpoint tests written literally in the reviewed graph contract. -/
def endpointTest {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (z : ℂ) (ν : EndpointIndex d) (x : Vec d) (a : JointObservationIndex d) : ℂ :=
  let first : Fin d := ⟨0, by omega⟩
  let kernel := fun w => homogenizedGaussianKernel Q first (1 / 2) (by norm_num) w
  let kernelDeriv := fun w j x =>
    iteratedFDeriv ℝ 1 (kernel w) (-x) (fun _ => unitVector j)
  match ν, a with
  | .inr true, .inl (j,k) => if k = first then (1 / 2 : ℂ) * kernelDeriv z j x else 0
  | .inl i, .inl (j,k) => if k = i then
      (1 / 2 : ℂ) * kernelDeriv (-z) j x +
        (if j = first then z * kernel z x else 0) else 0
  | .inr false, .inr () => z * kernel z x
  | _, _ => 0

private lemma schwartz_sum_apply {ι : Type*} [Fintype ι]
    (F : ι → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (x : Vec d) (a : JointObservationIndex d) :
    (∑ j, F j) x a = ∑ j, F j x a := by
  have h : (∑ j, F j) x = ∑ j, F j x := by
    simp only [sum_apply]
  rw [h, WithLp.ofLp_sum, Finset.sum_apply]

lemma endpointTest_transpose {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (z : ℂ) (x : Vec d) (a : JointObservationIndex d) :
    endpointTest hd Q z (.inr true) x a = profileTransposeTest hd Q z x a := by
  cases a with
  | inl a =>
    rcases a with ⟨j,k⟩
    dsimp only [endpointTest]
    simp only [reflected_kernel_derivative]
    simp [profileTransposeTest, schwartz_sum_apply,
      PiLp.smul_apply, jointCoordinateSchwartz_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs <;> simp_all
    all_goals ring
  | inr a =>
    simp [endpointTest, profileTransposeTest, schwartz_sum_apply,
      PiLp.smul_apply, jointCoordinateSchwartz_apply, smul_eq_mul]

lemma endpointTest_velocity {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (z : ℂ) (i : Fin d) (x : Vec d) (a : JointObservationIndex d) :
    endpointTest hd Q z (.inl i) x a = profileVelocityTest hd Q i z x a := by
  cases a with
  | inl a =>
    rcases a with ⟨j,k⟩
    dsimp only [endpointTest]
    simp only [reflected_kernel_derivative]
    simp [profileVelocityTest, schwartz_sum_apply,
      PiLp.smul_apply, jointCoordinateSchwartz_apply, Prod.mk.injEq, smul_eq_mul]
    split_ifs <;> simp_all
    all_goals ring
  | inr a =>
    simp [endpointTest, profileVelocityTest, schwartz_sum_apply,
      PiLp.smul_apply, jointCoordinateSchwartz_apply, smul_eq_mul]

lemma endpointTest_clock {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (z : ℂ) (x : Vec d) (a : JointObservationIndex d) :
    endpointTest hd Q z (.inr false) x a = profileClockTest hd Q z x a := by
  cases a <;> simp [endpointTest, profileClockTest, PiLp.smul_apply,
    jointCoordinateSchwartz_apply, smul_eq_mul]

/-- Exact Fourier evaluation of the endpoint tests, with no stochastic premise. -/
lemma endpoint_fourier_identity {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (C : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ) (z : ℂ) :
    let first : Fin d := ⟨0, by omega⟩
    let A := homogenizedCoefficient Q
    let N : ℂ := ((2 * Real.pi) ^ (-(d : ℝ)) : ℝ)
    let cov := fun ν => ∫ x : Vec d,
      ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
        endpointTest hd Q z (.inr true) x a * (C a b : ℂ) * endpointTest hd Q z ν x b
    (∀ i : Fin d,
      cov (.inl i) = N * (∫ k : Vec d, density A first z k *
        ((1 / 4 : ℂ) * ∑ j : Fin d, ∑ l : Fin d,
          (k j : ℂ) * (k l : ℂ) * (C (.inl (j,first)) (.inl (l,i)) : ℂ))) +
        N * (∫ k : Vec d, density A first z k *
          ((1 / 2 : ℂ) * Complex.I * z * ∑ j : Fin d,
            (k j : ℂ) * (C (.inl (j,first)) (.inl (first,i)) : ℂ))) ∧
      cov (.inl i) = velocityGaussianProfile hd Q C i z) ∧
    cov (.inr false) = N * (z / 2) * (∫ k : Vec d,
      density A first z k * (Complex.I * ∑ j : Fin d,
        (k j : ℂ) * (C (.inl (j,first)) (.inr ()) : ℂ))) ∧
    cov (.inr false) = clockGaussianProfile hd Q C z ∧
    (∀ i, Differentiable ℂ (velocityGaussianProfile hd Q C i)) ∧
    Differentiable ℂ (clockGaussianProfile hd Q C) := by
  dsimp only
  let first : Fin d := ⟨0, by omega⟩
  have hv (i : Fin d) : (∫ x : Vec d,
      ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
        endpointTest hd Q z (.inr true) x a * (C a b : ℂ) * endpointTest hd Q z (.inl i) x b) =
        velocityGaussianProfile hd Q C i z := by
    simp_rw [endpointTest_transpose, endpointTest_velocity]
    exact integral_profileTransposeTest_velocity hd Q C i z
  have hc : (∫ x : Vec d,
      ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
        endpointTest hd Q z (.inr true) x a * (C a b : ℂ) * endpointTest hd Q z (.inr false) x b) =
        clockGaussianProfile hd Q C z := by
    simp_rw [endpointTest_transpose, endpointTest_clock]
    exact integral_profileTransposeTest_clock hd Q C z
  have hfv (i : Fin d) := velocity_fourier_contraction (homogenizedCoefficient Q)
    (posDef_homogenizedCoefficient Q) first z
    (fun j l => (C (.inl (j,first)) (.inl (l,i)) : ℂ))
  have hfc := clock_fourier_contraction (homogenizedCoefficient Q)
    (posDef_homogenizedCoefficient Q) first z
    (fun j => (C (.inl (j,first)) (.inr ()) : ℂ))
  change _ = clockGaussianProfile hd Q C z at hfc
  refine ⟨fun i => ⟨?_, hv i⟩, hc.trans hfc.symm, hc, ?_, ?_⟩
  · refine (hv i).trans ?_
    simpa only [velocityGaussianProfile, Complex.ofReal_sum, Complex.ofReal_mul] using
      (hfv i).symm
  · intro i
    unfold velocityGaussianProfile
    fun_prop
  · unfold clockGaussianProfile
    fun_prop

end EinsteinFull.Blueprint.GaussianFourier

namespace EinsteinFull.Blueprint
open EinsteinRelation MeasureTheory

/-- Graph node `e:fourier`, paper/main.tex:1246–1273. The covariance
construction is its graph dependency; this deterministic Gaussian evaluation
in fact holds for every real covariance matrix. The unused premise is retained
solely to preserve the exact ordered graph interface. -/
@[nolint unusedArguments]
theorem node_e_u3A_fourier_of_deps (_hcov : node_p_u3A_covarianceStmt) :
    node_e_u3A_fourierStmt := by
  intro d hd D Q _ Z C _ _ z
  simpa only [node_e_u3A_fourierStmt, GaussianFourier.endpointTest,
    GaussianFourier.density, GaussianFourier.quadratic, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc] using!
    GaussianFourier.endpoint_fourier_identity hd Q C z

end EinsteinFull.Blueprint
