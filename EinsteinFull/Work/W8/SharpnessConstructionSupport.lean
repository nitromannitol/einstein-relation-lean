import EinsteinRelation.Sharpness.SharpPhysicalLaw
import EinsteinRelation.Sharpness.InverseIdentification
import EinsteinRelation.Sharpness.ScaledSeedDerivatives
import EinsteinRelation.Sharpness.Energy

/-!
# The explicit deterministic sharpness construction

The fields are the literal scaled convolution, Jacobian coefficient, divergence
clock and physical pair of `paper/main.tex:1526–1584`. The positive scales are
chosen before all distribution samples and spatial points. No probability law
or asymptotic response is assumed or constructed in this module.
-/

open MeasureTheory

namespace EinsteinFull.Work.W8

open EinsteinRelation EinsteinRelation.Sharpness

/-- A deterministic scale for the actual convolution seed. -/
noncomputable def seedScale (d : ℕ) : ℝ :=
  Classical.choose (exists_seedField_gradient_scale d)

theorem seedScale_pos (d : ℕ) : 0 < seedScale d :=
  (Classical.choose_spec (exists_seedField_gradient_scale d)).1

/-- The bounded corrector candidate on genuine distribution samples. -/
noncomputable def corrector {d : ℕ} (W : NoiseSample d) (x : Vec d) : ℝ :=
  seedScale d * seedField d W x

theorem corrector_gradient_bound {d : ℕ} (W : NoiseSample d) (x : Vec d) :
    euclideanNorm (gradient (corrector W) x) ≤ (1 / 4 : ℝ) :=
  (Classical.choose_spec (exists_seedField_gradient_scale d)).2 W x

theorem corrector_contDiff {d : ℕ} (W : NoiseSample d) :
    ContDiff ℝ (⊤ : ℕ∞) (corrector W) :=
  sharpSeed_contDiff (seedScale d) W

theorem corrector_abs_le {d : ℕ} (W : NoiseSample d) (x : Vec d) :
    |corrector W x| ≤ seedScale d :=
  sharpSeed_abs_le (seedScale_pos d) W x

/-- Every coordinate derivative of the actual corrector has a deterministic
bound chosen before the sample and point. -/
theorem exists_corrector_derivative_bound (d : ℕ) (is : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d),
      |iteratedCoordinateDerivative is (corrector W) x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_seedField_derivative_bound d is
  refine ⟨seedScale d * C, mul_nonneg (seedScale_pos d).le hC, fun W x => ?_⟩
  change |iteratedCoordinateDerivative is (fun y => seedScale d * seedField d W y) x| ≤ _
  rw [iteratedCoordinateDerivative_scaled_seedField, abs_mul, abs_of_pos (seedScale_pos d)]
  exact mul_le_mul_of_nonneg_left (hbound W x) (seedScale_pos d).le

/-- A deterministic positive clock parameter for the actual scaled seed. -/
noncomputable def clockParameter {d : ℕ} (i : Fin d) : ℝ :=
  Classical.choose (exists_uniform_seedField_density_parameter_of_gradient_bound
    i (seedScale d) corrector_gradient_bound)

theorem clockParameter_pos {d : ℕ} (i : Fin d) : 0 < clockParameter i :=
  (Classical.choose_spec (exists_uniform_seedField_density_parameter_of_gradient_bound
    i (seedScale d) corrector_gradient_bound)).1

theorem density_bounds {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    (3 / 4 : ℝ) ≤ densityField i (clockParameter i) (corrector W) x ∧
      densityField i (clockParameter i) (corrector W) x ≤ (5 / 4 : ℝ) :=
  (Classical.choose_spec (exists_uniform_seedField_density_parameter_of_gradient_bound
    i (seedScale d) corrector_gradient_bound)).2 W x

theorem density_pos {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    0 < densityField i (clockParameter i) (corrector W) x := by
  linarith [(density_bounds i W x).1]

private theorem jacobian_ne_zero {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    jacobianFactor i (gradient (corrector W) x) ≠ 0 := by
  have hb := (jacobianFactor_bounds i _ (corrector_gradient_bound W x)).1
  have hp : 0 < jacobianFactor i (gradient (corrector W) x) := by linarith
  exact hp.ne'

/-- The concrete physical coefficient and potential, in the canonical carrier. -/
noncomputable def physicalPair {d : ℕ} (i : Fin d) (W : NoiseSample d) : FieldPair d :=
  sharpPhysicalPair i (clockParameter i) (seedScale d)
    corrector_gradient_bound (density_bounds i) W

/-- The concrete map of distributions into physical fields is Borel. -/
theorem measurable_physicalPair {d : ℕ} (i : Fin d) : Measurable (physicalPair i) :=
  measurable_sharpPhysicalPair i (clockParameter i) (seedScale d)
    corrector_gradient_bound (density_bounds i)

/-- Both coordinates are the actual manuscript formulas. -/
theorem physicalPair_apply {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    (physicalPair i W).1 x =
      (densityField i (clockParameter i) (corrector W) x)⁻¹ •
        coefficientField i (corrector W) x ∧
    (physicalPair i W).2 x =
      -(1 / 2 : ℝ) * Real.log (densityField i (clockParameter i) (corrector W) x) :=
  ⟨rfl, rfl⟩

theorem physicalPair_isSmooth {d : ℕ} (i : Fin d) (W : NoiseSample d) :
    IsSmoothFieldPair (physicalPair i W) :=
  sharpPhysicalPair_isSmooth i (clockParameter i) (seedScale d)
    corrector_gradient_bound (density_bounds i) W

/-- One regularity constant precedes every distribution sample. -/
theorem exists_physicalPair_regularity {d : ℕ} (i : Fin d) :
    ∃ Λ : ℝ, 4 ≤ Λ ∧ ∀ W : NoiseSample d, IsRegular Λ (physicalPair i W) :=
  sharpPhysicalPair_regular i (clockParameter i) (seedScale d)
    corrector_gradient_bound (density_bounds i)

/-- Explicit Euclidean symmetry and ellipticity of the physical coefficient. -/
theorem physicalPair_isElliptic {d : ℕ} (i : Fin d) (W : NoiseSample d) :
    IsElliptic 4 ((physicalPair i W).1 : Vec d → Mat d) :=
  physicalCoefficientField_isElliptic i (clockParameter i) (corrector W)
    (corrector_gradient_bound W) (density_bounds i W)

/-- The canonical exponential clock is exactly the constructed divergence clock. -/
theorem physicalPair_clockDensity {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    clockDensity (physicalPair i W) x = densityField i (clockParameter i) (corrector W) x :=
  exp_neg_two_potentialField i (clockParameter i) (corrector W) x (density_pos i W x)

/-- The actual time change recovers the Jacobian coefficient. -/
theorem physicalPair_reducedCoefficient {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    reducedCoefficient (physicalPair i W) x = coefficientField i (corrector W) x :=
  reduce_physicalCoefficientField i (clockParameter i) (corrector W) x (density_pos i W x)

/-- The coefficient uses the true inverse and determinant of the Jacobian. -/
theorem reducedCoefficient_inverse_formula {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (x : Vec d) :
    reducedCoefficient (physicalPair i W) x =
      (jacobian i (gradient (corrector W) x)).det •
        ((jacobian i (gradient (corrector W) x))⁻¹ *
          ((jacobian i (gradient (corrector W) x))⁻¹).transpose) := by
  rw [physicalPair_reducedCoefficient, det_jacobian]
  exact coefficient_eq_inverse_formula i _ (jacobian_ne_zero i W x)

theorem reducedCoefficient_isElliptic {d : ℕ} (i : Fin d) (W : NoiseSample d) :
    IsElliptic 3 (reducedCoefficient (physicalPair i W)) := by
  have heq : reducedCoefficient (physicalPair i W) = coefficientField i (corrector W) :=
    funext (physicalPair_reducedCoefficient i W)
  rw [heq]
  exact coefficientField_isElliptic i (corrector W) (corrector_gradient_bound W)

/-- The bounded smooth candidate has the exact constant harmonic flux. -/
theorem physicalPair_harmonic {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    (reducedCoefficient (physicalPair i W) x).mulVec
      (unitVector i + gradient (corrector W) x) = unitVector i := by
  rw [physicalPair_reducedCoefficient]
  exact coefficientField_harmonic i (corrector W) x (jacobian_ne_zero i W x)

/-- The actual reduced generator obeys the clock identity at every signed force. -/
theorem physicalPair_generator {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (lam : ℝ) (x : Vec d) :
    reducedGenerator i (physicalPair i W) lam (corrector W) x =
      (1 - clockDensity (physicalPair i W) x) / clockParameter i +
        lam * (1 - reducedCoefficient (physicalPair i W) x i i) := by
  have heq : reducedCoefficient (physicalPair i W) = coefficientField i (corrector W) :=
    funext (physicalPair_reducedCoefficient i W)
  rw [physicalPair_clockDensity]
  simp only [reducedGenerator, heq]
  exact clock_generator_identity i (clockParameter i) lam (corrector W)
    (clockParameter_pos i).ne' (jacobian_ne_zero i W) x

/-- The diagonal formula isolates the precise nonnegative clock-energy term. -/
theorem reducedCoefficient_diagonal {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    reducedCoefficient (physicalPair i W) x i i =
      1 - gradient (corrector W) x i + sharpEnergy i (gradient (corrector W) x) := by
  rw [physicalPair_reducedCoefficient]
  exact coefficient_diagonal i _ (jacobian_ne_zero i W x)

/-- For the positive clock parameter, local energy is positive exactly where
this actual corrector has nonzero gradient. No expectation positivity is assumed. -/
theorem clockEnergy_pos_iff {d : ℕ} (i : Fin d) (W : NoiseSample d) (x : Vec d) :
    0 < clockParameter i * sharpEnergy i (gradient (corrector W) x) ↔
      gradient (corrector W) x ≠ 0 := by
  have hj : 0 < 1 + gradient (corrector W) x i := by
    have hb := (jacobianFactor_bounds i _ (corrector_gradient_bound W x)).1
    change (3 / 4 : ℝ) ≤ 1 + gradient (corrector W) x i at hb
    linarith
  rw [mul_pos_iff_of_pos_left (clockParameter_pos i)]
  exact sharpEnergy_pos_iff i _ hj

/-- The harmonic coordinate has exactly constant generator at every signed force.
This is the deterministic identity preceding the stochastic Itô argument. -/
theorem physicalPair_harmonicCoordinate_generator {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (lam : ℝ) (x : Vec d) :
    reducedGenerator i (physicalPair i W) lam (fun y => y i + corrector W y) x = lam := by
  have hgrad : ∀ y, gradient (fun z => z i + corrector W z) y =
      unitVector i + gradient (corrector W) y := by
    intro y
    funext k
    have hc : DifferentiableAt ℝ (fun z : Vec d => z i) y := differentiableAt_apply i y
    have hψ := (corrector_contDiff W).differentiable (by simp) y
    change (fderiv ℝ (fun z : Vec d => z i + corrector W z) y) (unitVector k) =
      unitVector i k + (fderiv ℝ (corrector W) y) (unitVector k)
    rw [fderiv_fun_add hc hψ, ContinuousLinearMap.add_apply, (hasFDerivAt_apply i y).fderiv]
    simp only [ContinuousLinearMap.proj_apply]
    congr 1
    simp only [unitVector, Pi.single_apply, eq_comm]
  have hflux : (fun y => (reducedCoefficient (physicalPair i W) y).mulVec
      (gradient (fun z => z i + corrector W z) y)) = fun _ => unitVector i := by
    funext y
    rw [hgrad]
    exact physicalPair_harmonic i W y
  have hdiv : divergence (fun _ : Vec d => unitVector i) x = 0 := by
    simp only [divergence, coordinateDerivative, fderiv_const_apply,
      ContinuousLinearMap.zero_apply, Finset.sum_const_zero]
  have hpair : dot ((reducedCoefficient (physicalPair i W) x).mulVec (unitVector i))
      (unitVector i + gradient (corrector W) x) = 1 := by
    rw [physicalPair_reducedCoefficient]
    have hp := coefficientField_dot_gradient i (corrector W) x (jacobian_ne_zero i W x)
    have he : dot ((coefficientField i (corrector W) x).mulVec (unitVector i))
        (unitVector i) = coefficientField i (corrector W) x i i := by
      simp [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
    have hadd : ∀ u v w : Vec d, dot u (v + w) = dot u v + dot u w := by
      intro u v w
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hadd, he, hp]
    ring
  unfold reducedGenerator
  rw [hflux, hdiv, hgrad, hpair]
  ring

private theorem iteratedFDeriv_basis {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    iteratedFDeriv ℝ k f x (fun j => unitVector (dirs j)) =
      iteratedCoordinateDerivative (List.ofFn dirs) f x := by
  induction k generalizing x with
  | zero => simp only [List.ofFn_zero, iteratedFDeriv_zero_apply,
      iteratedCoordinateDerivative_nil]
  | succ k ih =>
    rw [List.ofFn_succ, iteratedCoordinateDerivative_cons, iteratedFDeriv_succ_apply_left]
    change (fderiv ℝ (iteratedFDeriv ℝ k f) x) (unitVector (dirs 0))
        (fun j => unitVector (dirs j.succ)) =
      (fderiv ℝ (iteratedCoordinateDerivative (List.ofFn (fun j => dirs j.succ)) f) x)
        (unitVector (dirs 0))
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      hf.differentiable_iteratedFDeriv (mod_cast ENat.coe_lt_top k) x
    rw [← fderiv_continuousMultilinear_apply_const_apply hdiff]
    have heq : (fun y => iteratedFDeriv ℝ k f y (fun j => unitVector (dirs j.succ))) =
        iteratedCoordinateDerivative (List.ofFn (fun j => dirs j.succ)) f :=
      funext (ih (fun j => dirs j.succ))
    rw [heq]

/-- Every Fréchet derivative of the constructed corrector is bounded in the
literal Euclidean multilinear norm, uniformly over all samples and points. -/
theorem exists_corrector_euclidean_derivative_bound (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : NoiseSample d) (x : Vec d) (v : Fin k → Vec d),
      |iteratedFDeriv ℝ k (corrector W) x v| ≤ C * ∏ j, euclideanNorm (v j) := by
  classical
  have hb : ∀ dirs : Fin k → Fin d, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : NoiseSample d) (x : Vec d),
        |iteratedCoordinateDerivative (List.ofFn dirs) (corrector W) x| ≤ C :=
    fun dirs => exists_corrector_derivative_bound d (List.ofFn dirs)
  choose C hC hbound using hb
  refine ⟨∑ dirs, C dirs, Finset.sum_nonneg (fun dirs _ => hC dirs), fun W x v => ?_⟩
  let T := iteratedFDeriv ℝ k (corrector W) x
  have hv (j : Fin k) : (∑ i : Fin d, v j i • unitVector i) = v j := by
    ext i
    simp [unitVector, Pi.single_apply]
  have hexp : T v = ∑ dirs : Fin k → Fin d,
      (∏ j, v j (dirs j)) * T (fun j => unitVector (dirs j)) := by
    calc
      T v = T (fun j => ∑ i : Fin d, v j i • unitVector i) := by
        simp only [hv]
      _ = ∑ dirs : Fin k → Fin d, T (fun j => v j (dirs j) • unitVector (dirs j)) :=
        T.map_sum _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro dirs _
        rw [T.map_smul_univ, smul_eq_mul]
  have hc (j : Fin k) (i : Fin d) : |v j i| ≤ euclideanNorm (v j) := by
    unfold euclideanNorm
    apply Real.abs_le_sqrt
    rw [sq]
    exact Finset.single_le_sum (f := fun i => v j i * v j i)
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ i)
  change |T v| ≤ _
  rw [hexp]
  calc
    |∑ dirs : Fin k → Fin d, (∏ j, v j (dirs j)) * T (fun j => unitVector (dirs j))| ≤
        ∑ dirs : Fin k → Fin d,
          |(∏ j, v j (dirs j)) * T (fun j => unitVector (dirs j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ dirs : Fin k → Fin d, (∏ j, euclideanNorm (v j)) * C dirs := by
      apply Finset.sum_le_sum
      intro dirs _
      rw [abs_mul, Finset.abs_prod]
      have hp : (∏ j, |v j (dirs j)|) ≤ ∏ j, euclideanNorm (v j) :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hc j (dirs j))
      have hT : |T (fun j => unitVector (dirs j))| ≤ C dirs := by
        rw [iteratedFDeriv_basis (corrector_contDiff W)]
        exact hbound dirs W x
      exact mul_le_mul hp hT (abs_nonneg _) (Finset.prod_nonneg (fun j _ => Real.sqrt_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, mul_comm]


end EinsteinFull.Work.W8
