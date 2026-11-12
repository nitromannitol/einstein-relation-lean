import EinsteinRelation.Calculus.HorizontalCore

/-! # Horizontal integration by parts on actual test orbits

Source `eq.horizontal-ibp`, `paper/main.tex:240–248`, on the bounded smooth core.
Both integral operands are proved integrable. The identity follows from actual
translation invariance and the proved zero-mean product derivative. Extending the
identity to the full source H¹ space is a separate internal closure argument.
-/

open MeasureTheory Filter
noncomputable section
namespace EinsteinRelation

/-- Product rule for the actual coordinate derivative. -/
theorem coordinateDerivative_mul {d : ℕ} (i : Fin d) (f g : Vec d → ℝ) (x : Vec d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    coordinateDerivative i (fun y => f y * g y) x =
      f x * coordinateDerivative i g x + g x * coordinateDerivative i f x := by
  simp only [coordinateDerivative, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Product rule for observables, with derivatives taken along actual translation orbits. -/
theorem horizontalDerivative_mul {d : ℕ} (i : Fin d) (F G : FieldPair d → ℝ)
    (ω : FieldPair d) (hF : DifferentiableAt ℝ (orbit F ω) 0)
    (hG : DifferentiableAt ℝ (orbit G ω) 0) :
    horizontalDerivative i (fun η => F η * G η) ω =
      F ω * horizontalDerivative i G ω + G ω * horizontalDerivative i F ω := by
  change coordinateDerivative i (fun x => orbit F ω x * orbit G ω x) 0 = _
  rw [coordinateDerivative_mul i _ _ _ hF hG, orbit_zero, orbit_zero]
  rfl

/-- Integrability of the actual derivative times a core observable. -/
theorem IsHorizontalTest.integrable_mul_derivative {d : ℕ} {F G : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (hG : IsHorizontalTest G)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (i : Fin d) :
    Integrable (fun ω => F ω * horizontalDerivative i G ω) Q := by
  obtain ⟨B, hB0, hB⟩ := hF.bound_orbit
  obtain ⟨D, _hD0, hD⟩ := hG.bound_derivative i
  refine Integrable.of_bound (hF.1.mul (hG.measurable_derivative i)).aestronglyMeasurable
    (B * D) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hBF : |F ω| ≤ B := by simpa only [orbit_zero] using hB ω 0
  exact mul_le_mul hBF (hD ω 0) (abs_nonneg _) hB0

/-- Horizontal integration by parts on the bounded smooth orbit core.
Full H1 closure/generator-domain equivalence is a separate internal obligation. -/
theorem integral_horizontalDerivative_mul_eq_neg {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (i : Fin d) (F G : FieldPair d → ℝ)
    (hF : IsHorizontalTest F) (hG : IsHorizontalTest G) :
    (∫ ω, F ω * horizontalDerivative i G ω ∂Q) =
      -(∫ ω, G ω * horizontalDerivative i F ω ∂Q) := by
  obtain ⟨B, hB0, hB⟩ := hF.bound_orbit
  obtain ⟨D, _hD0, hD⟩ := hF.bound_derivative i
  obtain ⟨C, hC0, hC⟩ := hG.bound_orbit
  obtain ⟨E, _hE0, hE⟩ := hG.bound_derivative i
  have hf (ω : FieldPair d) (x : Vec d) : DifferentiableAt ℝ (orbit F ω) x :=
    (hF.2.1 ω).differentiable (by simp) |>.differentiableAt
  have hg (ω : FieldPair d) (x : Vec d) : DifferentiableAt ℝ (orbit G ω) x :=
    (hG.2.1 ω).differentiable (by simp) |>.differentiableAt
  have hprod_diff (ω : FieldPair d) (x : Vec d) :
      DifferentiableAt ℝ (orbit (fun η => F η * G η) ω) x :=
    (hf ω x).mul (hg ω x)
  have hprod_bound : ∃ M : ℝ, ∀ ω x, |orbit (fun η => F η * G η) ω x| ≤ M := by
    refine ⟨B * C, fun ω x => ?_⟩
    change |orbit F ω x * orbit G ω x| ≤ B * C
    rw [abs_mul]
    exact mul_le_mul (hB ω x) (hC ω x) (abs_nonneg _) hB0
  have hprod_deriv_bound : ∃ M : ℝ, ∀ ω x,
      |coordinateDerivative i (orbit (fun η => F η * G η) ω) x| ≤ M := by
    refine ⟨B * E + C * D, fun ω x => ?_⟩
    change |coordinateDerivative i (fun y => orbit F ω y * orbit G ω y) x| ≤ _
    rw [coordinateDerivative_mul i _ _ _ (hf ω x) (hg ω x)]
    calc
      |orbit F ω x * coordinateDerivative i (orbit G ω) x +
          orbit G ω x * coordinateDerivative i (orbit F ω) x| ≤
          |orbit F ω x * coordinateDerivative i (orbit G ω) x| +
            |orbit G ω x * coordinateDerivative i (orbit F ω) x| := abs_add_le _ _
      _ = |orbit F ω x| * |coordinateDerivative i (orbit G ω) x| +
          |orbit G ω x| * |coordinateDerivative i (orbit F ω) x| := by rw [abs_mul, abs_mul]
      _ ≤ B * E + C * D := add_le_add
        (mul_le_mul (hB ω x) (hE ω x) (abs_nonneg _) hB0)
        (mul_le_mul (hC ω x) (hD ω x) (abs_nonneg _) hC0)
  have hz := integral_horizontalDerivative_eq_zero_of_bounded Q hQ i
    (fun η => F η * G η) (hF.1.mul hG.1) hprod_diff hprod_bound hprod_deriv_bound
  have heq : horizontalDerivative i (fun η => F η * G η) =
      fun ω => F ω * horizontalDerivative i G ω + G ω * horizontalDerivative i F ω := by
    funext ω
    exact horizontalDerivative_mul i F G ω (hf ω 0) (hg ω 0)
  rw [heq, integral_add (hF.integrable_mul_derivative hG Q i)
    (hG.integrable_mul_derivative hF Q i)] at hz
  linarith only [hz]

end EinsteinRelation
