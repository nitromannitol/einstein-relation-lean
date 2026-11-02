import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import Mathlib.Topology.Algebra.Module.Star

/-!
# The actual bilinear transpose on complex L2

Lift scalar conjugation as a bounded semilinear map, then conjugate the Hilbert
adjoint on both sides. The resulting operator is complex linear and satisfies
the actual bilinear integral pairing in the frozen transpose predicate.
-/

open MeasureTheory
open scoped NNReal

noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α]

/-- Pointwise conjugation on actual complex L2, bundled as a bounded star-linear map. -/
def complexL2Conjugation (μ : Measure α) : Lp ℂ 2 μ →L⋆[ℂ] Lp ℂ 2 μ :=
  (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.compLpL 2 μ

/-- The bundled conjugation agrees with the existing Lp star operation. -/
theorem complexL2Conjugation_apply (μ : Measure α) (f : Lp ℂ 2 μ) :
    complexL2Conjugation μ f = star f := by
  apply Lp.ext
  exact ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.coeFn_compLpL f).trans
    (Lp.coeFn_star f).symm

/-- Applying the actual L2 conjugation twice is the identity. -/
theorem complexL2Conjugation_involutive (μ : Measure α) (f : Lp ℂ 2 μ) :
    complexL2Conjugation μ (complexL2Conjugation μ f) = f := by
  simp only [complexL2Conjugation_apply, star_star]

/-- Actual complex L2 conjugation preserves the norm. -/
theorem norm_complexL2Conjugation (μ : Measure α) (f : Lp ℂ 2 μ) :
    ‖complexL2Conjugation μ f‖ = ‖f‖ := by
  rw [complexL2Conjugation_apply, Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

/-- The Hermitian pairing with conjugation is the actual bilinear integral. -/
theorem inner_complexL2Conjugation_eq_integral_mul (μ : Measure α) (f g : Lp ℂ 2 μ) :
    inner ℂ (complexL2Conjugation μ f) g = ∫ x, f x * g x ∂μ := by
  rw [complexL2Conjugation_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with x hx
  change (star f) x = star (f x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

/-- The bilinear transpose is conjugation composed with the Hilbert adjoint and conjugation. -/
def complexL2Transpose (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (complexL2Conjugation μ).comp ((ContinuousLinearMap.adjoint A).comp (complexL2Conjugation μ))

/-- The constructed transpose satisfies the paper's bilinear integral identity. -/
theorem integral_complexL2Transpose (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (f g : Lp ℂ 2 μ) :
    (∫ x, A f x * g x ∂μ) = ∫ x, f x * complexL2Transpose μ A g x ∂μ := by
  calc
    _ = inner ℂ (complexL2Conjugation μ g) (A f) := by
      rw [inner_complexL2Conjugation_eq_integral_mul]
      congr 1
      ext x
      exact mul_comm _ _
    _ = inner ℂ (ContinuousLinearMap.adjoint A (complexL2Conjugation μ g)) f :=
      (A.adjoint_inner_left f (complexL2Conjugation μ g)).symm
    _ = inner ℂ (complexL2Conjugation μ (complexL2Transpose μ A g)) f := by
      simp only [complexL2Transpose, ContinuousLinearMap.comp_apply,
        complexL2Conjugation_involutive]
    _ = _ := by
      rw [inner_complexL2Conjugation_eq_integral_mul]
      congr 1
      ext x
      exact mul_comm _ _

/-- A bounded complex linear map is determined by all its bilinear L2 tests. -/
theorem complexL2Transpose_unique (μ : Measure α)
    (A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (h : ∀ f g, (∫ x, A f x * g x ∂μ) = ∫ x, f x * B g x ∂μ) :
    B = complexL2Transpose μ A := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  have he := (h (complexL2Conjugation μ f) g).symm.trans
    (integral_complexL2Transpose μ A (complexL2Conjugation μ f) g)
  simpa only [← inner_complexL2Conjugation_eq_integral_mul,
    complexL2Conjugation_involutive] using he

/-- Transposition reverses operator composition. -/
theorem complexL2Transpose_comp (μ : Measure α)
    (A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    complexL2Transpose μ (A.comp B) =
      (complexL2Transpose μ B).comp (complexL2Transpose μ A) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [complexL2Transpose, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, complexL2Conjugation_involutive]

/-- The transpose of the identity is the identity. -/
theorem complexL2Transpose_id (μ : Measure α) :
    complexL2Transpose μ (ContinuousLinearMap.id ℂ (Lp ℂ 2 μ)) =
      ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [complexL2Transpose, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    complexL2Conjugation_involutive]

/-- Taking the bilinear transpose twice returns the original bounded operator. -/
theorem complexL2Transpose_involutive (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    complexL2Transpose μ (complexL2Transpose μ A) = A := by
  symm
  apply complexL2Transpose_unique
  intro f g
  calc
    _ = ∫ x, g x * complexL2Transpose μ A f x ∂μ := by
      congr 1
      ext x
      exact mul_comm _ _
    _ = ∫ x, A g x * f x ∂μ := (integral_complexL2Transpose μ A g f).symm
    _ = _ := by
      congr 1
      ext x
      exact mul_comm _ _

/-- Conjugating the Hilbert adjoint does not increase the operator norm. -/
theorem norm_complexL2Transpose_le (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    ‖complexL2Transpose μ A‖ ≤ ‖A‖ := by
  apply (complexL2Transpose μ A).opNorm_le_bound (norm_nonneg A)
  intro f
  change ‖complexL2Conjugation μ (ContinuousLinearMap.adjoint A (complexL2Conjugation μ f))‖ ≤ _
  rw [norm_complexL2Conjugation, ← ContinuousLinearMap.adjoint.norm_map A]
  simpa only [norm_complexL2Conjugation] using
    (ContinuousLinearMap.adjoint A).le_opNorm (complexL2Conjugation μ f)

/-- The actual bilinear transpose preserves the operator norm exactly. -/
theorem norm_complexL2Transpose (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    ‖complexL2Transpose μ A‖ = ‖A‖ := by
  apply le_antisymm (norm_complexL2Transpose_le μ A)
  have h := norm_complexL2Transpose_le μ (complexL2Transpose μ A)
  rwa [complexL2Transpose_involutive] at h

open EinsteinRelation

/-- Every bounded operator family has the actual frozen bilinear transpose. -/
theorem isComplexTransposeSemigroup_complexL2Transpose {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) :
    IsComplexTransposeSemigroup Q P (fun t => complexL2Transpose (reducedLaw Q) (P t)) :=
  fun t => integral_complexL2Transpose (reducedLaw Q) (P t)

/-- The full bilinear transpose predicate determines every operator in the family. -/
theorem IsComplexTransposeSemigroup.eq_complexL2Transpose {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R) :
    R = fun t => complexL2Transpose (reducedLaw Q) (P t) := by
  funext t
  exact complexL2Transpose_unique (reducedLaw Q) (P t) (R t) (hR t)

/-- Families with the same complete bilinear transpose pairing agree. -/
theorem IsComplexTransposeSemigroup.unique {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀}
    {P R S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hS : IsComplexTransposeSemigroup Q P S) : R = S :=
  hR.eq_complexL2Transpose.trans hS.eq_complexL2Transpose.symm

/-- Every operator in a frozen transpose family has exactly the forward operator norm. -/
theorem IsComplexTransposeSemigroup.norm_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R) (t : ℝ≥0) : ‖R t‖ = ‖P t‖ := by
  rw [hR.eq_complexL2Transpose]
  exact norm_complexL2Transpose (reducedLaw Q) (P t)

/-- The frozen bilinear transpose of a complete stationary semigroup starts at the identity. -/
theorem IsComplexTransposeSemigroup.zero {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) : R 0 = ContinuousLinearMap.id ℂ _ := by
  simp only [hR.eq_complexL2Transpose, hP.1, complexL2Transpose_id]

/-- The frozen bilinear transpose inherits the semigroup law. -/
theorem IsComplexTransposeSemigroup.add {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (s t : ℝ≥0) :
    R (s+t) = (R s).comp (R t) := by
  simp only [hR.eq_complexL2Transpose]
  rw [add_comm s t, hP.2.1, complexL2Transpose_comp]

/-- The structural quadratic-force growth estimate holds for every frozen transpose family. -/
theorem IsComplexTransposeSemigroup.norm_le {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexTransposeSemigroup Q P R)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) :
    ‖R t‖ ≤ Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) := by
  rw [hR.norm_eq]
  exact hP.norm_le t

end EinsteinFull
