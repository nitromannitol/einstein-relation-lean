import EinsteinFull.Calculus.ComplexForceAnalyticSupport
import EinsteinFull.Calculus.ComplexTransposeContinuitySupport

/-!
# Force analyticity of the actual transpose and centered operators

Bilinear transposition is a bounded complex linear operator on the space of
bounded L2 operators. The actual reduced-law centering is also bounded and
complex linear. Composition transfers entire force dependence to both objects.
-/

open MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α]

/-- Bilinear transposition preserves sums of bounded complex L2 operators. -/
theorem complexL2Transpose_add (μ : Measure α)
    (A B : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    complexL2Transpose μ (A+B) = complexL2Transpose μ A + complexL2Transpose μ B := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [complexL2Transpose, map_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply]

/-- Actual bilinear transposition as a bounded complex linear map on operators. -/
def complexL2TransposeCLM (μ : Measure α) :
    (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  ({ toFun := complexL2Transpose μ
     map_add' := complexL2Transpose_add μ
     map_smul' := complexL2Transpose_smul μ } :
      (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)).mkContinuous 1
    (fun A => by simpa only [one_mul] using! norm_complexL2Transpose_le μ A)

/-- The bundled transposition evaluates to the actual conjugated Hilbert adjoint. -/
theorem complexL2TransposeCLM_apply (μ : Measure α)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    complexL2TransposeCLM μ A = complexL2Transpose μ A := rfl

/-- Actual bilinear transposition preserves operator-norm analyticity. -/
theorem analyticAt_complexL2Transpose (μ : Measure α)
    {A : ℂ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} {z₀ : ℂ} (hA : AnalyticAt ℂ A z₀) :
    AnalyticAt ℂ (fun z => complexL2Transpose μ (A z)) z₀ :=
  ((complexL2TransposeCLM μ).analyticAt _).comp hA

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}

/-- Every frozen bilinear transpose family is entire in force in operator norm. -/
theorem analyticAt_complexTransposeSemigroup
    {F G : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (hG : ∀ z : ℂ, IsComplexTransposeSemigroup Q (F z) (G z))
    (t : ℝ≥0) (z₀ : ℂ) : AnalyticAt ℂ (fun z => G z t) z₀ := by
  have ha := analyticAt_complexL2Transpose (reducedLaw Q)
    (analyticAt_complexEnvironmentSemigroup hF t z₀)
  apply ha.congr
  apply Eventually.of_forall
  intro z
  exact (congrFun (hG z).eq_complexL2Transpose t).symm

/-- The internally constructed evolution has an entire bilinear transpose. -/
theorem analyticAt_forcedComplexEvolution_transpose (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z =>
      complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i z t)) z₀ :=
  analyticAt_complexL2Transpose _ (analyticAt_forcedComplexEvolution t z₀)

/-- Actual reduced-law centering, bundled as a bounded complex linear map. -/
def centeredComplexLpCLM (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  letI := reducedLaw_probability Q
  ContinuousLinearMap.id ℂ _ - (Lp.constL 2 (reducedLaw Q) ℂ).comp
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2
      (Lp.const 2 (reducedLaw Q) 1))

/-- The bundled projection is exactly the frozen reduced-law centering. -/
theorem centeredComplexLpCLM_apply (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) : centeredComplexLpCLM Q f = centeredComplexLp Q f := by
  letI := reducedLaw_probability Q
  change f - Lp.const 2 (reducedLaw Q)
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2
      (Lp.const 2 (reducedLaw Q) 1) f) =
    f - Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)
  congr 2
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
  simp only [hω, Function.const_apply, ContinuousLinearMap.mul_apply', one_mul]

/-- Applying actual centering on both sides preserves operator-norm analyticity. -/
theorem analyticAt_centeredComplexLpCLM_comp
    {A : ℂ → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)} {z₀ : ℂ}
    (hA : AnalyticAt ℂ A z₀) : AnalyticAt ℂ
      (fun z => (centeredComplexLpCLM Q).comp ((A z).comp (centeredComplexLpCLM Q))) z₀ := by
  have hr := (((ContinuousLinearMap.compL ℂ _ _ _).flip
    (centeredComplexLpCLM Q)).analyticAt _).comp hA
  exact (((ContinuousLinearMap.compL ℂ _ _ _)
    (centeredComplexLpCLM Q)).analyticAt _).comp hr

/-- The actual twice-centered stationary semigroup is entire in operator norm. -/
theorem analyticAt_centered_complexEnvironmentSemigroup
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z)) (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => (centeredComplexLpCLM Q).comp
      ((F z t).comp (centeredComplexLpCLM Q))) z₀ :=
  analyticAt_centeredComplexLpCLM_comp (analyticAt_complexEnvironmentSemigroup hF t z₀)

/-- The actual twice-centered transpose family is entire in operator norm. -/
theorem analyticAt_centered_complexTransposeSemigroup
    {F G : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (hG : ∀ z : ℂ, IsComplexTransposeSemigroup Q (F z) (G z))
    (t : ℝ≥0) (z₀ : ℂ) : AnalyticAt ℂ (fun z => (centeredComplexLpCLM Q).comp
      ((G z t).comp (centeredComplexLpCLM Q))) z₀ :=
  analyticAt_centeredComplexLpCLM_comp (analyticAt_complexTransposeSemigroup hF hG t z₀)

/-- On each actual datum the twice-centered forward orbit is entire in complex force. -/
theorem analyticAt_centered_complexEnvironmentSemigroup_apply
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (t : ℝ≥0) (z₀ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    AnalyticAt ℂ (fun z => centeredComplexLp Q (F z t (centeredComplexLp Q f))) z₀ := by
  have ha := ((ContinuousLinearMap.apply ℂ _ f).analyticAt _).comp
    (analyticAt_centered_complexEnvironmentSemigroup hF t z₀)
  change AnalyticAt ℂ (fun z => centeredComplexLpCLM Q (F z t (centeredComplexLpCLM Q f))) z₀ at ha
  simpa only [centeredComplexLpCLM_apply] using ha

/-- On each actual datum the twice-centered transpose orbit is entire in complex force. -/
theorem analyticAt_centered_complexTransposeSemigroup_apply
    {F G : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (hG : ∀ z : ℂ, IsComplexTransposeSemigroup Q (F z) (G z))
    (t : ℝ≥0) (z₀ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    AnalyticAt ℂ (fun z => centeredComplexLp Q (G z t (centeredComplexLp Q f))) z₀ := by
  have ha := ((ContinuousLinearMap.apply ℂ _ f).analyticAt _).comp
    (analyticAt_centered_complexTransposeSemigroup hF hG t z₀)
  change AnalyticAt ℂ (fun z => centeredComplexLpCLM Q (G z t (centeredComplexLpCLM Q f))) z₀ at ha
  simpa only [centeredComplexLpCLM_apply] using ha

/-- The internally constructed twice-centered forward evolution is entire in operator norm. -/
theorem analyticAt_centered_forcedComplexEvolution (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => (centeredComplexLpCLM Q).comp
      ((forcedComplexEvolution Q i z t).comp (centeredComplexLpCLM Q))) z₀ :=
  analyticAt_centeredComplexLpCLM_comp (analyticAt_forcedComplexEvolution t z₀)

/-- The internally constructed twice-centered transpose is entire in operator norm. -/
theorem analyticAt_centered_forcedComplexEvolution_transpose (t : ℝ≥0) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => (centeredComplexLpCLM Q).comp
      ((complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i z t)).comp
        (centeredComplexLpCLM Q))) z₀ :=
  analyticAt_centeredComplexLpCLM_comp (analyticAt_forcedComplexEvolution_transpose t z₀)

end EinsteinFull
