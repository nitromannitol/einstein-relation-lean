import EinsteinRelation.Correctors.WeightedCutoffInterpolation
import EinsteinRelation.Correctors.PairedPDECoercivity

/-! # Interpolation of the actual weighted spatial energy flux

Source: `paper/main.tex:824–832`. Integrating coercivity against a constant
gradient bound avoids requiring measurability of an auxiliary vector field.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The integrable literal flux and energy-class fields obey spatial
coercivity followed by Hölder interpolation. Source: `paper/main.tex:824–832`. -/
theorem integral_energy_flux_interpolation {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) (μ : Measure (Vec d))
    {χ v : Vec d → ℝ} {G D : Vec d → Vec d}
    (hχ : Measurable χ) (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hv : MemLp v 2 μ) (hG : MemLp (fun x => euclideanNorm (G x)) 2 μ)
    {L : ℝ} (hD : ∀ x, euclideanSq (D x) ≤ L ^ 2)
    (n : ℕ) (hn : 2 ≤ n)
    (hP : Integrable (fun x => dot ((A x).mulVec (G x)) (fun j =>
      χ x ^ (2*n) * G x j + 2 * (n : ℝ) * χ x ^ (2*n-1) * v x * D x j)) μ) :
    (-2 * ∫ x, dot ((A x).mulVec (G x)) (fun j =>
      χ x ^ (2*n) * G x j + 2 * (n : ℝ) * χ x ^ (2*n-1) * v x * D x j) ∂μ) +
      (∫ x, χ x ^ (2*n) * euclideanSq (G x) ∂μ) ≤
        (4 * (n : ℝ)^2 * K^2 * L^2) *
          ((∫ x, χ x ^ (2*n) * v x^2 ∂μ) ^ (1 - (n : ℝ)⁻¹) *
            (∫ x, v x^2 ∂μ) ^ ((n : ℝ)⁻¹)) := by
  have hsq : Integrable (fun x => euclideanSq (G x)) μ := by
    simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using hG.integrable_sq
  have hE := hsq.bdd_mul (hχ.pow_const (2*n)).aestronglyMeasurable (by
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hχb x).1 _)]
    exact pow_le_one₀ (hχb x).1 (hχb x).2)
  obtain ⟨herror, hinterp⟩ := integral_cutoff_error_le μ hχ hχb hv n hn
  have hp (x : Vec d) :
      -2 * dot ((A x).mulVec (G x)) (fun j =>
        χ x^(2*n) * G x j + 2*(n : ℝ)*χ x^(2*n-1)*v x*D x j) +
        χ x^(2*n)*euclideanSq (G x) ≤
          (4*(n : ℝ)^2*K^2*L^2) * (χ x^(2*n-2)*(v x)^2) := by
    have hχx := (hχb x).1
    have he := paired_cutoff_coercivity hK A x (G x) (D x) (v x) (χ x)
      (hχb x).1 n (by omega)
    have hd := mul_le_mul_of_nonneg_left (hD x)
      (by positivity : 0 ≤ 4*(n : ℝ)^2*K^2*χ x^(2*n-2)*(v x)^2)
    have hexpand : dot ((A x).mulVec (G x)) (fun j =>
        χ x^(2*n)*G x j + 2*(n : ℝ)*χ x^(2*n-1)*v x*D x j) =
        χ x^(2*n)*dot (G x) ((A x).mulVec (G x)) +
          (2*(n : ℝ)*χ x^(2*n-1)*v x)*dot ((A x).mulVec (G x)) (D x) := by
      change dotProduct ((A x).mulVec (G x))
        (χ x^(2*n) • G x + (2*(n : ℝ)*χ x^(2*n-1)*v x) • D x) = _
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      rw [dotProduct_comm ((A x).mulVec (G x)) (G x)]
      rfl
    rw [hexpand]
    push_cast at he
    nlinarith only [he, hd]
  have hi := integral_mono_ae ((hP.const_mul (-2)).add hE)
    (herror.const_mul (4*(n : ℝ)^2*K^2*L^2)) (Filter.Eventually.of_forall hp)
  dsimp only [Pi.add_apply] at hi
  rw [integral_add (hP.const_mul (-2)) hE, integral_const_mul,
    integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hinterp (by positivity))

end EinsteinRelation.Correctors
