import EinsteinRelation.Correctors.TensorLocalL2Support
open MeasureTheory
namespace EinsteinRelation.Correctors
private theorem sqrt_le_two_mul_add {I J D : ℝ}
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (h : I ≤ 2 * J + 2 * D ^ 2) :
    Real.sqrt I ≤ 2 * (Real.sqrt J + D) := by
  have hi := Real.sq_sqrt hI
  have hj := Real.sq_sqrt hJ
  have hsi := Real.sqrt_nonneg I
  have hsj := Real.sqrt_nonneg J
  nlinarith [sq_nonneg (Real.sqrt J - D)]
/-- Source: `paper/main.tex:718-723`. Change the scalar gauge using only
local L² membership and the difference of the two constants. -/
theorem root_integral_scalar_gauge_comparison
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (u : X → ℝ) (hu : MemLp u 2 μ) (a b : ℝ) :
    Real.sqrt (∫ x, |u x - b| ^ 2 ∂μ) ≤
      2 * (Real.sqrt (∫ x, |u x - a| ^ 2 ∂μ) +
        Real.sqrt (μ.real Set.univ) * |a - b|) := by
  have hia : Integrable (fun x => (u x - a) ^ 2) μ :=
    (hu.sub (memLp_const a)).integrable_sq
  have hib : Integrable (fun x => (u x - b) ^ 2) μ :=
    (hu.sub (memLp_const b)).integrable_sq
  have hbound : (∫ x, (u x - b) ^ 2 ∂μ) ≤
      2 * (∫ x, (u x - a) ^ 2 ∂μ) + 2 * μ.real Set.univ * (a - b) ^ 2 := by
    calc
      _ ≤ ∫ x, 2 * (u x - a) ^ 2 + 2 * (a - b) ^ 2 ∂μ :=
        integral_mono hib ((hia.const_mul 2).add (integrable_const _))
          (fun x => by nlinarith [sq_nonneg (u x - a - (a - b))])
      _ = _ := by
        rw [integral_add (hia.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const]
        simp only [smul_eq_mul]
        ring
  have hmass : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hs : (Real.sqrt (μ.real Set.univ) * |a - b|) ^ 2 =
      μ.real Set.univ * (a - b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hmass, sq_abs]
  simp only [sq_abs]
  apply sqrt_le_two_mul_add (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  rwa [hs, ← mul_assoc]
/-- Source: `paper/main.tex:733-745`. The corresponding tensor gauge
comparison retains the exact Frobenius norm. -/
theorem root_integral_tensor_gauge_comparison
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {d : ℕ} (u : X → Mat d) (hu : ∀ j k, MemLp (fun x => u x j k) 2 μ)
    (a b : Mat d) :
    Real.sqrt (∫ x, frobeniusNorm (u x - b) ^ 2 ∂μ) ≤
      2 * (Real.sqrt (∫ x, frobeniusNorm (u x - a) ^ 2 ∂μ) +
        Real.sqrt (μ.real Set.univ) * frobeniusNorm (a - b)) := by
  have hia := integrable_frobeniusNorm_sq_of_memLp (fun x => u x - a)
    (fun j k => (hu j k).sub (memLp_const _))
  have hib := integrable_frobeniusNorm_sq_of_memLp (fun x => u x - b)
    (fun j k => (hu j k).sub (memLp_const _))
  have hpoint (x : X) : frobeniusNorm (u x - b) ^ 2 ≤
      2 * frobeniusNorm (u x - a) ^ 2 + 2 * frobeniusNorm (a - b) ^ 2 := by
    simp only [frobeniusNorm_sq_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    simp only [Matrix.sub_apply]
    nlinarith [sq_nonneg (u x j k - a j k - (a j k - b j k))]
  have hbound : (∫ x, frobeniusNorm (u x - b) ^ 2 ∂μ) ≤
      2 * (∫ x, frobeniusNorm (u x - a) ^ 2 ∂μ) +
        2 * μ.real Set.univ * frobeniusNorm (a - b) ^ 2 := by
    calc
      _ ≤ ∫ x, 2 * frobeniusNorm (u x - a) ^ 2 +
          2 * frobeniusNorm (a - b) ^ 2 ∂μ :=
        integral_mono hib ((hia.const_mul 2).add (integrable_const _)) hpoint
      _ = _ := by
        rw [integral_add (hia.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const]
        simp only [smul_eq_mul]
        ring
  have hmass : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hs : (Real.sqrt (μ.real Set.univ) * frobeniusNorm (a - b)) ^ 2 =
      μ.real Set.univ * frobeniusNorm (a - b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hmass]
  apply sqrt_le_two_mul_add (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _) (by unfold frobeniusNorm; positivity)
  rwa [hs, ← mul_assoc]
end EinsteinRelation.Correctors
