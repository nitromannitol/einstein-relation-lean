import EinsteinRelation.Correctors.L2MatrixEnergyForm
import EinsteinRelation.Correctors.CoefficientLpEnergy

open MeasureTheory
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- The actual cutoff coefficient energy defines a symmetric continuous form.
Source: `paper/main.tex:798–806`; AKM Lemma 8.2. -/
theorem exists_coefficient_cutoff_energy_form {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (A : Coefficient d K) {U : Set (Vec d)} {χ : Vec d → ℝ}
    (hχ : IsSpatialTest U χ) :
    ∃ B : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U) →L[ℝ] ℝ,
      (∀ f g, B f g = B g f) ∧
      ∀ f g, B f g = ∫ x in U,
        χ x^2 * dot ((A x).mulVec (f x).ofLp) (g x).ofLp := by
  obtain ⟨C,hC⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  let a : Vec d → Mat d := fun x => χ x^2 • A x
  have ha i j : AEStronglyMeasurable (fun x => a x i j) (volume.restrict U) :=
    (hχ.1.continuous.aestronglyMeasurable.pow 2).mul
      ((A.locally_integrable i j).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
  have hsym : ∀ᵐ x ∂volume.restrict U, (a x).transpose = a x := by
    filter_upwards with x
    simp only [a,Matrix.transpose_smul,A.symmetric]
  have hb : ∀ᵐ x ∂volume.restrict U, ∀ i j, |a x i j| ≤ C^2*K := by
    filter_upwards with x
    intro i j
    have hentry : |A x i j| ≤ K := by
      apply abs_entry_le_of_quadratic_bounds hK (A x) (A.symmetric x)
      · intro ξ
        exact (show 0 ≤ euclideanSq ξ from by
          unfold euclideanSq dot
          exact Finset.sum_nonneg fun j _ => mul_self_nonneg _).trans (A.elliptic x ξ).1
      · exact fun ξ => (A.elliptic x ξ).2
    have hχC : |χ x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
    have hC0 : 0 ≤ C := (abs_nonneg _).trans hχC
    have hs : χ x^2 ≤ C^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hχC 2
    change |χ x^2 * A x i j| ≤ _
    rw [abs_mul,abs_sq]
    exact mul_le_mul hs hentry (abs_nonneg _) (sq_nonneg _)
  obtain ⟨B,hBs,hBr⟩ := exists_L2_matrix_energy_form (volume.restrict U) a ha hsym
    (mul_nonneg (sq_nonneg C) hK) hb
  refine ⟨B,hBs,?_⟩
  intro f g
  rw [hBr]
  apply integral_congr_ae
  filter_upwards with x
  simp only [a,Matrix.smul_mulVec,dot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

end EinsteinRelation.Correctors
