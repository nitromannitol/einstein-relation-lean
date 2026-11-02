import EinsteinRelation.Sharpness.SeedDensityLipschitz
import EinsteinRelation.Sharpness.CoefficientLipschitz
import EinsteinRelation.Sharpness.MatrixOperatorLipschitz
import EinsteinRelation.Sharpness.PotentialBounds
namespace EinsteinRelation.Sharpness
private theorem physicalLip_inv (a : ℝ) (ha : (3/4 : ℝ) ≤ a) : |a⁻¹| ≤ (4/3 : ℝ) := by
  have hp : 0 < a := by linarith
  rw [abs_of_pos (inv_pos.mpr hp)]
  have hn : 0 ≤ a⁻¹ := inv_nonneg.mpr hp.le
  have hm : a * a⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) hn]
private theorem physicalLip_inv_sub (a b : ℝ) (ha : (3/4 : ℝ) ≤ a) (hb : (3/4 : ℝ) ≤ b) :
    |a⁻¹-b⁻¹| ≤ 2 * |a-b| := by
  have hpa : 0 < a := by linarith
  have hpb : 0 < b := by linarith
  rw [inv_sub_inv' hpa.ne' hpb.ne', abs_mul, abs_mul, abs_sub_comm b a]
  have h1 := mul_le_mul (physicalLip_inv a ha) (le_refl |a-b|) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4/3)
  have h2 := mul_le_mul h1 (physicalLip_inv b hb) (abs_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 4/3) (abs_nonneg (a-b)))
  nlinarith [abs_nonneg (a-b)]
/-- Source main.tex1218–1231: the actual physical coefficient entries of a fixed scaled seed
are uniformly Lipschitz in Euclidean distance when its actual density is bounded below.
The constant precedes all samples, matrix indices and points. -/
theorem exists_uniform_seedField_physicalCoefficient_entry_euclidean_lipschitz {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) (δ : ℝ)
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3/4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (W : NoiseSample d) (x y : Vec d) (j k : Fin d),
      |physicalCoefficientField i δ (fun z => ε * seedField d W z) x j k -
       physicalCoefficientField i δ (fun z => ε * seedField d W z) y j k| ≤ L * euclideanNorm (x-y) := by
  obtain ⟨A, hA, hALip⟩ := exists_coefficient_euclidean_lipschitz_on_small_gradients d
  obtain ⟨G, hG, hGLip⟩ := exists_uniform_scaled_seedField_gradient_euclidean_lipschitz d ε
  obtain ⟨D, hD, hDLip⟩ := exists_uniform_seedField_density_euclidean_lipschitz i ε hgrad δ
  let C : ℝ := ∑ j : Fin d, ∑ k : Fin d, |coefficient i 0 j k|
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  have hCentry (j k : Fin d) : |coefficient i 0 j k| ≤ C :=
    (Finset.single_le_sum (fun l _ => abs_nonneg (coefficient i 0 j l)) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun n _ => abs_nonneg (coefficient i 0 l n)) (Finset.mem_univ j))
  have hzero : euclideanNorm (0 : Vec d) ≤ (1/4 : ℝ) := by
    norm_num [euclideanNorm, euclideanSq, dot]
  have hbound (W : NoiseSample d) (z : Vec d) (j k : Fin d) :
      |coefficientField i (fun t => ε * seedField d W t) z j k| ≤ C+A/4 := by
    have hl := hALip i _ 0 (hgrad W z) hzero j k
    rw [sub_zero] at hl
    have hs := abs_sub_abs_le_abs_sub (coefficient i (gradient (fun t => ε * seedField d W t) z) j k) (coefficient i 0 j k)
    have hb := mul_le_mul_of_nonneg_left (hgrad W z) hA
    change |coefficient i (gradient (fun t => ε * seedField d W t) z) j k| ≤ _
    linarith [hCentry j k]
  have hB : 0 ≤ C+A/4 := add_nonneg hC (div_nonneg hA (by norm_num))
  refine ⟨(4/3 : ℝ)*(A*G)+2*D*(C+A/4), by positivity, ?_⟩
  intro W x y j k
  let ψ := fun t => ε * seedField d W t
  have hdist : 0 ≤ euclideanNorm (x-y) := Real.sqrt_nonneg _
  have hcoef : |coefficientField i ψ x j k-coefficientField i ψ y j k| ≤ A*G*euclideanNorm (x-y) :=
    (hALip i _ _ (hgrad W x) (hgrad W y) j k).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hGLip W x y) hA)
  have hinv : |(densityField i δ ψ x)⁻¹-(densityField i δ ψ y)⁻¹| ≤ 2*D*euclideanNorm (x-y) :=
    (physicalLip_inv_sub _ _ (hμ W x) (hμ W y)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hDLip W x y) (by norm_num : (0:ℝ) ≤ 2))
  change |(densityField i δ ψ x)⁻¹ * coefficientField i ψ x j k -
    (densityField i δ ψ y)⁻¹ * coefficientField i ψ y j k| ≤ _
  have heq : (densityField i δ ψ x)⁻¹ * coefficientField i ψ x j k -
      (densityField i δ ψ y)⁻¹ * coefficientField i ψ y j k =
      (densityField i δ ψ x)⁻¹ * (coefficientField i ψ x j k-coefficientField i ψ y j k) +
      ((densityField i δ ψ x)⁻¹-(densityField i δ ψ y)⁻¹) * coefficientField i ψ y j k := by ring
  rw [heq]
  calc _ ≤ |(densityField i δ ψ x)⁻¹ * (coefficientField i ψ x j k-coefficientField i ψ y j k)| +
      |((densityField i δ ψ x)⁻¹-(densityField i δ ψ y)⁻¹) * coefficientField i ψ y j k| := abs_add_le _ _
    _ ≤ (4/3 : ℝ)*(A*G*euclideanNorm (x-y)) + (2*D*euclideanNorm (x-y))*(C+A/4) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul (physicalLip_inv _ (hμ W x)) hcoef (abs_nonneg _) (by norm_num))
        (mul_le_mul hinv (hbound W y j k) (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- Actual physical matrix operator Lipschitz regularity, with one constant before all samples.
Source main.tex1218–1231; the bound uses the literal Euclidean operator predicate. -/
theorem exists_uniform_seedField_physicalCoefficient_operator_lipschitz {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) (δ : ℝ)
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3/4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ W : NoiseSample d,
      IsOperatorLipschitz L (physicalCoefficientField i δ (fun y => ε * seedField d W y)) := by
  obtain ⟨L,hL,hentry⟩ := exists_uniform_seedField_physicalCoefficient_entry_euclidean_lipschitz i ε hgrad δ hμ
  exact ⟨(d:ℝ)^2*L, mul_nonneg (sq_nonneg _) hL, fun W =>
    isOperatorLipschitz_of_entrywise _ L hL (fun x y j k => hentry W x y j k)⟩

/-- Actual potential Euclidean Lipschitz regularity, with one constant before all samples.
Source main.tex1231; the actual density Lipschitz estimate is proved inside the consumer. -/
theorem exists_uniform_seedField_potential_euclidean_lipschitz {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ)) (δ : ℝ)
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3/4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (W : NoiseSample d) (x y : Vec d),
      |potentialField i δ (fun z => ε * seedField d W z) x -
       potentialField i δ (fun z => ε * seedField d W z) y| ≤ L * euclideanNorm (x-y) := by
  obtain ⟨L,hL,hLip⟩ := exists_uniform_seedField_density_euclidean_lipschitz i ε hgrad δ
  exact ⟨(2/3:ℝ)*L, mul_nonneg (by norm_num) hL, fun W =>
    potentialField_lipschitz_of_density i δ L _ (hμ W) (hLip W)⟩
end EinsteinRelation.Sharpness
