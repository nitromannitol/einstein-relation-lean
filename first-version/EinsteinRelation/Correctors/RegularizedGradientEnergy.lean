import EinsteinRelation.Correctors.SymmetricEnergyDerivative
import EinsteinRelation.Correctors.LocalizedEnergyYoung
import EinsteinRelation.Correctors.WeakDivergenceH1Testing
import EinsteinRelation.Correctors.EuclideanCoordinateCharacterization

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Testing the actual elliptic time derivative controls the derivative of
localized coefficient energy. Source: `paper/main.tex:798–806`; AKM Lemma 8.2. -/
theorem regularized_gradient_energy_derivative_le {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (a : Vec d → Mat d)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (B : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U) →L[ℝ] ℝ)
    (hsym : ∀ f g, B f g = B g f)
    (hB : ∀ f g, B f g = ∫ x in U,
      χ x ^ 2 * dot ((a x).mulVec (f x).ofLp) (g x).ofLp)
    {g : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U)}
    {g' : Lp (EuclideanSpace ℝ (Fin d)) 2 (volume.restrict U)}
    {v : Vec d → ℝ} {t : ℝ} (hd : HasDerivAt g g' t)
    (hv : MemLp v 2 (volume.restrict U))
    (hw : HasWeakGradient U v (fun x => (g' x).ofLp))
    (hF : ∀ i, MemLp (fun x => (a x).mulVec (g t x).ofLp i) 2 (volume.restrict U))
    (hdiv : HasWeakDivergence U (fun x => (a x).mulVec (g t x).ofLp) v) :
    deriv (fun s => B (g s) (g s)) t ≤
      2 * (∫ x in U, (dot ((a x).mulVec (g t x).ofLp) (gradient χ x))^2) := by
  let F : Vec d → Vec d := fun x => (a x).mulVec (g t x).ofLp
  let w : Vec d → ℝ := fun x => dot (F x) (gradient χ x)
  have hD (i : Fin d) : MemLp (fun x => g' x i) 2 (volume.restrict U) :=
    (memLp_euclidean_iff_coordinates _ _).mp (Lp.memLp g') i
  obtain ⟨hwm,hvv,hvw,he⟩ := localized_H1_energy_products_integrable hχ hv hF hD
  have htest := weakDivergence_test_cutoff_H1 hU hv hD hF hv hw hdiv hχ
  have heq : (∫ x in U, dot (F x)
      (fun i => χ x ^ 2 * (g' x).ofLp i + 2 * χ x * v x * coordinateDerivative i χ x)) =
      (∫ x in U, χ x ^ 2 * dot (F x) (g' x).ofLp) +
        2 * (∫ x in U, χ x * v x * w x) := by
    rw [← integral_const_mul, ← integral_add he (hvw.const_mul 2)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [w]
      simp only [dot, gradient, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  have hrhs : (∫ x in U, v x * (χ x ^ 2 * v x)) = ∫ x in U, χ x ^ 2 * v x ^ 2 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  change _ = -(∫ x in U, v x * (χ x ^ 2 * v x)) at htest
  rw [heq,hrhs] at htest
  have hder := hasDerivAt_symmetric_bilinear_energy B hsym hd
  rw [hder.deriv, hB]
  have hy := integral_localized_energy_young (volume.restrict U) χ v w
    hvv hvw hwm.integrable_sq
  change 2 * (∫ x in U, χ x ^ 2 * dot (F x) (g' x).ofLp) ≤ _
  linarith only [htest, hy]

end EinsteinRelation.Correctors
