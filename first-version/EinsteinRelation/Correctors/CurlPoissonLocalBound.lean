import EinsteinRelation.Correctors.PoissonLocalBound
import EinsteinRelation.Correctors.PoissonGradientDivergence
import EinsteinRelation.TimeChange.EuclideanTransport

/-! Source: `paper/main.tex:741-753`. Each flux-corrector entry satisfies
an actual scalar Poisson equation with a curl source. The homogeneous GT
8.17 input suffices for its local value estimate. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- A bounded vector source in the distributional curl equation controls
an actual scalar weak potential on the smaller ball. The constant precedes
all fields, the matrix indices, and the local source bound. -/
theorem curl_poisson_local_bound_of_GT
    (h817 : LocalBoundednessEstimate) (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Vec d → ℝ) (g G : Vec d → Vec d)
      (j k : Fin d), HasWeakGradient Set.univ u g →
      Measurable G → (∀ ℓ, LocallyIntegrable (fun x => G x ℓ) volume) →
      (∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x, u x * (-(∑ ℓ : Fin d,
          coordinateDerivative ℓ (coordinateDerivative ℓ ψ) x))) =
          -(∫ x, G x k * coordinateDerivative j ψ x) +
            ∫ x, G x j * coordinateDerivative k ψ x) →
      ∀ M : ℝ, 0 < M →
      (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), euclideanNorm (G x) ≤ M) →
      MemLp u 2 (volume.restrict (ball 0 1)) →
      MemLp g 2 (volume.restrict (ball 0 1)) →
      ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) (1 / 4)),
        |u x| ≤ C * (Real.sqrt (∫ y in ball (0 : Vec d) 1, |u y| ^ 2) + M) := by
  obtain ⟨C, hC, hbound⟩ := poisson_local_bound_of_GT h817 d hd
  refine ⟨2 * C, by positivity, ?_⟩
  intro u g G j k hw hG hGloc hP M hM hGn hu hg
  let F : Vec d → Vec d := fun x => G x j • unitVector k - G x k • unitVector j
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hFloc (ℓ : Fin d) : LocallyIntegrable (fun x => F x ℓ) volume := by
    have h := ((hGloc j).smul (unitVector k ℓ)).sub ((hGloc k).smul (unitVector j ℓ))
    change LocallyIntegrable
      (fun x => unitVector k ℓ * G x j - unitVector j ℓ * G x k) volume at h
    simpa only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
  have hdot (x : Vec d) (ψ : Vec d → ℝ) :
      dot (F x) (gradient ψ x) = G x j * coordinateDerivative k ψ x -
        G x k * coordinateDerivative j ψ x := by
    change dotProduct (G x j • unitVector k - G x k • unitVector j) (gradient ψ x) = _
    simp [sub_dotProduct, smul_dotProduct, unitVector, single_dotProduct, gradient]
  have hJ : HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0) := by
    apply hasWeakDivergence_gradient_sub_of_poisson hw hFloc
    intro ψ hψ hc
    rw [hP ψ hψ hc]
    have hD (ℓ : Fin d) : Continuous (coordinateDerivative ℓ ψ) :=
      (((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => unitVector ℓ))).continuous
    have hj := (hGloc j).integrable_smul_right_of_hasCompactSupport
      (hD k) (hc.fderiv_apply ℝ (unitVector k))
    have hk := (hGloc k).integrable_smul_right_of_hasCompactSupport
      (hD j) (hc.fderiv_apply ℝ (unitVector j))
    simp only [smul_eq_mul] at hj hk
    simp_rw [hdot]
    rw [integral_sub hj hk]
    ring
  have hn (ℓ : Fin d) : euclideanNorm (unitVector ℓ) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  have hFn : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), euclideanNorm (F x) ≤ 2 * M := by
    filter_upwards [hGn] with x hx
    have h := TimeChange.euclideanNorm_add_le (G x j • unitVector k)
      ((-G x k) • unitVector j)
    rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul, hn, hn,
      abs_neg, mul_one, mul_one] at h
    have heq : F x = G x j • unitVector k + (-G x k) • unitVector j := by
      dsimp [F]; simp only [neg_smul, sub_eq_add_neg]
    rw [heq]
    exact h.trans (by linarith [Regeneration.coordinate_abs_le_euclideanNorm (G x) j,
      Regeneration.coordinate_abs_le_euclideanNorm (G x) k])
  have hb := hbound u g F hw hJ hF (2 * M) (by positivity) hFn hu hg
  filter_upwards [hb] with x hx
  have hs := Real.sqrt_nonneg (∫ y in ball (0 : Vec d) 1, |u y| ^ 2)
  nlinarith

end EinsteinRelation.Correctors
