import EinsteinRelation.Correctors.PoissonGradientDivergence

/-! Source: `paper/main.tex:733-745`. Distributional curl equations
supply the divergence-free flux required by the scalar Poisson estimate. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- An actual weak potential of a curl source gives the corresponding
zero-divergence Poisson flux, with the manuscript's signs. -/
theorem hasWeakDivergence_gradient_sub_curl_of_poisson {d : ℕ}
    {u : Vec d → ℝ} {g G : Vec d → Vec d} (j k : Fin d)
    (hw : HasWeakGradient Set.univ u g)
    (hGloc : ∀ ℓ, LocallyIntegrable (fun x => G x ℓ) volume)
    (hP : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, u x * (-(∑ ℓ : Fin d,
        coordinateDerivative ℓ (coordinateDerivative ℓ ψ) x))) =
          -(∫ x, G x k * coordinateDerivative j ψ x) +
            ∫ x, G x j * coordinateDerivative k ψ x) :
    HasWeakDivergence Set.univ
      (fun x => g x - (G x j • unitVector k - G x k • unitVector j))
      (fun _ => 0) := by
  let F : Vec d → Vec d := fun x => G x j • unitVector k - G x k • unitVector j
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
  show HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0)
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

end EinsteinRelation.Correctors
