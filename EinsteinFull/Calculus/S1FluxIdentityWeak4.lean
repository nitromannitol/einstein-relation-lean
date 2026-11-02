import EinsteinFull.Calculus.S1FluxIdentityWeak3

/-!
# Weak flux identity: the combined abstract statement
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

/-- The exact flux identity for a field `F` with weak gradient relation to `u`, and weak
divergence `D` of `a F`, in the shape of `e:flux-identity`. -/
theorem fluxId_weak_abstract (i e0 : Fin d)
    (a : Vec d → Mat d) (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hsym : ∀ x, (a x).transpose = a x) (A : Mat d) (hA : A.transpose = A)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (S : Fin d → Fin d → Vec d → ℝ) (hS : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (S k j))
    (hSanti : ∀ k j x, S k j x = -S j k x)
    (G : Vec d → Fin d → ℝ)
    (hG : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, fderiv ℝ φ x (unitVector j) = G x j)
    (hSG : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j,
      (∑ k, fderiv ℝ (fun y => S k j y) x (unitVector k)) =
        (∑ l, a x j l * (unitVector i l + G x l)) - A j i)
    (cφ : ℝ) (cS : Fin d → Fin d → ℝ) (hcS : ∀ k j, cS k j = -cS j k)
    {u : Vec d → ℂ} {g Fv : Fin d → Vec d → ℂ} {ε : ℂ}
    (hu : LocallyIntegrable u volume) (hg : ∀ m, LocallyIntegrable (g m) volume)
    (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (hFvdef : ∀ j x, Fv j x = g j x - ε * (unitVector e0 j : ℂ) * u x)
    (hGc : ∀ m (θ : Vec d → ℂ), FSC θ →
      ∫ x, g m x * θ x = -∫ x, u x * fderiv ℝ θ x (unitVector m))
    (D : Vec d → ℂ) (hD : LocallyIntegrable D volume)
    (hDc : ∀ θ : Vec d → ℂ, FSC θ → ∫ x, D x * θ x =
      -∫ x, ∑ k, (∑ j, (a x k j : ℂ) * Fv j x) * fderiv ℝ θ x (unitVector k))
    {ψ : Vec d → ℂ} (hψ : FSC ψ) :
    (∫ x, (∑ j, ((a x i j - A i j : ℝ) : ℂ) * Fv j x) * ψ x) =
      (∫ x, ((φ x - cφ : ℝ) : ℂ) * D x * ψ x) +
      (∫ x, ((φ x - cφ : ℝ) : ℂ) *
        (∑ k, (∑ j, (a x k j : ℂ) * Fv j x) * fderiv ℝ ψ x (unitVector k))) -
      (∫ x, ∑ k, ∑ j, ((S k j x - cS k j : ℝ) : ℂ) * Fv j x *
        fderiv ℝ ψ x (unitVector k)) +
      ε * ∫ x, (∑ k, ((S k e0 x - cS k e0 : ℝ) : ℂ) * g k x) * ψ x := by
  have hcast : ∀ {f : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)) := fun hf => Complex.ofRealCLM.contDiff.comp hf
  have hφc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((φ x - cφ : ℝ) : ℂ)) :=
    hcast (hφ.sub contDiff_const)
  have hSc : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => ((S k j x - cS k j : ℝ) : ℂ)) :=
    fun k j => hcast ((hS k j).sub contDiff_const)
  have hac : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => (a x k j : ℂ)) :=
    fun k j => hcast (ha k j)
  have hanti : ∀ k j x, ((S k j x - cS k j : ℝ) : ℂ) = -((S j k x - cS j k : ℝ) : ℂ) := by
    intro k j x
    rw [hSanti k j x, hcS k j]
    push_cast
    ring
  have hA' := fluxId_cA hFv (fun k j x => (a x k j : ℂ)) hac
    (fun x => ((φ x - cφ : ℝ) : ℂ)) hφc D hD hDc hψ
  have hB' := fluxId_cB hu hg hFv hFvdef hGc (fun k j x => ((S k j x - cS k j : ℝ) : ℂ))
    hSc hanti hψ (e0 := e0)
  have hdiffφ : ∀ x v, fderiv ℝ (fun y => ((φ y - cφ : ℝ) : ℂ)) x v =
      (fderiv ℝ φ x v : ℂ) := fun x v => by
    rw [fluxId_fderiv_ofReal (f := fun y => φ y - cφ)
      ((hφ.differentiable (by simp) x).sub_const cφ), fderiv_sub_const]
  have hdiffS : ∀ k j x v, fderiv ℝ (fun y => ((S k j y - cS k j : ℝ) : ℂ)) x v =
      (fderiv ℝ (fun y => S k j y) x v : ℂ) := fun k j x v => by
    rw [fluxId_fderiv_ofReal (f := fun y => S k j y - cS k j)
      (((hS k j).differentiable (by simp) x).sub_const (cS k j)), fderiv_sub_const]
  have hC' := fluxId_cC i a ha hsym A hA G Fv hFv
    (fun j x => ∑ k, fderiv ℝ (fun y => ((S k j y - cS k j : ℝ) : ℂ)) x (unitVector k))
    (fun j => ContDiff.sum fun k _ => fluxId_smooth_fderiv (hSc k j) _)
    (by
      filter_upwards [hSG] with x hx j
      simp only [hdiffS]
      rw [← Complex.ofReal_sum, hx j])
    (fun k x => fderiv ℝ (fun y => ((φ y - cφ : ℝ) : ℂ)) x (unitVector k))
    (fun k => fluxId_smooth_fderiv hφc _)
    (by
      filter_upwards [hG] with x hx k
      rw [hdiffφ, hx k])
    hψ
  linear_combination hC' - hA' - hB'

end EinsteinFull
