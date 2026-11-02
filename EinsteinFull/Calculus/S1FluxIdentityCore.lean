import EinsteinFull.Calculus.S1FluxIdentityWeak4
import EinsteinFull.Calculus.S1FluxIdentityDiv2

/-!
# Pathwise core of `e:flux-identity`

For one fixed environment: the endpoint flux identity from a weak gradient relation, the
centered equation (as a weak divergence identity) and the flux relation `J = (a - A) F`.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

theorem fluxId_core (i e0 : Fin d) (a : Vec d → Mat d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
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
    {u V : Vec d → ℂ} {g Fv J : Fin d → Vec d → ℂ} (ε σ κ c₀ : ℂ)
    (hu : LocallyIntegrable u volume) (hg : ∀ m, LocallyIntegrable (g m) volume)
    (hV : LocallyIntegrable V volume) (hJ : ∀ j, LocallyIntegrable (J j) volume)
    (hFvdef : ∀ j x, Fv j x = g j x - ε * (unitVector e0 j : ℂ) * u x)
    (hGc : ∀ m (θ : Vec d → ℂ), FSC θ →
      ∫ x, g m x * θ x = -∫ x, u x * fderiv ℝ θ x (unitVector m))
    (hJrel : ∀ k, ∀ᵐ x ∂(volume : Measure (Vec d)),
      J k x = ∑ j, ((a x k j - A k j : ℝ) : ℂ) * Fv j x)
    (he : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, V x * (φ x : ℂ)) +
        (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (A j k : ℂ) * g k x * (fderiv ℝ φ x (unitVector j) : ℂ)) -
        σ * (∫ x, (∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, J j x * (fderiv ℝ φ x (unitVector j) : ℂ)) +
        κ * (∫ x, (J e0 x - c₀) * (φ x : ℂ)))
    (Dd : Vec d → ℂ)
    (hDm : ∀ᵐ x ∂(volume : Measure (Vec d)),
      2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀) = Dd x)
    {ψ : Vec d → ℂ} (hψ : FSC ψ) (L : ℂ)
    (hLd : L = ε * ∫ x, (∑ k, ((S k e0 x - cS k e0 : ℝ) : ℂ) * g k x) * ψ x) :
    (∫ x, J i x * ψ x) =
      (∫ x, ((φ x - cφ : ℝ) : ℂ) * Dd x * ψ x) +
      (∫ x, ((φ x - cφ : ℝ) : ℂ) *
        (∑ k, (∑ j, (a x k j : ℂ) * Fv j x) * fderiv ℝ ψ x (unitVector k))) -
      (∫ x, ∑ k, ∑ j, ((S k j x - cS k j : ℝ) : ℂ) * Fv j x *
        fderiv ℝ ψ x (unitVector k)) +
      L := by
  have hFv : ∀ j, LocallyIntegrable (Fv j) volume := by
    intro j
    have e : Fv j = fun x => g j x - ε * (unitVector e0 j : ℂ) * u x := funext (hFvdef j)
    rw [e]
    exact fluxId_LI_sub (hg j) (fluxId_LI_const_mul (ε * (unitVector e0 j : ℂ)) hu)
  have hDl : LocallyIntegrable Dd volume :=
    (fluxId_LI_D A ε σ κ c₀ e0 hg hV hJ).congr hDm
  have hDc : ∀ θ : Vec d → ℂ, FSC θ → ∫ x, Dd x * θ x =
      -∫ x, ∑ k, (∑ j, (a x k j : ℂ) * Fv j x) * fderiv ℝ θ x (unitVector k) := by
    intro θ hθ
    have h1 := fluxId_hDc a A ε σ κ c₀ e0 hu hg hV hJ hFvdef hGc hJrel he hθ
    have h2 : ∫ x, (2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x -
        2 * κ * (J e0 x - c₀)) * θ x = ∫ x, Dd x * θ x :=
      integral_congr_ae (hDm.mono fun x hx => by simp only [hx])
    rw [← h2]
    exact h1
  have habs := fluxId_weak_abstract i e0 a ha hsym A hA φ hφ S hS hSanti G hG hSG cφ cS hcS
    hu hg hFv hFvdef hGc Dd hDl hDc hψ
  have hL : ∫ x, J i x * ψ x =
      ∫ x, (∑ j, ((a x i j - A i j : ℝ) : ℂ) * Fv j x) * ψ x :=
    integral_congr_ae ((hJrel i).mono fun x hx => by simp only [hx])
  rw [hL, habs, hLd]

end EinsteinFull
