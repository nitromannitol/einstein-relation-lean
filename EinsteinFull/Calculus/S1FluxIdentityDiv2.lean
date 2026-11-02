import EinsteinFull.Calculus.S1FluxIdentityDiv

/-!
# Weak divergence of `a F` against complex tests (support for `e:flux-identity`)
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

theorem fluxId_LI_add {f g : Vec d → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) : LocallyIntegrable (fun x => f x + g x) volume :=
  hf.add hg

theorem fluxId_LI_sub {f g : Vec d → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) : LocallyIntegrable (fun x => f x - g x) volume :=
  hf.sub hg

theorem fluxId_LI_const_mul (c : ℂ) {f : Vec d → ℂ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun x => c * f x) volume :=
  hf.smul c

theorem fluxId_LI_sum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℂ}
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) volume) :
    LocallyIntegrable (fun x => ∑ i ∈ s, f i x) volume :=
  locallyIntegrable_finsetSum s hf

theorem fluxId_LI_D (A : Mat d) {V : Vec d → ℂ} {g J : Fin d → Vec d → ℂ} (ε σ κ c₀ : ℂ)
    (e0 : Fin d) (hg : ∀ m, LocallyIntegrable (g m) volume)
    (hV : LocallyIntegrable V volume) (hJ : ∀ j, LocallyIntegrable (J j) volume) :
    LocallyIntegrable
      (fun x => 2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀))
      volume :=
  fluxId_LI_sub (fluxId_LI_sub (fluxId_LI_const_mul 2 hV)
    (fluxId_LI_const_mul (2 * σ + ε)
      (fluxId_LI_sum Finset.univ fun j _ => fluxId_LI_const_mul (A j e0 : ℂ) (hg j))))
    (fluxId_LI_const_mul (2 * κ) (fluxId_LI_sub (hJ e0) (locallyIntegrable_const c₀)))

theorem fluxId_aFv_ae(a : Vec d → Mat d) (A : Mat d) {u : Vec d → ℂ}
    {g Fv J : Fin d → Vec d → ℂ} (ε : ℂ) (e0 : Fin d)
    (hFvdef : ∀ j x, Fv j x = g j x - ε * (unitVector e0 j : ℂ) * u x)
    (hJrel : ∀ k, ∀ᵐ x ∂(volume : Measure (Vec d)),
      J k x = ∑ j, ((a x k j - A k j : ℝ) : ℂ) * Fv j x) (k : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), (∑ j, (a x k j : ℂ) * Fv j x) =
      ∑ j, (A k j : ℂ) * g j x + J k x - ε * (A k e0 : ℂ) * u x := by
  have hδ : ∑ j, (A k j : ℂ) * (unitVector e0 j : ℂ) = (A k e0 : ℂ) := by
    rw [Finset.sum_eq_single e0]
    · simp [unitVector]
    · intro j _ hj
      simp [unitVector, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ e0) h
  filter_upwards [hJrel k] with x hx
  have hJ' : J k x = ∑ j, ((a x k j : ℂ) - (A k j : ℂ)) *
      (g j x - ε * (unitVector e0 j : ℂ) * u x) := by
    rw [hx]
    exact Finset.sum_congr rfl fun j _ => by rw [hFvdef j x]; push_cast; ring
  have h6 := fluxId_alg6 (fun j => (a x k j : ℂ)) (fun j => (A k j : ℂ)) (fun j => g j x)
    (fun j => (unitVector e0 j : ℂ)) ε (u x) 1 (A k e0 : ℂ) (J k x) hδ hJ'
  simp only [hFvdef]
  simpa only [mul_one] using h6

/-- The weak divergence of `a F` against complex smooth compact tests. -/
theorem fluxId_hDc (a : Vec d → Mat d) (A : Mat d) {u V : Vec d → ℂ}
    {g Fv J : Fin d → Vec d → ℂ} (ε σ κ c₀ : ℂ) (e0 : Fin d)
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
    {θ : Vec d → ℂ} (hθ : FSC θ) :
    ∫ x, (2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀)) * θ x =
      -∫ x, ∑ k, (∑ j, (a x k j : ℂ) * Fv j x) * fderiv ℝ θ x (unitVector k) := by
  have hLD : LocallyIntegrable
      (fun x => 2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀))
      volume :=
    fluxId_LI_sub (fluxId_LI_sub (fluxId_LI_const_mul 2 hV)
      (fluxId_LI_const_mul (2 * σ + ε)
        (fluxId_LI_sum Finset.univ fun j _ => fluxId_LI_const_mul (A j e0 : ℂ) (hg j))))
      (fluxId_LI_const_mul (2 * κ) (fluxId_LI_sub (hJ e0) (locallyIntegrable_const c₀)))
  have hLF : ∀ k, LocallyIntegrable (fun x => ∑ j, (a x k j : ℂ) * Fv j x) volume := by
    intro k
    have h1 : LocallyIntegrable (fun x => ∑ j, (A k j : ℂ) * g j x + J k x -
        ε * (A k e0 : ℂ) * u x) volume :=
      fluxId_LI_sub (fluxId_LI_add
        (fluxId_LI_sum Finset.univ fun j _ => fluxId_LI_const_mul (A k j : ℂ) (hg j)) (hJ k))
        (fluxId_LI_const_mul (ε * (A k e0 : ℂ)) hu)
    exact h1.congr ((fluxId_aFv_ae a A ε e0 hFvdef hJrel k).mono fun x hx => hx.symm)
  have key : ∫ x, (2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x -
        2 * κ * (J e0 x - c₀)) * θ x =
      -∑ k, ∫ x, (∑ j, (a x k j : ℂ) * Fv j x) * fderiv ℝ θ x (unitVector k) :=
    fluxId_complexify
      (fun x => 2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀))
      (fun k x => ∑ j, (a x k j : ℂ) * Fv j x) hLD hLF
      (fun φ hφ hφc => fluxId_div_real a A ε σ κ c₀ e0 hu hg hV hJ hFvdef hGc hJrel he hφ hφc)
      θ hθ.1 hθ.2
  rw [key]
  congr 1
  exact (integral_finsetSum _ fun k _ =>
    fluxId_intT (hLF k) (hθ.deriv (unitVector k)).1.continuous
      (hθ.deriv (unitVector k)).2).symm

end EinsteinFull
