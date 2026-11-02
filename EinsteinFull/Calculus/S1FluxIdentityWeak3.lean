import EinsteinFull.Calculus.S1FluxIdentityWeak2

/-!
# Weak flux identity: the scalar-potential and flux-potential steps
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

theorem fluxId_split_gen {Fv : Fin d → Vec d → ℂ} (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (acx : Fin d → Fin d → Vec d → ℂ) (hacx : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (acx k j))
    {τ : Fin d → Vec d → ℂ} (hτ : ∀ k, FSC (τ k)) :
    ∫ x, ∑ k, (∑ j, acx k j x * Fv j x) * τ k x =
      ∑ k, ∑ j, ∫ x, Fv j x * (acx k j x * τ k x) := by
  have iF : ∀ k j, Integrable (fun x => Fv j x * (acx k j x * τ k x)) := fun k j =>
    fluxId_intT (hFv j) (FSC.mul_left (hacx k j) (hτ k)).1.continuous
      (FSC.mul_left (hacx k j) (hτ k)).2
  have e : (fun x => ∑ k, (∑ j, acx k j x * Fv j x) * τ k x) =
      fun x => ∑ k, ∑ j, Fv j x * (acx k j x * τ k x) := by
    funext x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ => iF k j)]
  exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun j _ => iF k j

theorem fluxId_split2 {Fv : Fin d → Vec d → ℂ} (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (c : Fin d → Fin d → Vec d → ℂ) (hc : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (c k j))
    {τ : Fin d → Vec d → ℂ} (hτ : ∀ k, FSC (τ k)) :
    ∫ x, ∑ k, ∑ j, c k j x * Fv j x * τ k x =
      ∑ k, ∑ j, ∫ x, Fv j x * (c k j x * τ k x) := by
  have iF : ∀ k j, Integrable (fun x => Fv j x * (c k j x * τ k x)) := fun k j =>
    fluxId_intT (hFv j) (FSC.mul_left (hc k j) (hτ k)).1.continuous
      (FSC.mul_left (hc k j) (hτ k)).2
  have e : (fun x => ∑ k, ∑ j, c k j x * Fv j x * τ k x) =
      fun x => ∑ k, ∑ j, Fv j x * (c k j x * τ k x) := by
    funext x
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ => iF k j)]
  exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun j _ => iF k j

/-- The scalar-potential step: the weak divergence of `a F` against `φ ψ`. -/
theorem fluxId_cA {Fv : Fin d → Vec d → ℂ} (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (acx : Fin d → Fin d → Vec d → ℂ) (hacx : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (acx k j))
    (φc : Vec d → ℂ) (hφc : ContDiff ℝ (⊤ : ℕ∞) φc)
    (D : Vec d → ℂ) (hD : LocallyIntegrable D volume)
    (hDc : ∀ θ : Vec d → ℂ, FSC θ → ∫ x, D x * θ x =
      -∫ x, ∑ k, (∑ j, acx k j x * Fv j x) * fderiv ℝ θ x (unitVector k))
    {ψ : Vec d → ℂ} (hψ : FSC ψ) :
    (∫ x, φc x * D x * ψ x) +
        (∫ x, φc x * ∑ k, (∑ j, acx k j x * Fv j x) * fderiv ℝ ψ x (unitVector k)) =
      -∑ k, ∑ j, ∫ x, Fv j x * (acx k j x * (fderiv ℝ φc x (unitVector k) * ψ x)) := by
  have iT : ∀ j (θ : Vec d → ℂ), FSC θ → Integrable (fun x => Fv j x * θ x) :=
    fun j θ hθ => fluxId_intT (hFv j) hθ.1.continuous hθ.2
  have hΘ : FSC (fun x => φc x * ψ x) := FSC.mul_left hφc hψ
  have hdφ : ∀ k, FSC (fun x => fderiv ℝ φc x (unitVector k) * ψ x) := fun k =>
    FSC.mul_left (fluxId_smooth_fderiv hφc _) hψ
  have hdψ : ∀ k, FSC (fun x => φc x * fderiv ℝ ψ x (unitVector k)) := fun k =>
    FSC.mul_left hφc (hψ.deriv _)
  have hk : ∀ k j, ∫ x, Fv j x * (acx k j x *
        fderiv ℝ (fun y => φc y * ψ y) x (unitVector k)) =
      (∫ x, Fv j x * (acx k j x * (fderiv ℝ φc x (unitVector k) * ψ x))) +
        ∫ x, Fv j x * (acx k j x * (φc x * fderiv ℝ ψ x (unitVector k))) := by
    intro k j
    rw [← integral_add (iT j _ (FSC.mul_left (hacx k j) (hdφ k)))
      (iT j _ (FSC.mul_left (hacx k j) (hdψ k)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    first | (simp only []; rw [fluxId_fderiv_mul (hφc.differentiable (by simp) x)
        (hψ.1.differentiable (by simp) x)]; ring) |
      (rw [fluxId_fderiv_mul (hφc.differentiable (by simp) x)
        (hψ.1.differentiable (by simp) x)]; ring)
  have h1 : ∫ x, φc x * D x * ψ x =
      -(∑ k, ∑ j, ∫ x, Fv j x * (acx k j x * (fderiv ℝ φc x (unitVector k) * ψ x))) -
        ∑ k, ∑ j, ∫ x, Fv j x * (acx k j x * (φc x * fderiv ℝ ψ x (unitVector k))) := by
    have e0 : ∫ x, φc x * D x * ψ x = ∫ x, D x * (φc x * ψ x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        first | (simp only []; ring) | ring)
    rw [e0, hDc _ hΘ, fluxId_RD_split hFv acx hacx hΘ]
    have e1 : (∑ k, ∑ j, ∫ x, Fv j x * (acx k j x *
          fderiv ℝ (fun y => φc y * ψ y) x (unitVector k))) =
        ∑ k, ∑ j, ((∫ x, Fv j x * (acx k j x * (fderiv ℝ φc x (unitVector k) * ψ x))) +
          ∫ x, Fv j x * (acx k j x * (φc x * fderiv ℝ ψ x (unitVector k)))) :=
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hk k j
    rw [e1]
    simp only [Finset.sum_add_distrib]
    ring
  have h3 : ∫ x, φc x * ∑ k, (∑ j, acx k j x * Fv j x) * fderiv ℝ ψ x (unitVector k) =
      ∑ k, ∑ j, ∫ x, Fv j x * (acx k j x * (φc x * fderiv ℝ ψ x (unitVector k))) := by
    have e : (fun x => φc x * ∑ k, (∑ j, acx k j x * Fv j x) * fderiv ℝ ψ x (unitVector k)) =
        fun x => ∑ k, (∑ j, acx k j x * Fv j x) * (φc x * fderiv ℝ ψ x (unitVector k)) := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact fluxId_split_gen hFv acx hacx (τ := fun k x => φc x * fderiv ℝ ψ x (unitVector k)) hdψ
  rw [h1, h3]
  ring

theorem fluxId_alg4 (ε : ℂ) (e0 : Fin d) (a b : Fin d → Fin d → ℂ)
    (h0 : ∑ j, ∑ k, a j k = 0) :
    ∑ j, ∑ k, -(a j k + (ε * (unitVector e0 j : ℂ)) * b j k) = -(ε * ∑ k, b e0 k) := by
  have h1 : ∀ j, ∑ k, -(a j k + (ε * (unitVector e0 j : ℂ)) * b j k) =
      -(∑ k, a j k) - (ε * (unitVector e0 j : ℂ)) * ∑ k, b j k := by
    intro j
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hdelta : ∑ j, (ε * (unitVector e0 j : ℂ)) * ∑ k, b j k = ε * ∑ k, b e0 k := by
    rw [Finset.sum_eq_single e0]
    · simp [unitVector]
    · intro j _ hj
      simp [unitVector, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ e0) h
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    h0, hdelta]
  ring

/-- The flux-potential step: the antisymmetric cancellation. -/
theorem fluxId_cB {u : Vec d → ℂ} {g Fv : Fin d → Vec d → ℂ} {ε : ℂ} {e0 : Fin d}
    (hu : LocallyIntegrable u volume) (hg : ∀ m, LocallyIntegrable (g m) volume)
    (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (hFvdef : ∀ j x, Fv j x = g j x - ε * (unitVector e0 j : ℂ) * u x)
    (hGc : ∀ m (θ : Vec d → ℂ), FSC θ →
      ∫ x, g m x * θ x = -∫ x, u x * fderiv ℝ θ x (unitVector m))
    (Sc : Fin d → Fin d → Vec d → ℂ) (hSc : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (Sc k j))
    (hanti : ∀ k j x, Sc k j x = -Sc j k x)
    {ψ : Vec d → ℂ} (hψ : FSC ψ) :
    -(∫ x, ∑ k, ∑ j, Sc k j x * Fv j x * fderiv ℝ ψ x (unitVector k)) +
        ε * ∫ x, (∑ k, Sc k e0 x * g k x) * ψ x =
      ∑ j, ∫ x, Fv j x * ((∑ k, fderiv ℝ (Sc k j) x (unitVector k)) * ψ x) := by
  have iT : ∀ j (θ : Vec d → ℂ), FSC θ → Integrable (fun x => Fv j x * θ x) :=
    fun j θ hθ => fluxId_intT (hFv j) hθ.1.continuous hθ.2
  have iU : ∀ (θ : Vec d → ℂ), FSC θ → Integrable (fun x => u x * θ x) :=
    fun θ hθ => fluxId_intT hu hθ.1.continuous hθ.2
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Fin d → Fin d → Vec d → ℂ, ∀ k j x, Ψ k j x = Sc k j x * ψ x :=
    ⟨fun k j x => Sc k j x * ψ x, fun _ _ _ => rfl⟩
  have hΨfun : ∀ k j, Ψ k j = fun x => Sc k j x * ψ x := fun k j => funext (hΨdef k j)
  have hΨ : ∀ k j, FSC (Ψ k j) := fun k j => by
    rw [hΨfun]
    exact FSC.mul_left (hSc k j) hψ
  have hΨanti : ∀ k j y, Ψ k j y = -Ψ j k y := fun k j y => by
    rw [hΨdef, hΨdef, hanti k j y]
    ring
  have hτ : ∀ k, FSC (fun x => fderiv ℝ ψ x (unitVector k)) := fun k => hψ.deriv _
  -- the pairings of the potential-gradient terms
  have hX4 : ∫ x, ∑ k, ∑ j, Sc k j x * Fv j x * fderiv ℝ ψ x (unitVector k) =
      ∑ k, ∑ j, ∫ x, Fv j x * (Sc k j x * fderiv ℝ ψ x (unitVector k)) :=
    fluxId_split2 hFv Sc hSc hτ
  have hX5 : ∫ x, (∑ k, Sc k e0 x * g k x) * ψ x =
      ∑ k, ∫ x, g k x * (Sc k e0 x * ψ x) := by
    have e : (fun x => (∑ k, Sc k e0 x * g k x) * ψ x) =
        fun x => ∑ k, g k x * (Sc k e0 x * ψ x) := by
      funext x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    exact integral_finsetSum _ fun k _ =>
      fluxId_intT (hg k) (FSC.mul_left (hSc k e0) hψ).1.continuous (FSC.mul_left (hSc k e0) hψ).2
  have hW : ∀ j, ∫ x, Fv j x * ((∑ k, fderiv ℝ (Sc k j) x (unitVector k)) * ψ x) =
      ∑ k, ∫ x, Fv j x * (fderiv ℝ (Sc k j) x (unitVector k) * ψ x) := by
    intro j
    have e : (fun x => Fv j x * ((∑ k, fderiv ℝ (Sc k j) x (unitVector k)) * ψ x)) =
        fun x => ∑ k, Fv j x * (fderiv ℝ (Sc k j) x (unitVector k) * ψ x) := by
      funext x
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [e]
    exact integral_finsetSum _ fun k _ =>
      iT j _ (FSC.mul_left (fluxId_smooth_fderiv (hSc k j) _) hψ)
  -- product rule
  have hk : ∀ k j, ∫ x, Fv j x * (fderiv ℝ (Sc k j) x (unitVector k) * ψ x) =
      (∫ x, Fv j x * fderiv ℝ (Ψ k j) x (unitVector k)) -
        ∫ x, Fv j x * (Sc k j x * fderiv ℝ ψ x (unitVector k)) := by
    intro k j
    have i1 := iT j _ (FSC.mul_left (fluxId_smooth_fderiv (hSc k j) (unitVector k)) hψ)
    have i2 := iT j _ (FSC.mul_left (hSc k j) (hτ k))
    have i3 := iT j _ ((hΨ k j).deriv (unitVector k))
    rw [← integral_sub i3 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hΨfun]
    first | (simp only []; rw [fluxId_fderiv_mul (hSc k j |>.differentiable (by simp) x)
        (hψ.1.differentiable (by simp) x)]; ring) |
      (rw [fluxId_fderiv_mul (hSc k j |>.differentiable (by simp) x)
        (hψ.1.differentiable (by simp) x)]; ring)
  -- gradient relation applied to the potential derivatives
  have hRG : ∀ k j, ∫ x, Fv j x * fderiv ℝ (Ψ k j) x (unitVector k) =
      -((∫ x, u x * fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j)) +
        (ε * (unitVector e0 j : ℂ)) * ∫ x, u x * fderiv ℝ (Ψ k j) x (unitVector k)) := by
    intro k j
    have hθ := (hΨ k j).deriv (unitVector k)
    rw [fluxId_RG hu hg hFvdef hGc j hθ]
    have i2 := iU _ hθ
    have i3 := iU _ (hθ.deriv (unitVector j))
    rw [neg_inj, ← integral_const_mul, ← integral_add i3 (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    first | (simp only []; ring) | ring
  -- the double sum of second derivatives vanishes
  have hA0 : ∑ j, ∑ k, ∫ x, u x *
      fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j) = 0 := by
    have iA : ∀ k j, Integrable (fun x => u x *
        fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j)) := fun k j =>
      iU _ (((hΨ k j).deriv (unitVector k)).deriv (unitVector j))
    have hz : ∀ x, ∑ j, ∑ k,
        fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j) = 0 :=
      fun x => fluxId_sum_zero Ψ (fun k j => (hΨ k j).1) hΨanti x
    have e : ∑ j, ∑ k, ∫ x, u x *
        fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j) =
        ∫ x, ∑ j, ∑ k, u x *
          fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j) := by
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => iA k j)]
      exact Finset.sum_congr rfl fun j _ => (integral_finsetSum _ fun k _ => iA k j).symm
    rw [e]
    have e0 : (fun x => ∑ j, ∑ k, u x *
        fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j)) =
        fun _ => (0 : ℂ) := by
      funext x
      simp only [← Finset.mul_sum, hz x, mul_zero]
    rw [e0]
    simp
  have hb : ∀ k, ∫ x, g k x * (Sc k e0 x * ψ x) =
      -∫ x, u x * fderiv ℝ (Ψ k e0) x (unitVector k) := fun k => by
    have := hGc k (Ψ k e0) (hΨ k e0)
    simpa only [hΨdef] using this
  have hZ : (∑ j, ∑ k, ∫ x, Fv j x * fderiv ℝ (Ψ k j) x (unitVector k)) =
      -(ε * ∑ k, ∫ x, u x * fderiv ℝ (Ψ k e0) x (unitVector k)) := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hRG k j]
    exact fluxId_alg4 ε e0
      (fun j k => ∫ x, u x *
        fderiv ℝ (fun y => fderiv ℝ (Ψ k j) y (unitVector k)) x (unitVector j))
      (fun j k => ∫ x, u x * fderiv ℝ (Ψ k j) x (unitVector k)) hA0
  have hc : (∑ j, ∑ k, ∫ x, Fv j x * (Sc k j x * fderiv ℝ ψ x (unitVector k))) =
      ∑ k, ∑ j, ∫ x, Fv j x * (Sc k j x * fderiv ℝ ψ x (unitVector k)) := Finset.sum_comm
  have hR : ∑ j, ∫ x, Fv j x * ((∑ k, fderiv ℝ (Sc k j) x (unitVector k)) * ψ x) =
      (∑ j, ∑ k, ∫ x, Fv j x * fderiv ℝ (Ψ k j) x (unitVector k)) -
        ∑ k, ∑ j, ∫ x, Fv j x * (Sc k j x * fderiv ℝ ψ x (unitVector k)) := by
    rw [Finset.sum_congr rfl fun j _ => hW j,
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hk k j]
    simp only [Finset.sum_sub_distrib]
    rw [hc]
  rw [hR, hZ, hX4, hX5, Finset.sum_congr rfl fun k _ => hb k, Finset.sum_neg_distrib]
  ring

end EinsteinFull
