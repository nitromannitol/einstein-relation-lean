import EinsteinFull.Calculus.S1FluxIdentityWeak2

/-!
# Weak divergence of `a F` from the centered equation (support for `e:flux-identity`)

For a real smooth compact test: the centered-equation identity, the gradient relation and the
flux relation `J = (a - A) F` give the weak divergence of `a F`.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

theorem fluxId_smooth_fderiv_real {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x v) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

theorem fluxId_FSC_ofReal {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : FSC (fun x => (φ x : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp hφ, hφc.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)⟩

theorem fluxId_FSC_ofReal_deriv {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (v : Vec d) : FSC (fun x => (fderiv ℝ φ x v : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp (fluxId_smooth_fderiv_real hφ v),
    (hφc.fderiv_apply ℝ v).comp_left (g := ((↑) : ℝ → ℂ)) (by simp)⟩

theorem fluxId_alg5 (α β γ δ : Fin d → ℂ) (ε u B0 : ℂ) (hδ : ∑ j, β j * δ j = B0) :
    ∑ j, α j * (γ j - ε * δ j * u) =
      ∑ j, β j * γ j + ∑ j, (α j - β j) * (γ j - ε * δ j * u) - ε * B0 * u := by
  have h : ∀ j, α j * (γ j - ε * δ j * u) =
      (α j - β j) * (γ j - ε * δ j * u) + β j * γ j - ε * u * (β j * δ j) := by
    intro j
    ring
  rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hδ]
  ring

theorem fluxId_alg6 (α β γ δ : Fin d → ℂ) (ε u w B0 Jk : ℂ) (hδ : ∑ j, β j * δ j = B0)
    (hJ : Jk = ∑ j, (α j - β j) * (γ j - ε * δ j * u)) :
    (∑ j, α j * (γ j - ε * δ j * u)) * w =
      ∑ j, β j * (γ j * w) + Jk * w - (ε * B0) * (u * w) := by
  have h5 := fluxId_alg5 α β γ δ ε u B0 hδ
  have hs : (∑ j, β j * γ j) * w = ∑ j, β j * (γ j * w) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h5, ← hJ]
  linear_combination hs

theorem fluxId_int_dsum {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → κ → ℂ)
    (f : ι → κ → Vec d → ℂ) (hf : ∀ j k, Integrable (f j k) volume) :
    ∫ x, ∑ j, ∑ k, c j k * f j k x = ∑ j, ∑ k, c j k * ∫ x, f j k x := by
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => (hf j k).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => (hf j k).const_mul _)]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

/-- The weak divergence of `a F` against a real smooth compact test. -/
theorem fluxId_div_real (a : Vec d → Mat d) (A : Mat d) {u V : Vec d → ℂ}
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
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x, (2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀)) *
        (φ x : ℂ)) =
      -∑ k, ∫ x, (∑ j, (a x k j : ℂ) * Fv j x) * (fderiv ℝ φ x (unitVector k) : ℂ) := by
  have hC := fluxId_FSC_ofReal hφ hφc
  have hD : ∀ k, FSC (fun x => (fderiv ℝ φ x (unitVector k) : ℂ)) :=
    fun k => fluxId_FSC_ofReal_deriv hφ hφc _
  have iT : ∀ {f : Vec d → ℂ}, LocallyIntegrable f volume → ∀ {θ : Vec d → ℂ}, FSC θ →
      Integrable (fun x => f x * θ x) volume :=
    fun {_} hf {_} hθ => fluxId_intT hf hθ.1.continuous hθ.2
  have hδ : ∀ k, ∑ j, (A k j : ℂ) * (unitVector e0 j : ℂ) = (A k e0 : ℂ) := by
    intro k
    rw [Finset.sum_eq_single e0]
    · simp [unitVector]
    · intro j _ hj
      simp [unitVector, Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ e0) h
  -- the pointwise form of `a F`
  have hpt : ∀ k (w : Vec d → ℂ), ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∑ j, (a x k j : ℂ) * Fv j x) * w x =
        ∑ j, (A k j : ℂ) * (g j x * w x) + J k x * w x - (ε * (A k e0 : ℂ)) * (u x * w x) := by
    intro k w
    filter_upwards [hJrel k] with x hx
    have hJ' : J k x = ∑ j, ((a x k j : ℂ) - (A k j : ℂ)) *
        (g j x - ε * (unitVector e0 j : ℂ) * u x) := by
      rw [hx]
      exact Finset.sum_congr rfl fun j _ => by rw [hFvdef j x]; push_cast; ring
    have h6 := fluxId_alg6 (fun j => (a x k j : ℂ)) (fun j => (A k j : ℂ)) (fun j => g j x)
      (fun j => (unitVector e0 j : ℂ)) ε (u x) (w x) (A k e0 : ℂ) (J k x) (hδ k) hJ'
    simp only [hFvdef]
    exact h6
  -- pairing of each flux component
  have hk : ∀ k, ∫ x, (∑ j, (a x k j : ℂ) * Fv j x) * (fderiv ℝ φ x (unitVector k) : ℂ) =
      (∑ j, (A k j : ℂ) * ∫ x, g j x * (fderiv ℝ φ x (unitVector k) : ℂ)) +
        (∫ x, J k x * (fderiv ℝ φ x (unitVector k) : ℂ)) -
        (ε * (A k e0 : ℂ)) * ∫ x, u x * (fderiv ℝ φ x (unitVector k) : ℂ) := by
    intro k
    rw [integral_congr_ae (hpt k (fun x => (fderiv ℝ φ x (unitVector k) : ℂ)))]
    have i1 : ∀ j, Integrable (fun x => g j x * (fderiv ℝ φ x (unitVector k) : ℂ)) volume :=
      fun j => iT (hg j) (hD k)
    have iA : Integrable (fun x => ∑ j, (A k j : ℂ) *
        (g j x * (fderiv ℝ φ x (unitVector k) : ℂ))) volume :=
      integrable_finsetSum _ fun j _ => (i1 j).const_mul (A k j : ℂ)
    have iB : Integrable (fun x => J k x * (fderiv ℝ φ x (unitVector k) : ℂ)) volume :=
      iT (hJ k) (hD k)
    have iC : Integrable (fun x => (ε * (A k e0 : ℂ)) *
        (u x * (fderiv ℝ φ x (unitVector k) : ℂ))) volume :=
      (iT hu (hD k)).const_mul _
    have iAB : Integrable (fun x => ∑ j, (A k j : ℂ) *
        (g j x * (fderiv ℝ φ x (unitVector k) : ℂ)) +
        J k x * (fderiv ℝ φ x (unitVector k) : ℂ)) volume := iA.add iB
    have hsumint : ∫ x, ∑ j, (A k j : ℂ) * (g j x * (fderiv ℝ φ x (unitVector k) : ℂ)) =
        ∑ j, (A k j : ℂ) * ∫ x, g j x * (fderiv ℝ φ x (unitVector k) : ℂ) := by
      rw [integral_finsetSum _ fun j _ => (i1 j).const_mul (A k j : ℂ)]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    rw [integral_sub iAB iC, integral_add iA iB, hsumint, integral_const_mul]
  -- the gradient relation against the cast test
  have hgr : ∀ k, ∫ x, u x * (fderiv ℝ φ x (unitVector k) : ℂ) =
      -∫ x, g k x * (φ x : ℂ) := by
    intro k
    have h := hGc k (fun x => (φ x : ℂ)) hC
    have e : ∀ x, fderiv ℝ (fun y => (φ y : ℂ)) x (unitVector k) =
        (fderiv ℝ φ x (unitVector k) : ℂ) := fun x =>
      fluxId_fderiv_ofReal (hφ.differentiable (by simp) x) _
    simp only [e] at h
    rw [h, neg_neg]
  have hCint : Integrable (fun x => (φ x : ℂ)) volume :=
    hC.1.continuous.integrable_of_hasCompactSupport hC.2
  have cTA : ∫ x, ∑ j, ∑ k, (A j k : ℂ) * g k x * (fderiv ℝ φ x (unitVector j) : ℂ) =
      ∑ j, ∑ k, (A j k : ℂ) * ∫ x, g k x * (fderiv ℝ φ x (unitVector j) : ℂ) := by
    have e : (fun x => ∑ j, ∑ k, (A j k : ℂ) * g k x * (fderiv ℝ φ x (unitVector j) : ℂ)) =
        fun x => ∑ j, ∑ k, (A j k : ℂ) * (g k x * (fderiv ℝ φ x (unitVector j) : ℂ)) := by
      funext x
      simp only [mul_assoc]
    rw [e]
    exact fluxId_int_dsum (fun j k => (A j k : ℂ))
      (fun j k x => g k x * (fderiv ℝ φ x (unitVector j) : ℂ))
      (fun j k => iT (hg k) (hD j))
  have cTg : ∫ x, (∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ) =
      ∑ j, (A j e0 : ℂ) * ∫ x, g j x * (φ x : ℂ) := by
    have e : (fun x => (∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ)) =
        fun x => ∑ j, (A j e0 : ℂ) * (g j x * (φ x : ℂ)) := by
      funext x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (iT (hg j) hC).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have cTJs : ∫ x, ∑ j, J j x * (fderiv ℝ φ x (unitVector j) : ℂ) =
      ∑ j, ∫ x, J j x * (fderiv ℝ φ x (unitVector j) : ℂ) :=
    integral_finsetSum _ fun j _ => iT (hJ j) (hD j)
  have iAg : Integrable (fun x => (∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ)) volume := by
    have e : (fun x => (∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ)) =
        fun x => ∑ j, (A j e0 : ℂ) * (g j x * (φ x : ℂ)) := by
      funext x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact integrable_finsetSum _ fun j _ => (iT (hg j) hC).const_mul _
  have iJ : Integrable (fun x => (J e0 x - c₀) * (φ x : ℂ)) volume :=
    ((iT (hJ e0) hC).sub (hCint.const_mul c₀)).congr
      (Filter.Eventually.of_forall fun x => (sub_mul _ _ _).symm)
  have hLHS : ∫ x, (2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x - 2 * κ * (J e0 x - c₀)) *
        (φ x : ℂ) =
      2 * (∫ x, V x * (φ x : ℂ)) -
        (2 * σ + ε) * (∫ x, (∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ)) -
        (2 * κ) * ∫ x, (J e0 x - c₀) * (φ x : ℂ) := by
    have e : (fun x => (2 * V x - (2 * σ + ε) * ∑ j, (A j e0 : ℂ) * g j x -
          2 * κ * (J e0 x - c₀)) * (φ x : ℂ)) =
        fun x => 2 * (V x * (φ x : ℂ)) -
          (2 * σ + ε) * ((∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ)) -
          (2 * κ) * ((J e0 x - c₀) * (φ x : ℂ)) := by
      funext x
      ring
    have iV2 : Integrable (fun x => 2 * (V x * (φ x : ℂ))) volume := (iT hV hC).const_mul 2
    have iG2 : Integrable (fun x => (2 * σ + ε) *
        ((∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ))) volume := iAg.const_mul _
    have iJ2 : Integrable (fun x => (2 * κ) * ((J e0 x - c₀) * (φ x : ℂ))) volume :=
      iJ.const_mul _
    have iVG : Integrable (fun x => 2 * (V x * (φ x : ℂ)) -
        (2 * σ + ε) * ((∑ j, (A j e0 : ℂ) * g j x) * (φ x : ℂ))) volume := iV2.sub iG2
    rw [e, integral_sub iVG iJ2, integral_sub iV2 iG2, integral_const_mul,
      integral_const_mul, integral_const_mul]
  have hu' : ∑ k, (ε * (A k e0 : ℂ)) * ∫ x, u x * (fderiv ℝ φ x (unitVector k) : ℂ) =
      -(ε * ∑ k, (A k e0 : ℂ) * ∫ x, g k x * (φ x : ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hgr k]; ring
  have hRHS : -∑ k, ∫ x, (∑ j, (a x k j : ℂ) * Fv j x) * (fderiv ℝ φ x (unitVector k) : ℂ) =
      -((∑ k, ∑ j, (A k j : ℂ) * ∫ x, g j x * (fderiv ℝ φ x (unitVector k) : ℂ)) +
        (∑ k, ∫ x, J k x * (fderiv ℝ φ x (unitVector k) : ℂ)) +
        ε * ∑ k, (A k e0 : ℂ) * ∫ x, g k x * (φ x : ℂ)) := by
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, Finset.sum_add_distrib, hu']
    ring
  have he' := he φ hφ hφc
  rw [cTA, cTJs] at he'
  rw [hLHS, hRHS]
  linear_combination 2 * he' - ε * cTg

end EinsteinFull
