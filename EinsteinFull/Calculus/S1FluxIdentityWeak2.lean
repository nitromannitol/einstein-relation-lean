import EinsteinFull.Calculus.S1FluxIdentityWeak

/-!
# Weak flux identity: test-pairing steps (support for `e:flux-identity`)
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

/-- Smooth compactly supported complex test function. -/
def FSC (θ : Vec d → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ

theorem FSC.add {θ₁ θ₂ : Vec d → ℂ} (h₁ : FSC θ₁) (h₂ : FSC θ₂) :
    FSC (fun x => θ₁ x + θ₂ x) :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

theorem FSC.mul_left {g θ : Vec d → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h : FSC θ) :
    FSC (fun x => g x * θ x) :=
  ⟨hg.mul h.1, h.2.mul_left (f := g)⟩

theorem FSC.deriv {θ : Vec d → ℂ} (h : FSC θ) (v : Vec d) :
    FSC (fun x => fderiv ℝ θ x v) :=
  ⟨fluxId_smooth_fderiv h.1 v, h.2.fderiv_apply ℝ v⟩

theorem FSC.sum {ι : Type*} (s : Finset ι) {θ : ι → Vec d → ℂ} (h : ∀ i ∈ s, FSC (θ i)) :
    FSC (fun x => ∑ i ∈ s, θ i x) := by
  refine ⟨ContDiff.sum fun i hi => (h i hi).1, ?_⟩
  have hc := Finset.sum_induction (fun i => θ i) (fun f : Vec d → ℂ => HasCompactSupport f)
    (fun a b ha hb => ha.add hb) HasCompactSupport.zero (fun i hi => (h i hi).2)
  have e : (fun x => ∑ i ∈ s, θ i x) = ∑ i ∈ s, θ i := by
    funext x
    simp [Finset.sum_apply]
  rw [e]
  exact hc

theorem fluxId_alg3 (i j : Fin d) (a A : Mat d) (hsym : a.transpose = a)
    (hA : A.transpose = A) (G : Fin d → ℝ) :
    (∑ l, a j l * (unitVector i l + G l)) - A j i - ∑ k, a k j * G k = a i j - A i j := by
  have hs : ∀ j l, a j l = a l j := fun j l => by
    have := congrFun (congrFun hsym l) j
    simpa [Matrix.transpose_apply] using this
  have hAs : ∀ j l, A j l = A l j := fun j l => by
    have := congrFun (congrFun hA l) j
    simpa [Matrix.transpose_apply] using this
  have hreal : ∑ l, a j l * (unitVector i l + G l) = a j i + ∑ l, a j l * G l := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    simp [unitVector, Pi.single_apply]
  have h2 : ∑ k, a k j * G k = ∑ l, a j l * G l :=
    Finset.sum_congr rfl fun k _ => by rw [hs k j]
  rw [hreal, h2, hs j i, hAs j i]
  ring

/-- The gradient relation for `g` transfers to the pairing with `Fv`. -/
theorem fluxId_RG {u : Vec d → ℂ} {g Fv : Fin d → Vec d → ℂ} {ε : ℂ} {e0 : Fin d}
    (hu : LocallyIntegrable u volume) (hg : ∀ m, LocallyIntegrable (g m) volume)
    (hFvdef : ∀ j x, Fv j x = g j x - ε * (unitVector e0 j : ℂ) * u x)
    (hGc : ∀ m (θ : Vec d → ℂ), FSC θ →
      ∫ x, g m x * θ x = -∫ x, u x * fderiv ℝ θ x (unitVector m))
    (j : Fin d) {θ : Vec d → ℂ} (hθ : FSC θ) :
    ∫ x, Fv j x * θ x =
      -∫ x, u x * (fderiv ℝ θ x (unitVector j) + ε * (unitVector e0 j : ℂ) * θ x) := by
  have i1 := fluxId_intT (hg j) hθ.1.continuous hθ.2
  have i2 := fluxId_intT hu hθ.1.continuous hθ.2
  have i3 := fluxId_intT hu (hθ.deriv (unitVector j)).1.continuous (hθ.deriv (unitVector j)).2
  have hI : ∫ x, u x * (fderiv ℝ θ x (unitVector j) + ε * (unitVector e0 j : ℂ) * θ x) =
      (∫ x, u x * fderiv ℝ θ x (unitVector j)) +
        (ε * (unitVector e0 j : ℂ)) * ∫ x, u x * θ x := by
    rw [← integral_const_mul, ← integral_add i3 (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    first | (simp only []; ring) | ring
  have hL : ∫ x, Fv j x * θ x =
      (∫ x, g j x * θ x) - (ε * (unitVector e0 j : ℂ)) * ∫ x, u x * θ x := by
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    first | (simp only []; rw [hFvdef]; ring) | (rw [hFvdef]; ring)
  rw [hL, hI, hGc j θ hθ]
  ring

theorem fluxId_RD_split {Fv : Fin d → Vec d → ℂ} (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (acx : Fin d → Fin d → Vec d → ℂ) (hacx : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (acx k j))
    {θ : Vec d → ℂ} (hθ : FSC θ) :
    ∫ x, ∑ k, (∑ j, acx k j x * Fv j x) * fderiv ℝ θ x (unitVector k) =
      ∑ k, ∑ j, ∫ x, Fv j x * (acx k j x * fderiv ℝ θ x (unitVector k)) := by
  have iF : ∀ k j, Integrable (fun x => Fv j x * (acx k j x * fderiv ℝ θ x (unitVector k))) :=
    fun k j =>
      fluxId_intT (hFv j) (FSC.mul_left (hacx k j) (hθ.deriv _)).1.continuous
        (FSC.mul_left (hacx k j) (hθ.deriv _)).2
  have e : (fun x => ∑ k, (∑ j, acx k j x * Fv j x) * fderiv ℝ θ x (unitVector k)) =
      fun x => ∑ k, ∑ j, Fv j x * (acx k j x * fderiv ℝ θ x (unitVector k)) := by
    funext x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun j _ => iF k j)]
  exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun j _ => iF k j

/-- The commutator pairing reduces to the corrector flux and the potential divergence. -/
theorem fluxId_cC (i : Fin d) (a : Vec d → Mat d)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hsym : ∀ x, (a x).transpose = a x) (A : Mat d) (hA : A.transpose = A)
    (G : Vec d → Fin d → ℝ)
    (Fv : Fin d → Vec d → ℂ) (hFv : ∀ j, LocallyIntegrable (Fv j) volume)
    (w : Fin d → Vec d → ℂ) (hws : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (w j))
    (hw : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, w j x =
      (((∑ l, a x j l * (unitVector i l + G x l)) - A j i : ℝ) : ℂ))
    (dφ : Fin d → Vec d → ℂ) (hdφs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (dφ k))
    (hdφ : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ k, dφ k x = (G x k : ℂ))
    {ψ : Vec d → ℂ} (hψ : FSC ψ) :
    ∫ x, (∑ j, ((a x i j - A i j : ℝ) : ℂ) * Fv j x) * ψ x =
      (∑ j, ∫ x, Fv j x * (w j x * ψ x)) -
        ∑ k, ∑ j, ∫ x, Fv j x * ((a x k j : ℂ) * (dφ k x * ψ x)) := by
  have hcast : ∀ {f : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)) := fun hf => Complex.ofRealCLM.contDiff.comp hf
  have hac : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => (a x k j : ℂ)) := fun k j => hcast (ha k j)
  have iT : ∀ j (θ : Vec d → ℂ), FSC θ → Integrable (fun x => Fv j x * θ x) :=
    fun j θ hθ => fluxId_intT (hFv j) hθ.1.continuous hθ.2
  have hθ1 : ∀ j, FSC (fun x => ((a x i j - A i j : ℝ) : ℂ) * ψ x) := fun j =>
    FSC.mul_left (hcast ((ha i j).sub contDiff_const)) hψ
  have e1 : ∫ x, (∑ j, ((a x i j - A i j : ℝ) : ℂ) * Fv j x) * ψ x =
      ∑ j, ∫ x, Fv j x * (((a x i j - A i j : ℝ) : ℂ) * ψ x) := by
    have : (fun x => (∑ j, ((a x i j - A i j : ℝ) : ℂ) * Fv j x) * ψ x) =
        fun x => ∑ j, Fv j x * (((a x i j - A i j : ℝ) : ℂ) * ψ x) := by
      funext x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact integral_finsetSum _ fun j _ => iT j _ (hθ1 j)
  have hFSC_w : ∀ j, FSC (fun x => w j x * ψ x) := fun j => FSC.mul_left (hws j) hψ
  have hFSC_d : ∀ k j, FSC (fun x => (a x k j : ℂ) * (dφ k x * ψ x)) := fun k j =>
    FSC.mul_left (hac k j) (FSC.mul_left (hdφs k) hψ)
  have e2 : (∑ k, ∑ j, ∫ x, Fv j x * ((a x k j : ℂ) * (dφ k x * ψ x))) =
      ∑ j, ∫ x, Fv j x * (∑ k, (a x k j : ℂ) * (dφ k x * ψ x)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_finsetSum _ (fun k _ => iT j _ (hFSC_d k j))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (Finset.mul_sum _ _ _).symm)
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (iT j _ (hFSC_w j)) (iT j _ (FSC.sum _ fun k _ => hFSC_d k j))]
  refine integral_congr_ae ?_
  filter_upwards [hw, hdφ] with x hwx hdx
  have h3 := fluxId_alg3 i j (a x) A (hsym x) hA (G x)
  have hc : (((∑ l, a x j l * (unitVector i l + G x l)) - A j i : ℝ) : ℂ) -
      ((∑ k, a x k j * G x k : ℝ) : ℂ) = ((a x i j - A i j : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub]
    exact congrArg _ h3
  have hY : ((∑ k, a x k j * G x k : ℝ) : ℂ) = ∑ k, (a x k j : ℂ) * (G x k : ℂ) := by
    push_cast
    rfl
  have hS : ∑ k, (a x k j : ℂ) * ((G x k : ℂ) * ψ x) =
      (∑ k, (a x k j : ℂ) * (G x k : ℂ)) * ψ x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [hwx j, hdx, hS]
  linear_combination (-(Fv j x * ψ x)) * hc + (-(Fv j x * ψ x)) * hY

end EinsteinFull
