import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Smooth flux identity (support for `e:flux-identity`)

Pure analysis for a fixed environment: the exact identity of `paper/main.tex:818–824`
for smooth `F`, smooth `psi` of compact support, smooth scalar and antisymmetric
flux potentials, and the corrector equations holding almost everywhere in space.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ}

theorem fluxId_smooth_fderiv {f : Vec d → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x v) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

theorem fluxId_fderiv_mul {c e : Vec d → ℂ} {x : Vec d} (hc : DifferentiableAt ℝ c x)
    (he : DifferentiableAt ℝ e x) (v : Vec d) :
    fderiv ℝ (fun y => c y * e y) x v = c x * fderiv ℝ e x v + e x * fderiv ℝ c x v := by
  rw [fderiv_fun_mul hc he]
  simp

theorem fluxId_fderiv_sum {ι : Type*} (s : Finset ι) {f : ι → Vec d → ℂ} {x : Vec d}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (v : Vec d) :
    fderiv ℝ (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, fderiv ℝ (f i) x v := by
  rw [fderiv_fun_sum h, ContinuousLinearMap.sum_apply]

/-- Integration by parts for smooth complex functions, one of them compactly supported. -/
theorem fluxId_ibp {f g : Vec d → ℂ} (v : Vec d)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hfd : Continuous (fun x => fderiv ℝ f x v) := (fluxId_smooth_fderiv hf v).continuous
  have hgd : Continuous (fun x => fderiv ℝ g x v) := (fluxId_smooth_fderiv hg v).continuous
  have hgdc : HasCompactSupport (fun x => fderiv ℝ g x v) := hgc.fderiv_apply ℝ v
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (hfd.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left (f := fun x => fderiv ℝ f x v))
  · exact (hf.continuous.mul hgd).integrable_of_hasCompactSupport (hgdc.mul_left (f := f))
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hgc.mul_left (f := f))
  · exact fun x _ => hf.differentiable (by simp) x
  · exact fun x _ => hg.differentiable (by simp) x

/-- Real-valued integration by parts for smooth functions, one compactly supported. -/
theorem fluxId_ibp_real {f g : Vec d → ℝ} (v : Vec d)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hfd : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgdc : HasCompactSupport (fun x => fderiv ℝ g x v) := hgc.fderiv_apply ℝ v
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (hfd.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left (f := fun x => fderiv ℝ f x v))
  · exact (hf.continuous.mul hgd).integrable_of_hasCompactSupport (hgdc.mul_left (f := f))
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left (f := f))
  · exact fun x _ => hf.differentiable (by simp) x
  · exact fun x _ => hg.differentiable (by simp) x

theorem fluxId_integrable_fderiv_mul {g θ : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ) (v : Vec d) :
    Integrable (fun x => fderiv ℝ g x v * θ x) :=
  (((hg.continuous_fderiv (by simp)).clm_apply continuous_const).mul
    hθ.continuous).integrable_of_hasCompactSupport
    (hθc.mul_left (f := fun x => fderiv ℝ g x v))

theorem fluxId_integral_fderiv_apply{Θ : Vec d → ℂ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ)
    (hc : HasCompactSupport Θ) (v : Vec d) : ∫ x, fderiv ℝ Θ x v = 0 := by
  have h := fluxId_ibp (f := fun _ => (1 : ℂ)) (g := Θ) v contDiff_const hΘ hc
  simpa using h

/-- The first algebraic identity: collecting the product-rule terms. -/
theorem fluxId_alg1 (dφ aF daF : Fin d → ℂ) (φ ψ0 : ℂ) (dψ : Fin d → ℂ)
    (S dS : Fin d → Fin d → ℂ) (F : Fin d → ℂ) (dF : Fin d → Fin d → ℂ) :
    φ * (∑ j, daF j) * ψ0 + φ * (∑ k, aF k * dψ k)
        - (∑ k, ∑ j, S k j * F j * dψ k) - (∑ k, ∑ j, S k j * dF k j) * ψ0 =
      (∑ j, (dφ j * (aF j * ψ0) + φ * (daF j * ψ0 + aF j * dψ j)))
        - (∑ k, ∑ j, (dS k j * (F j * ψ0) + S k j * (dF k j * ψ0 + F j * dψ k)))
        - (∑ j, dφ j * (aF j * ψ0)) + ∑ k, ∑ j, dS k j * (F j * ψ0) := by
  have e1 : φ * (∑ j, daF j) * ψ0 = ∑ j, φ * daF j * ψ0 := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have e2 : φ * (∑ k, aF k * dψ k) = ∑ k, φ * aF k * dψ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have e3 : (∑ k, ∑ j, S k j * dF k j) * ψ0 = ∑ k, ∑ j, S k j * dF k j * ψ0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
  have h1 : ∑ j, (dφ j * (aF j * ψ0) + φ * (daF j * ψ0 + aF j * dψ j)) =
      (∑ j, dφ j * (aF j * ψ0)) + (∑ j, φ * daF j * ψ0) + ∑ j, φ * aF j * dψ j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ k, ∑ j, (dS k j * (F j * ψ0) + S k j * (dF k j * ψ0 + F j * dψ k)) =
      (∑ k, ∑ j, dS k j * (F j * ψ0)) + (∑ k, ∑ j, S k j * dF k j * ψ0) +
        ∑ k, ∑ j, S k j * F j * dψ k := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, h1, h2]
  ring

/-- The second algebraic identity: the corrector equations and symmetry reduce the
flux terms to the commutator integrand. -/
theorem fluxId_alg2 (i : Fin d) (a A : Mat d) (hsym : a.transpose = a)
    (hA : A.transpose = A) (G : Fin d → ℝ) (F aFv : Fin d → ℂ) (ψ0 : ℂ)
    (dS : Fin d → Fin d → ℂ)
    (haFv : ∀ j, aFv j = ∑ l, (a j l : ℂ) * F l)
    (hdS : ∀ j, ∑ k, dS k j =
      (((∑ l, a j l * (unitVector i l + G l)) - A j i : ℝ) : ℂ)) :
    (∑ j, ((a i j - A i j : ℝ) : ℂ) * F j) * ψ0 =
      -(∑ j, (G j : ℂ) * (aFv j * ψ0)) + ∑ k, ∑ j, dS k j * (F j * ψ0) := by
  have hs : ∀ j l, a j l = a l j := fun j l => by
    have := congrFun (congrFun hsym l) j
    simpa [Matrix.transpose_apply] using this
  have hAs : ∀ j l, A j l = A l j := fun j l => by
    have := congrFun (congrFun hA l) j
    simpa [Matrix.transpose_apply] using this
  have hreal : ∀ j, ∑ l, a j l * (unitVector i l + G l) = a j i + ∑ l, a j l * G l := by
    intro j
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    simp [unitVector, Pi.single_apply]
  have hdS' : ∀ j, ∑ k, dS k j = (a j i : ℂ) + (∑ l, (a j l : ℂ) * (G l : ℂ)) - (A j i : ℂ) := by
    intro j
    rw [hdS j, hreal j]
    push_cast
    ring
  have e1 : ∑ j, (G j : ℂ) * (aFv j * ψ0) =
      ∑ j, (∑ l, (a j l : ℂ) * (G l : ℂ)) * (F j * ψ0) := by
    simp only [haFv, Finset.mul_sum, Finset.sum_mul]
    refine Eq.trans Finset.sum_comm ?_
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hs y x]
    ring
  have e2 : ∑ k, ∑ j, dS k j * (F j * ψ0) =
      ∑ j, ((a j i : ℂ) + (∑ l, (a j l : ℂ) * (G l : ℂ)) - (A j i : ℂ)) * (F j * ψ0) := by
    refine Eq.trans Finset.sum_comm ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hdS' j]
  rw [e1, e2, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hs j i, hAs j i]
  push_cast
  ring

/-- Exact smooth flux identity with abstract smooth complex potentials. -/
theorem fluxId_abstract (i : Fin d)
    (a : Vec d → Mat d) (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hsym : ∀ x, (a x).transpose = a x) (A : Mat d) (hA : A.transpose = A)
    (φc : Vec d → ℂ) (hφc : ContDiff ℝ (⊤ : ℕ∞) φc)
    (Sc : Fin d → Fin d → Vec d → ℂ) (hSc : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (Sc k j))
    (G : Vec d → Fin d → ℝ)
    (hG : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, fderiv ℝ φc x (unitVector j) = (G x j : ℂ))
    (hSG : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j,
      (∑ k, fderiv ℝ (Sc k j) x (unitVector k)) =
        (((∑ l, a x j l * (unitVector i l + G x l)) - A j i : ℝ) : ℂ))
    (F : Vec d → Fin d → ℂ) (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (aF : Vec d → Fin d → ℂ) (haFdef : ∀ y j, aF y j = ∑ l, (a y j l : ℂ) * F y l)
    (ψ : Vec d → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, (∑ j : Fin d, ((a x i j - A i j : ℝ) : ℂ) * F x j) * ψ x) =
      (∫ x, φc x * (∑ j : Fin d, fderiv ℝ (fun y => aF y j) x (unitVector j)) * ψ x) +
      (∫ x, φc x * (∑ k : Fin d, aF x k * fderiv ℝ ψ x (unitVector k))) -
      (∫ x, ∑ k : Fin d, ∑ j : Fin d, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k)) -
      (∫ x, (∑ k : Fin d, ∑ j : Fin d,
        Sc k j x * fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x) := by
  have hdiff : ∀ {f : Vec d → ℂ}, ContDiff ℝ (⊤ : ℕ∞) f → ∀ x, DifferentiableAt ℝ f x :=
    fun hf x => hf.differentiable (by simp) x
  have hcastR : ∀ {f : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)) :=
    fun hf => Complex.ofRealCLM.contDiff.comp hf
  have haF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun y => aF y j) := by
    intro j
    have : (fun y => aF y j) = fun y => ∑ l, (a y j l : ℂ) * F y l :=
      funext fun y => haFdef y j
    rw [this]
    exact ContDiff.sum fun l _ => (hcastR (ha j l)).mul (hF l)
  have hdivAF : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => ∑ j : Fin d, fderiv ℝ (fun y => aF y j) x (unitVector j)) :=
    ContDiff.sum fun j _ => fluxId_smooth_fderiv (haF j) (unitVector j)
  have intψ : ∀ {h : Vec d → ℂ}, ContDiff ℝ (⊤ : ℕ∞) h → Integrable (fun x => h x * ψ x) := by
    intro h hh
    exact (hh.continuous.mul hψ.continuous).integrable_of_hasCompactSupport
      (hψc.mul_left (f := h))
  have intdψ : ∀ {h : Vec d → ℂ}, ContDiff ℝ (⊤ : ℕ∞) h → ∀ k : Fin d,
      Integrable (fun x => h x * fderiv ℝ ψ x (unitVector k)) := by
    intro h hh k
    exact (hh.continuous.mul (fluxId_smooth_fderiv hψ _).continuous).integrable_of_hasCompactSupport
      ((hψc.fderiv_apply ℝ (unitVector k)).mul_left (f := h))
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Fin d → Vec d → ℂ, ∀ j y, Θ j y = φc y * (aF y j * ψ y) :=
    ⟨fun j y => φc y * (aF y j * ψ y), fun _ _ => rfl⟩
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : Fin d → Vec d → ℂ, ∀ k y, Ξ k y = ∑ j, Sc k j y * (F y j * ψ y) :=
    ⟨fun k y => ∑ j, Sc k j y * (F y j * ψ y), fun _ _ => rfl⟩
  have hΘs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Θ j) := by
    intro j
    have : Θ j = fun y => φc y * (aF y j * ψ y) := funext (hΘ j)
    rw [this]
    exact hφc.mul ((haF j).mul hψ)
  have hΞs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ξ k) := by
    intro k
    have : Ξ k = fun y => ∑ j, Sc k j y * (F y j * ψ y) := funext (hΞ k)
    rw [this]
    exact ContDiff.sum fun j _ => (hSc k j).mul ((hF j).mul hψ)
  have hΘc : ∀ j, HasCompactSupport (Θ j) := by
    intro j
    refine hψc.mono' ?_
    intro y hy
    apply subset_closure
    rw [Function.mem_support] at hy ⊢
    intro hψy
    apply hy
    rw [hΘ]
    simp [hψy]
  have hΞc : ∀ k, HasCompactSupport (Ξ k) := by
    intro k
    refine hψc.mono' ?_
    intro y hy
    apply subset_closure
    rw [Function.mem_support] at hy ⊢
    intro hψy
    apply hy
    rw [hΞ]
    simp [hψy]
  have i1 : ∀ j, Integrable (fun x => fderiv ℝ (Θ j) x (unitVector j)) := fun j =>
    (fluxId_smooth_fderiv (hΘs j) _).continuous.integrable_of_hasCompactSupport
      ((hΘc j).fderiv_apply ℝ _)
  have i2 : ∀ k, Integrable (fun x => fderiv ℝ (Ξ k) x (unitVector k)) := fun k =>
    (fluxId_smooth_fderiv (hΞs k) _).continuous.integrable_of_hasCompactSupport
      ((hΞc k).fderiv_apply ℝ _)
  have iDiv : Integrable (fun x => (∑ j, fderiv ℝ (Θ j) x (unitVector j)) -
      ∑ k, fderiv ℝ (Ξ k) x (unitVector k)) :=
    (integrable_finsetSum _ fun j _ => i1 j).sub (integrable_finsetSum _ fun k _ => i2 k)
  have hDiv : ∫ x, ((∑ j, fderiv ℝ (Θ j) x (unitVector j)) -
      ∑ k, fderiv ℝ (Ξ k) x (unitVector k)) = 0 := by
    rw [integral_sub (integrable_finsetSum _ fun j _ => i1 j)
        (integrable_finsetSum _ fun k _ => i2 k),
      integral_finsetSum _ fun j _ => i1 j, integral_finsetSum _ fun k _ => i2 k,
      Finset.sum_eq_zero (fun j _ => fluxId_integral_fderiv_apply (hΘs j) (hΘc j) _),
      Finset.sum_eq_zero (fun k _ => fluxId_integral_fderiv_apply (hΞs k) (hΞc k) _), sub_zero]
  have hA_ae : ∀ᵐ x ∂(volume : Measure (Vec d)),
      (φc x * (∑ j, fderiv ℝ (fun y => aF y j) x (unitVector j)) * ψ x +
        φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x) =
      (∑ j, ((a x i j - A i j : ℝ) : ℂ) * F x j) * ψ x +
        ((∑ j, fderiv ℝ (Θ j) x (unitVector j)) - ∑ k, fderiv ℝ (Ξ k) x (unitVector k)) := by
    filter_upwards [hG, hSG] with x hGx hSGx
    have f1 : ∀ j, fderiv ℝ (Θ j) x (unitVector j) =
        fderiv ℝ φc x (unitVector j) * (aF x j * ψ x) +
          φc x * (fderiv ℝ (fun y => aF y j) x (unitVector j) * ψ x +
            aF x j * fderiv ℝ ψ x (unitVector j)) := by
      intro j
      have : Θ j = fun y => φc y * (aF y j * ψ y) := funext (hΘ j)
      have dA : DifferentiableAt ℝ (fun y => aF y j * ψ y) x :=
        (hdiff (haF j) x).mul (hdiff hψ x)
      rw [this, fluxId_fderiv_mul (hdiff hφc x) dA,
        fluxId_fderiv_mul (hdiff (haF j) x) (hdiff hψ x)]
      ring
    have f2 : ∀ k, fderiv ℝ (Ξ k) x (unitVector k) =
        ∑ j, (fderiv ℝ (Sc k j) x (unitVector k) * (F x j * ψ x) +
          Sc k j x * (fderiv ℝ (fun y => F y j) x (unitVector k) * ψ x +
            F x j * fderiv ℝ ψ x (unitVector k))) := by
      intro k
      have : Ξ k = fun y => ∑ j, Sc k j y * (F y j * ψ y) := funext (hΞ k)
      have dB : ∀ j, DifferentiableAt ℝ (fun y => F y j * ψ y) x := fun j =>
        (hdiff (hF j) x).mul (hdiff hψ x)
      have dC : ∀ j ∈ (Finset.univ : Finset (Fin d)),
          DifferentiableAt ℝ (fun y => Sc k j y * (F y j * ψ y)) x := fun j _ =>
        (hdiff (hSc k j) x).mul (dB j)
      rw [this, fluxId_fderiv_sum (f := fun j y => Sc k j y * (F y j * ψ y)) _ dC]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fluxId_fderiv_mul (hdiff (hSc k j) x) (dB j),
        fluxId_fderiv_mul (hdiff (hF j) x) (hdiff hψ x)]
      ring
    have hD1 : ∑ j, fderiv ℝ (Θ j) x (unitVector j) =
        ∑ j, (fderiv ℝ φc x (unitVector j) * (aF x j * ψ x) +
          φc x * (fderiv ℝ (fun y => aF y j) x (unitVector j) * ψ x +
            aF x j * fderiv ℝ ψ x (unitVector j))) :=
      Finset.sum_congr rfl fun j _ => f1 j
    have hD2 : ∑ k, fderiv ℝ (Ξ k) x (unitVector k) =
        ∑ k, ∑ j, (fderiv ℝ (Sc k j) x (unitVector k) * (F x j * ψ x) +
          Sc k j x * (fderiv ℝ (fun y => F y j) x (unitVector k) * ψ x +
            F x j * fderiv ℝ ψ x (unitVector k))) :=
      Finset.sum_congr rfl fun k _ => f2 k
    have alg1 := fluxId_alg1 (fun j => fderiv ℝ φc x (unitVector j)) (fun j => aF x j)
      (fun j => fderiv ℝ (fun y => aF y j) x (unitVector j)) (φc x) (ψ x)
      (fun k => fderiv ℝ ψ x (unitVector k)) (fun k j => Sc k j x)
      (fun k j => fderiv ℝ (Sc k j) x (unitVector k)) (fun j => F x j)
      (fun k j => fderiv ℝ (fun y => F y j) x (unitVector k))
    have alg2 := fluxId_alg2 i (a x) A (hsym x) hA (fun j => G x j) (fun j => F x j)
      (fun j => aF x j) (ψ x) (fun k j => fderiv ℝ (Sc k j) x (unitVector k))
      (fun j => haFdef x j) hSGx
    beta_reduce at alg1 alg2
    simp only [hGx] at alg1 hD1
    rw [hD1, hD2]
    linear_combination alg1 - alg2
  have iR1 : Integrable (fun x => φc x * (∑ j, fderiv ℝ (fun y => aF y j) x (unitVector j)) *
      ψ x) := intψ (hφc.mul hdivAF)
  have iR2 : Integrable (fun x => φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k))) := by
    have : (fun x => φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k))) =
        fun x => ∑ k, (φc x * aF x k) * fderiv ℝ ψ x (unitVector k) := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun k _ => intdψ (hφc.mul (haF k)) k
  have iR3 : Integrable (fun x => ∑ k, ∑ j, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k)) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      intdψ ((hSc k j).mul (hF j)) k
  have iR4 : Integrable (fun x => (∑ k, ∑ j,
      Sc k j x * fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x) :=
    intψ (ContDiff.sum fun k _ => ContDiff.sum fun j _ =>
      (hSc k j).mul (fluxId_smooth_fderiv (hF j) _))
  have iL : Integrable (fun x => (∑ j : Fin d, ((a x i j - A i j : ℝ) : ℂ) * F x j) * ψ x) :=
    intψ (ContDiff.sum fun j _ => (hcastR ((ha i j).sub contDiff_const)).mul (hF j))
  have hsplit : (∫ x, (φc x * (∑ j, fderiv ℝ (fun y => aF y j) x (unitVector j)) * ψ x +
        φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x)) =
      (∫ x, φc x * (∑ j : Fin d, fderiv ℝ (fun y => aF y j) x (unitVector j)) * ψ x) +
      (∫ x, φc x * (∑ k : Fin d, aF x k * fderiv ℝ ψ x (unitVector k))) -
      (∫ x, ∑ k : Fin d, ∑ j : Fin d, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k)) -
      (∫ x, (∑ k : Fin d, ∑ j : Fin d,
        Sc k j x * fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x) := by
    have iA : Integrable (fun x => φc x * (∑ j, fderiv ℝ (fun y => aF y j) x (unitVector j)) *
        ψ x + φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k))) := iR1.add iR2
    have iB : Integrable (fun x => φc x * (∑ j, fderiv ℝ (fun y => aF y j) x (unitVector j)) *
        ψ x + φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k))) := iA.sub iR3
    rw [integral_sub iB iR4, integral_sub iA iR3, integral_add iR1 iR2]
  have e2 : (∫ x, (φc x * (∑ j, fderiv ℝ (fun y => aF y j) x (unitVector j)) * ψ x +
        φc x * (∑ k, aF x k * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * F x j * fderiv ℝ ψ x (unitVector k)) -
        (∑ k, ∑ j, Sc k j x * fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x)) =
      ∫ x, (∑ j : Fin d, ((a x i j - A i j : ℝ) : ℂ) * F x j) * ψ x := by
    rw [integral_congr_ae hA_ae, integral_add iL iDiv, hDiv, add_zero]
  exact e2.symm.trans hsplit

theorem fluxId_fderiv_ofReal {f : Vec d → ℝ} {x : Vec d} (hf : DifferentiableAt ℝ f x)
    (v : Vec d) : fderiv ℝ (fun y => (f y : ℂ)) x v = (fderiv ℝ f x v : ℂ) := by
  have h : HasFDerivAt (fun y => (f y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The smooth flux identity with the real potentials and constants of
`e:flux-identity`, in the exact shape of the statement. -/
theorem fluxId_concrete (i : Fin d)
    (a : Vec d → Mat d) (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (hsym : ∀ x, (a x).transpose = a x) (A : Mat d) (hA : A.transpose = A)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (S : Fin d → Fin d → Vec d → ℝ) (hS : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (S k j))
    (G : Vec d → Fin d → ℝ)
    (hG : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, fderiv ℝ φ x (unitVector j) = G x j)
    (hSG : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j,
      (∑ k, fderiv ℝ (fun y => S k j y) x (unitVector k)) =
        (∑ l, a x j l * (unitVector i l + G x l)) - A j i)
    (cφ : ℝ) (cS : Fin d → Fin d → ℝ)
    (F : Vec d → Fin d → ℂ) (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j))
    (ψ : Vec d → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    let aF := fun (x : Vec d) (j : Fin d) => ∑ l : Fin d, (a x j l : ℂ) * F x l
    let divAF := fun x : Vec d => ∑ j : Fin d, fderiv ℝ (fun y => aF y j) x (unitVector j)
    (∫ x, (∑ j : Fin d, ((a x i j - A i j : ℝ) : ℂ) * F x j) * ψ x) =
      (∫ x, ((φ x - cφ : ℝ) : ℂ) * divAF x * ψ x) +
      (∫ x, ((φ x - cφ : ℝ) : ℂ) * (∑ k : Fin d, aF x k * fderiv ℝ ψ x (unitVector k))) -
      (∫ x, ∑ k : Fin d, ∑ j : Fin d,
        ((S k j x - cS k j : ℝ) : ℂ) * F x j * fderiv ℝ ψ x (unitVector k)) -
      (∫ x, (∑ k : Fin d, ∑ j : Fin d, ((S k j x - cS k j : ℝ) : ℂ) *
        fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x) := by
  intro aF divAF
  have hφc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((φ x - cφ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.sub contDiff_const)
  have hSc : ∀ k j, ContDiff ℝ (⊤ : ℕ∞) (fun x => ((S k j x - cS k j : ℝ) : ℂ)) := fun k j =>
    Complex.ofRealCLM.contDiff.comp ((hS k j).sub contDiff_const)
  refine fluxId_abstract i a ha hsym A hA (fun x => ((φ x - cφ : ℝ) : ℂ)) hφc
    (fun k j x => ((S k j x - cS k j : ℝ) : ℂ)) hSc G ?_ ?_ F hF aF (fun _ _ => rfl) ψ hψ hψc
  · filter_upwards [hG] with x hx j
    rw [fluxId_fderiv_ofReal (f := fun y => φ y - cφ)
      ((hφ.differentiable (by simp) x).sub_const cφ), fderiv_sub_const, hx j]
  · filter_upwards [hSG] with x hx j
    have h1 : ∀ k, fderiv ℝ (fun y => ((S k j y - cS k j : ℝ) : ℂ)) x (unitVector k) =
        (fderiv ℝ (fun y => S k j y) x (unitVector k) : ℂ) := fun k => by
      rw [fluxId_fderiv_ofReal (f := fun y => S k j y - cS k j)
        (((hS k j).differentiable (by simp) x).sub_const (cS k j)), fderiv_sub_const]
    simp only [h1]
    rw [← Complex.ofReal_sum, hx j]

end EinsteinFull
