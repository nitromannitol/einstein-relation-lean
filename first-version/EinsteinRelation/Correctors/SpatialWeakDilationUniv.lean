import EinsteinRelation.Correctors.SpatialDilationTests
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Spatial dilation with a nonzero weak source

Source: `paper/main.tex:693–702,800–808`. These chain rules retain the
finite-time scalar residual when restoring the physical spatial scale.
Local integrability suffices; no additional spatial energy is assumed.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- A nonzero scalar dilation preserves local integrability.
Source: `paper/main.tex:693–702`. -/
theorem locallyIntegrable_comp_smul_of_ne_zero {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {F : Vec d → E} (hF : LocallyIntegrable F volume) {r : ℝ} (hr : r ≠ 0) :
    LocallyIntegrable (fun x => F (r • x)) volume := by
  let e : Vec d ≃ₜ Vec d := Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit
  have hm : LocallyIntegrable F (Measure.map (fun x : Vec d => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr]
    intro x
    obtain ⟨S,hS,hI⟩ := hF x
    refine ⟨S,hS,?_⟩
    rw [IntegrableOn,Measure.restrict_smul]
    exact hI.smul_measure ENNReal.ofReal_ne_top
  exact (locallyIntegrable_map_homeomorph e).mp hm

/-- The weak gradient chain rule needs only the integrability in the weak
gradient definition. Source: `paper/main.tex:693–702,800–808`. -/
theorem hasWeakGradient_univ_dilation {d : ℕ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u G) (r c : ℝ) (hr : 0 < r) :
    HasWeakGradient Set.univ (fun x => c*u (r • x))
      (fun x => (c*r) • G (r • x)) := by
  intro j
  refine ⟨?_,?_,?_⟩
  · rw [locallyIntegrableOn_univ]
    exact (locallyIntegrable_comp_smul_of_ne_zero (locallyIntegrableOn_univ.mp (hw j).1) hr.ne').smul c
  · rw [locallyIntegrableOn_univ]
    exact (locallyIntegrable_comp_smul_of_ne_zero (locallyIntegrableOn_univ.mp (hw j).2.1)
      hr.ne').smul (c*r)
  intro φ hφ
  obtain ⟨hψ,hchain⟩ := isSpatialTest_inv_dilation φ hφ r hr
  let ψ : Vec d → ℝ := fun x => φ (r⁻¹ • x)
  have hsrc := (hw j).2.2 ψ hψ
  simp only [Measure.restrict_univ] at hsrc ⊢
  have hscaled : (∫ x, u (r • x)*coordinateDerivative j ψ (r • x)) =
      -(∫ x, G (r • x) j*ψ (r • x)) := by
    rw [Measure.integral_comp_smul volume (fun x => u x*coordinateDerivative j ψ x) r,
      Measure.integral_comp_smul volume (fun x => G x j*ψ x) r,hsrc,smul_neg]
  have hψeq (x : Vec d) : ψ (r • x) = φ x := by
    simp only [ψ,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  have hchain' (x : Vec d) (j : Fin d) :
      coordinateDerivative j ψ (r • x) = r⁻¹*coordinateDerivative j φ x := hchain x j
  simp only [hchain',hψeq,mul_left_comm (u _),integral_const_mul] at hscaled
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
  calc
    c*(∫ x, u (r • x)*coordinateDerivative j φ x) =
        (c*r)*(r⁻¹*(∫ x, u (r • x)*coordinateDerivative j φ x)) := by
      rw [← mul_assoc,mul_assoc c r r⁻¹,mul_inv_cancel₀ hr.ne',mul_one]
    _ = -(c*(r*(∫ x, G (r • x) j*φ x))) := by
      rw [hscaled,mul_neg,mul_assoc]

/-- Restoring spatial scale multiplies a nonzero weak divergence by the
same spatial derivative factor. Source: `paper/main.tex:693–702,800–808`. -/
theorem hasWeakDivergence_dilation {d : ℕ} {F : Vec d → Vec d} {f : Vec d → ℝ}
    (hw : HasWeakDivergence Set.univ F f) (r c : ℝ) (hr : 0 < r) :
    HasWeakDivergence Set.univ (fun x => c • F (r • x))
      (fun x => (c*r)*f (r • x)) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    rw [locallyIntegrableOn_univ]
    exact (locallyIntegrable_comp_smul_of_ne_zero (locallyIntegrableOn_univ.mp (hw.1 j)) hr.ne').smul c
  · rw [locallyIntegrableOn_univ]
    exact (locallyIntegrable_comp_smul_of_ne_zero (locallyIntegrableOn_univ.mp hw.2.1) hr.ne').smul (c*r)
  intro φ hφ
  obtain ⟨hψ,hchain⟩ := isSpatialTest_inv_dilation φ hφ r hr
  let ψ : Vec d → ℝ := fun x => φ (r⁻¹ • x)
  have hsrc := hw.2.2 ψ hψ
  simp only [Measure.restrict_univ] at hsrc ⊢
  have hscaled : (∫ x, dot (F (r • x)) (gradient ψ (r • x))) =
      -(∫ x, f (r • x)*ψ (r • x)) := by
    rw [Measure.integral_comp_smul volume (fun x => dot (F x) (gradient ψ x)) r,
      Measure.integral_comp_smul volume (fun x => f x*ψ x) r,hsrc,smul_neg]
  have hψeq (x : Vec d) : ψ (r • x) = φ x := by
    simp only [ψ,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  have hchain' (x : Vec d) (j : Fin d) :
      coordinateDerivative j ψ (r • x) = r⁻¹*coordinateDerivative j φ x := hchain x j
  have hdot (x : Vec d) : dot (F (r • x)) (gradient ψ (r • x)) =
      r⁻¹*dot (F (r • x)) (gradient φ x) := by
    simp only [dot,gradient,hchain',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [hdot,hψeq,integral_const_mul] at hscaled
  have hdotc (x : Vec d) : dot (c • F (r • x)) (gradient φ x) =
      c*dot (F (r • x)) (gradient φ x) := by
    simp only [dot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  simp only [hdotc,mul_assoc,integral_const_mul]
  calc
    c*(∫ x, dot (F (r • x)) (gradient φ x)) =
        (c*r)*(r⁻¹*(∫ x, dot (F (r • x)) (gradient φ x))) := by
      rw [← mul_assoc,mul_assoc c r r⁻¹,mul_inv_cancel₀ hr.ne',mul_one]
    _ = -(c*(r*(∫ x, f (r • x)*φ x))) := by
      rw [hscaled,mul_neg,mul_assoc]

end EinsteinRelation.Correctors
