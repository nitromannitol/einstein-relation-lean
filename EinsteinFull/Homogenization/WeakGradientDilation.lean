import Homogenization.Sobolev.H1.Definitions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Weak gradients under spatial dilation

If `g` is the weak gradient of `f` on `ℝ^d`, then `x ↦ g(cx)` is the weak gradient of
`x ↦ c⁻¹ f(cx)` for every `c > 0`; square integrability on bounded sets is preserved by the
dilation. This is the change of variables used to pass between the unit range of dependence of
Armstrong, Kuusi and Mourrat and the unit sup-distance range of Armstrong, Kuusi and Loher.
-/

open MeasureTheory
open scoped Pointwise

namespace EinsteinFull.Homogenization

open _root_.Homogenization

variable {d : ℕ}

theorem fderiv_comp_smul_apply {χ : Vec d → ℝ} (hχ : Differentiable ℝ χ) (c : ℝ)
    (y v : Vec d) :
    fderiv ℝ (fun z => χ (c • z)) y v = c * fderiv ℝ χ (c • y) v := by
  have hlin : HasFDerivAt (fun z : Vec d => c • z)
      (c • ContinuousLinearMap.id ℝ (Vec d)) y := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) y).const_smul c
  have h : HasFDerivAt (fun z => χ (c • z))
      ((fderiv ℝ χ (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec d))) y :=
    ((hχ (c • y)).hasFDerivAt).comp y hlin
  rw [h.fderiv]
  simp [smul_eq_mul]

/-- Dilation of a whole-space weak gradient. -/
theorem HasWeakGradientOn.univ_dilate {f : Vec d → ℝ} {g : Vec d → Vec d} {c : ℝ}
    (hc : 0 < c) (h : HasWeakGradientOn Set.univ f g) :
    HasWeakGradientOn Set.univ (fun x => c⁻¹ * f (c • x)) (fun x => g (c • x)) := by
  intro i χ hχ hcs _
  have hc0 : c ≠ 0 := hc.ne'
  let χ' : Vec d → ℝ := fun y => χ (c⁻¹ • y)
  have hχ' : ContDiff ℝ (⊤ : ℕ∞) χ' := hχ.comp (contDiff_const_smul _)
  have hcs' : HasCompactSupport χ' := hcs.comp_smul (inv_ne_zero hc0)
  have hdiff : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hmain := h i χ' hχ' hcs' (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hmain ⊢
  have hderiv (y : Vec d) : fderiv ℝ χ' y (basisVec i) =
      c⁻¹ * fderiv ℝ χ (c⁻¹ • y) (basisVec i) := fderiv_comp_smul_apply hdiff c⁻¹ y _
  simp_rw [hderiv] at hmain
  have hL : ∫ x, c⁻¹ * f (c • x) * fderiv ℝ χ x (basisVec i) =
      |((c ^ d)⁻¹)| * ∫ y, f y * (c⁻¹ * fderiv ℝ χ (c⁻¹ • y) (basisVec i)) := by
    have := Measure.integral_comp_smul (volume : Measure (Vec d))
      (fun y => f y * (c⁻¹ * fderiv ℝ χ (c⁻¹ • y) (basisVec i))) c
    rw [Module.finrank_fin_fun, smul_eq_mul] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    ring
  have hR : ∫ x, g (c • x) i * χ x =
      |((c ^ d)⁻¹)| * ∫ y, g y i * χ' y := by
    have := Measure.integral_comp_smul (volume : Measure (Vec d))
      (fun y => g y i * χ' y) c
    rw [Module.finrank_fin_fun, smul_eq_mul] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [χ', smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hL, hR, hmain, mul_neg]

/-- Square integrability on a set is transported by dilation to the shrunken set. -/
theorem MemLp.comp_smul_restrict {E : Type*} [NormedAddCommGroup E] {f : Vec d → E}
    {c : ℝ} (hc : c ≠ 0) {S : Set (Vec d)} (hS : MeasurableSet S) {p : ENNReal}
    (hf : MemLp f p (volume.restrict (c • S))) :
    MemLp (fun x => f (c • x)) p (volume.restrict S) := by
  have hT : Measurable (fun x : Vec d => c • x) := measurable_const_smul c
  have hpre : (fun x : Vec d => c • x) ⁻¹' (c • S) = S := by
    ext x
    simp only [Set.mem_preimage, Set.smul_mem_smul_set_iff₀ hc]
  have hmap : Measure.map (fun x : Vec d => c • x) (volume.restrict S) =
      ENNReal.ofReal |((c ^ d)⁻¹)| • volume.restrict (c • S) := by
    have h1 := Measure.restrict_map (μ := (volume : Measure (Vec d))) hT
      (hS.const_smul_of_ne_zero hc)
    rw [hpre, Measure.map_addHaar_smul volume hc, Module.finrank_fin_fun,
      Measure.restrict_smul] at h1
    exact h1.symm
  have hg : MemLp f p (Measure.map (fun x : Vec d => c • x) (volume.restrict S)) := by
    rw [hmap]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hg.comp_of_map hT.aemeasurable

end EinsteinFull.Homogenization
