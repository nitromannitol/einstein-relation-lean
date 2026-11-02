import EinsteinFull.Calculus.ComplexLpChainSupport
import EinsteinFull.Calculus.ComplexHorizontalClosedGraphSupport

/-!
# Nonlinear chain rules on the full stationary complex H1 domain

Composition by a real C1 Lipschitz profile commutes with actual stationary
translations. Differentiating these orbits in L2 gives the full strong
horizontal chain rule, including the literal pointwise differential. No weak
domain identification, extra test-domain assumption or literature input is used.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section

namespace EinsteinFull

open EinsteinRelation

/-- Nonlinear Lipschitz composition commutes with actual complex L2 translation. -/
theorem complexTranslation_compLp {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) {F : ℂ → ℂ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (h0 : F 0 = 0) (f : Lp ℂ 2 Q) :
    complexTranslation Q hQ x (hF.compLp h0 f) =
      hF.compLp h0 (complexTranslation Q hQ x f) := by
  apply Lp.ext
  have hc := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
    (hF.coeFn_compLp h0 f)
  filter_upwards [coeFn_complexTranslation Q hQ x (hF.compLp h0 f),
    hF.coeFn_compLp h0 (complexTranslation Q hQ x f),
    coeFn_complexTranslation Q hQ x f, hc] with a ha hb hd he
  change (hF.compLp h0 f) (translate x a) = F (f (translate x a)) at he
  simp only [Function.comp_apply] at hb
  rw [ha, he, hb, hd]

/-- A real C1 Lipschitz profile preserves the actual strong horizontal derivative domain. -/
theorem HasComplexHorizontalDerivative.compLp {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f g)
    {F : ℂ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z) :
    HasComplexHorizontalDerivative Q hQ i (hF.compLp h0 f)
      ((memLp_complexDifferential Q hD (fun z => (hFD z).le_of_lipschitz hF) f g).toLp
        (fun a => D (f a) (g a))) := by
  have ho := hf.hasDerivAt_orbit 0
  simp only [zero_smul, complexTranslation_zero] at ho
  have hc := hasDerivAt_complexLp_comp Q hF h0 hD hFD ho
  simp only [zero_smul, complexTranslation_zero] at hc
  rw [hasDerivAt_iff_tendsto_slope_zero] at hc
  unfold HasComplexHorizontalDerivative
  simp only [← Complex.ofReal_inv, Complex.coe_smul]
  simp only [zero_add, zero_smul, complexTranslation_zero, ← complexTranslation_compLp] at hc
  exact hc

/-- The nonlinear chain rule holds simultaneously on the full actual horizontal H1 domain. -/
theorem HasComplexHorizontalGradient.compLp {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hf : HasComplexHorizontalGradient Q hQ f G)
    {F : ℂ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z) :
    HasComplexHorizontalGradient Q hQ (hF.compLp h0 f)
      (fun i => (memLp_complexDifferential Q hD
        (fun z => (hFD z).le_of_lipschitz hF) f (G i)).toLp
          (fun a => D (f a) (G i a))) :=
  fun i => (hf i).compLp hF h0 hD hFD

end EinsteinFull
