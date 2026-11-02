import EinsteinFull.Calculus.PhysicalGaugeUnitarySupport
import EinsteinFull.Calculus.PhysicalDomainSupport
import EinsteinRelation.Correctors.SpatialWeakProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The exponential gauge on the full physical H1 domains.

The real smooth-weight product rule is reused from the pinned blueprint
`Correctors/SpatialWeakProduct.lean` (7748a8e9000034825873768d309be8915ae53b07).
Both complex components and the actual L2 representatives are transported.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem coordinateDerivative_gaugeWeight {d : ℕ} (i j : Fin d) (lam : ℝ)
    (x : Vec d) :
    coordinateDerivative j (fun y : Vec d => Real.exp (lam * y i)) x =
      Real.exp (lam * x i) * lam * unitVector i j := by
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul lam).exp
  simp only [coordinateDerivative, h.fderiv, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ContinuousLinearMap.proj_apply]
  have he : unitVector j i = unitVector i j := by
    simp only [unitVector, Pi.single_apply, eq_comm]
  rw [he]
  ring

private theorem weakPartial_exp_mul {d : ℕ} (i j : Fin d) (lam : ℝ)
    {f g : Vec d → ℝ} (hfg : HasWeakPartialDerivative Set.univ j f g) :
    HasWeakPartialDerivative Set.univ j (fun x => Real.exp (lam * x i) * f x)
      (fun x => Real.exp (lam * x i) * (g x + lam * unitVector i j * f x)) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => Real.exp (lam * x i)) :=
    (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp
  have h := Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j hfg hφ
  convert h using 1
  funext x
  rw [coordinateDerivative_gaugeWeight]
  ring

/-- The genuine complex weak product rule for the physical exponential gauge. -/
theorem physicalGaugeMultiplier_weakPartial {d : ℕ} (i j : Fin d) (lam : ℝ)
    {f g : Vec d → ℂ}
    (hre : HasWeakPartialDerivative Set.univ j (fun x => (f x).re) (fun x => (g x).re))
    (him : HasWeakPartialDerivative Set.univ j (fun x => (f x).im) (fun x => (g x).im)) :
    HasWeakPartialDerivative Set.univ j
      (fun x => (physicalGaugeMultiplier i lam f x).re)
      (fun x => (physicalGaugeMultiplier i lam
        (fun y => g y + (lam : ℂ) * (unitVector i j : ℂ) * f y) x).re) ∧
    HasWeakPartialDerivative Set.univ j
      (fun x => (physicalGaugeMultiplier i lam f x).im)
      (fun x => (physicalGaugeMultiplier i lam
        (fun y => g y + (lam : ℂ) * (unitVector i j : ℂ) * f y) x).im) := by
  constructor
  · simpa only [physicalGaugeMultiplier, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, mul_zero, zero_mul,
      sub_zero, add_zero] using weakPartial_exp_mul i j lam hre
  · simpa only [physicalGaugeMultiplier, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, mul_zero, zero_mul,
      sub_zero, add_zero, zero_add] using weakPartial_exp_mul i j lam him

/-- The gauge transports the full weighted H1 graph and gives its actual gradient. -/
theorem physicalH1Graph_gauge_forward {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (physicalForceMeasure i lam))
    (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
    (hG : IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G) :
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (physicalGaugeUnitary i lam f) H ∧
      ∀ j : Fin d, (H j : Vec d → ℂ) =ᵐ[volume] fun x =>
        (Real.exp (lam * x i) : ℂ) *
          (G j x + (lam : ℂ) * (unitVector i j : ℂ) * f x) := by
  have hmem (j : Fin d) := memLp_physicalGaugeMultiplier i lam
    ((Lp.memLp (G j)).add ((Lp.memLp f).const_mul ((lam : ℂ) * (unitVector i j : ℂ))))
  let H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun j => (hmem j).toLp _
  have hrep (j : Fin d) : (H j : Vec d → ℂ) =ᵐ[volume]
      physicalGaugeMultiplier i lam
        (fun x => G j x + (lam : ℂ) * (unitVector i j : ℂ) * f x) :=
    (hmem j).coeFn_toLp
  refine ⟨H, ?_, hrep⟩
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (physicalGaugeUnitary i lam f) H _ _ (physicalGaugeUnitary_coe i lam f) hrep]
  exact ⟨fun j => (physicalGaugeMultiplier_weakPartial i j lam (hG.1 j) (hG.2 j)).1,
    fun j => (physicalGaugeMultiplier_weakPartial i j lam (hG.1 j) (hG.2 j)).2⟩

/-- The inverse gauge also transports the full H1 graph, retaining the signed derivative. -/
theorem physicalH1Graph_gauge_backward {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) :
    ∃ H : Fin d → Lp ℂ 2 (physicalForceMeasure i lam),
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩)
        ((physicalGaugeUnitary i lam).symm f) H ∧
      ∀ j : Fin d, (H j : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam] fun x =>
        (Real.exp (-lam * x i) : ℂ) *
          (G j x + ((-lam : ℝ) : ℂ) * (unitVector i j : ℂ) * f x) := by
  have hmem (j : Fin d) := memLp_physicalGaugeMultiplier_neg i lam
    ((Lp.memLp (G j)).add ((Lp.memLp f).const_mul (((-lam : ℝ) : ℂ) * (unitVector i j : ℂ))))
  let H : Fin d → Lp ℂ 2 (physicalForceMeasure i lam) := fun j => (hmem j).toLp _
  have hrep (j : Fin d) : (H j : Vec d → ℂ) =ᵐ[physicalForceMeasure i lam]
      physicalGaugeMultiplier i (-lam)
        (fun x => G j x + ((-lam : ℝ) : ℂ) * (unitVector i j : ℂ) * f x) :=
    (hmem j).coeFn_toLp
  refine ⟨H, ?_, hrep⟩
  rw [isPhysicalH1Graph_iff_representatives (physicalForceMeasure i lam)
    (Or.inr ⟨i, lam, rfl⟩) ((physicalGaugeUnitary i lam).symm f) H _ _
    (physicalGaugeUnitary_symm_coe i lam f) hrep]
  exact ⟨fun j => (physicalGaugeMultiplier_weakPartial i j (-lam) (hG.1 j) (hG.2 j)).1,
    fun j => (physicalGaugeMultiplier_weakPartial i j (-lam) (hG.1 j) (hG.2 j)).2⟩

/-- Multiplication by the gauge identifies the actual full physical H1 domains. -/
theorem physicalH1Graph_gauge_iff {d : ℕ} (i : Fin d) (lam : ℝ)
    (f : Lp ℂ 2 (physicalForceMeasure i lam)) :
    (∃ G, IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G) ↔
      ∃ H, IsPhysicalH1Graph volume (Or.inl rfl) (physicalGaugeUnitary i lam f) H := by
  constructor
  · rintro ⟨G, hG⟩
    obtain ⟨H, hH, _⟩ := physicalH1Graph_gauge_forward i lam f G hG
    exact ⟨H, hH⟩
  · rintro ⟨H, hH⟩
    obtain ⟨G, hG, _⟩ := physicalH1Graph_gauge_backward i lam _ H hH
    exact ⟨G, by simpa only [LinearIsometryEquiv.symm_apply_apply] using hG⟩

end EinsteinFull
